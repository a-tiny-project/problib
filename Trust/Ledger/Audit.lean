import Lean.Elab.Command
import Lean.Meta.AppBuilder
import Lean.Meta.Check
import Lean.Meta.SynthInstance
import Trust.Ledger.Command
import Trust.Ledger.Export

/-! The premise ledger audit and its baseline.

`#audit_premise_ledger [Root, …]` reads every claim of the groups whose
registering module lies under one of the roots. A claim with binders owes the
ledger an inhabitant, one necessity witness per premise, and the unbundling of
each bundled binder. The audit re-checks every registered witness and
inhabitant, so a row whose check now refuses is stale. It fills an
unconditional claim's binders with `default` values when it can, which gives
that claim an automatic inhabitant. It then compares what each claim still
owes with the package baseline that `#premise_ledger_baseline` declares. An
owed obligation that the baseline lists is exempt, and any other is open. A
baseline row is stale when it lists an obligation its claim no longer owes,
when its claim owes nothing or is not audited, or when it marks a rename from
a name that is still declared.

The audit prints one line per group and one total line, each followed by at
most `detailLimit` details. Each detail is a failure: an open obligation, a
stale registered row, or a stale baseline row. In report mode every line is
information. Under `set_option trust.ledger.enforce true`, a line with a
detail is an error. -/

namespace Trust.Ledger

open Lean Elab Command Meta

register_option trust.ledger.export : Bool := {
  defValue := false
  descr := "log the audited claims as claim/v2 rows, one JSON object per line"
}

register_option trust.ledger.revision : String := {
  defValue := ""
  descr := "the source revision that exported claim/v2 rows record: 40 \
    lowercase hexadecimal characters"
}

register_option trust.ledger.clean : Bool := {
  defValue := false
  descr := "whether exported claim/v2 rows record clean sources"
}

register_option trust.ledger.emitBaseline : Bool := {
  defValue := false
  descr := "log the baseline command that the audited claims need"
}

/-- A baseline holds at most this many rows. -/
def baselineRowLimit : Nat := 16384

/-- An audit prints at most this many details under each line. -/
def detailLimit : Nat := 64

/-- One baseline row: a claim and the obligations it may still owe. A renamed
claim names its previous name, which must no longer be declared. -/
structure BaselineRow where
  claim : Name
  previous : Option Name
  obligations : Array Obligation
deriving Inhabited, Repr

/-- The row as a baseline spells it. -/
def BaselineRow.render (row : BaselineRow) : String :=
  let renamed :=
    match row.previous with
    | some previous => s!" (was {previous})"
    | none => ""
  let labels := ", ".intercalate (row.obligations.map Obligation.label).toList
  s!"{row.claim}{renamed} : [{labels}]"

/-- The lines of the baseline command that declares `rows`: one row per line,
each ending in a comma. -/
def baselineLines (rows : Array BaselineRow) : Array String :=
  if rows.isEmpty then
    #["#premise_ledger_baseline []"]
  else
    #["#premise_ledger_baseline ["] ++
      rows.map (fun row => s!"  {row.render},") ++ #["]"]

/-- `lines` as one message: each line is a text of its own, and a text that
holds only a line break joins it to the next. Lean's printer copies the rest
of a text at every line break inside it, so one text that held every line
would print in time quadratic in its length. -/
private def linesMessage (lines : Array String) : MessageData :=
  .ofFormat (Format.joinSep lines.toList "\n")

/-- The baseline of the current file. Nothing imports a ledger file, and
fixtures that import one another keep their own baselines, so rows never
leave the file that declares them. -/
initialize baselineExtension : EnvExtension (Option (Array BaselineRow)) ←
  registerEnvExtension (pure none)

/-- One obligation of a baseline row: `inhabitant`, a premise id, or
`bundled` and a binder. A premise named `inhabitant` is written
`«inhabitant»`. -/
syntax premiseObligation :=
  &"inhabitant" <|> atomic(&"bundled" ident) <|> ident

/-- One baseline row: `Claim : [obligation, …]`, or
`New (was Old) : [obligation, …]` for a renamed claim. -/
syntax premiseBaselineRow :=
  ident ("(" &"was" ident ")")? " : " "[" premiseObligation,* "]"

/-- The package baseline: one row per line in byte order of claim names, each
listing the obligations its claim may still owe. -/
syntax (name := premiseLedgerBaselineCommand) "#premise_ledger_baseline "
  "[" sepBy(premiseBaselineRow, ",", ", ", allowTrailingSep) "]" : command

private def obligationOf (entry : Syntax) : Obligation :=
  let inner := entry[0]
  if inner.isIdent then
    .necessity inner.getId.eraseMacroScopes
  else if inner.getNumArgs == 2 then
    .bundled inner[1].getId.eraseMacroScopes
  else
    .inhabitant

private def rowOf (rowSyntax : Syntax) : CommandElabM BaselineRow :=
  match rowSyntax with
  | `(premiseBaselineRow| $claim:ident $[( was $previous?:ident )]?
      : [$entries,*]) =>
      return {
        claim := claim.getId.eraseMacroScopes
        previous := previous?.map (·.getId.eraseMacroScopes)
        obligations := entries.getElems.map fun entry => obligationOf entry.raw
      }
  | _ => throwErrorAt rowSyntax "premise ledger: malformed baseline row"

/-- The lines on which `node` starts and ends. -/
private def lineSpan (node : Syntax) : CommandElabM (Nat × Nat) := do
  let fileMap ← getFileMap
  let start := node.getPos?.getD 0
  let stop := node.getTailPos?.getD start
  return ((fileMap.toPosition start).line, (fileMap.toPosition stop).line)

private def distinctObligations (obligations : Array Obligation) :
    Array Obligation :=
  obligations.foldl (init := #[]) fun kept obligation =>
    if kept.contains obligation then kept else kept.push obligation

@[command_elab premiseLedgerBaselineCommand]
def elabPremiseLedgerBaseline : CommandElab := fun commandSyntax => do
  if (baselineExtension.getState (← getEnv)).isSome then
    refuse m!"premise ledger: refuse baseline: this file already declares one"
    return
  let rowSyntaxes := commandSyntax[2].getSepArgs
  unless rowSyntaxes.size ≤ baselineRowLimit do
    refuse m!"premise ledger: refuse baseline: {rowSyntaxes.size} rows \
      exceed the limit of {baselineRowLimit}"
    return
  let (_, opening) ← lineSpan commandSyntax[1]
  let (closing, _) ← lineSpan commandSyntax[3]
  let mut previousLine := opening
  let mut previousName : Option String := none
  let mut seen : NameSet := {}
  let mut rows := #[]
  for rowSyntax in rowSyntaxes do
    let row ← rowOf rowSyntax
    let (first, last) ← lineSpan rowSyntax
    unless first == last && previousLine < first do
      refuse m!"premise ledger: baseline row {row.claim} must hold a line of \
        its own"
    previousLine := last
    if seen.contains row.claim then
      refuse m!"premise ledger: refuse baseline row {row.claim}: it repeats a \
        row above it"
      continue
    seen := seen.insert row.claim
    let name := row.claim.toString
    if let some previous := previousName then
      unless previous < name do
        refuse m!"premise ledger: baseline row {row.claim} sorts before \
          {previous}, the row above it"
    previousName := some name
    let obligations := distinctObligations row.obligations
    unless obligations.size == row.obligations.size do
      refuse m!"premise ledger: baseline row {row.claim} repeats an \
        obligation"
    rows := rows.push { row with obligations }
  unless rowSyntaxes.isEmpty || previousLine < closing do
    refuse m!"premise ledger: the baseline's closing bracket must hold a \
      line of its own"
  modifyEnv fun environment =>
    baselineExtension.setState environment (some rows)

/-- `text` on one line: each line break, with the indentation after it,
becomes one space. -/
private def oneLine (text : String) : String := Id.run do
  let mut result := ""
  let mut indenting := false
  for character in text.toList do
    if character == '\n' then
      result := result.push ' '
      indenting := true
    else if indenting && character == ' ' then
      pure ()
    else
      indenting := false
      result := result.push character
  return result

/-- The instance an inhabitant names, as `id := argument` pairs on one line,
with every constant named in full. -/
private def instanceText (parameters : Array (Name × Expr)) : MetaM String := do
  let parts ← parameters.mapM fun (id, argument) => do
    let shown ← withOptions (fun options => options.setBool `pp.fullNames true)
      (ppExpr argument)
    return s!"{id} := {oneLine (shown.pretty 100000)}"
  return ", ".intercalate parts.toList

/-- The automatic instance of an unconditional claim. Every binder but a
negated conclusion is filled, at universe level zero, by its type's `default`
unfolded to weak head normal form, or, for an instance binder, by a
synthesized instance. There is none when a binder is a proposition or
synthesizes nothing. -/
private def autoInstance? (info : ConstantInfo) (shape : Shape) :
    MetaM (Option (Array (Name × Expr))) := do
  unless shape.kind == .unconditional do return none
  let levels := info.levelParams.map fun _ => Level.zero
  let mut type := info.instantiateTypeLevelParams levels
  let mut arguments := #[]
  for _ in [0:shape.arity] do
    let .forallE _ domain body binderInfo ← whnfR type | return none
    if ← isProp domain then return none
    let value? ←
      if binderInfo.isInstImplicit then
        synthInstance? domain
      else
        match ← synthInstance? (← mkAppM ``Inhabited #[domain]) with
        | some inhabited =>
            pure (some (← whnfD (← mkAppOptM ``Inhabited.default
              #[some domain, some inhabited])))
        | none => pure none
    let some value := value? | return none
    let value ← instantiateMVars value
    arguments := arguments.push value
    type := body.instantiate1 value
  unless ← isTypeCorrect (mkAppN (.const info.name levels) arguments) do
    return none
  return some <| shape.parameters.map fun (id, position) =>
    (id, arguments[position]!)

/-- The ledger's reading of one registered claim. -/
private structure ClaimAudit where
  claim : Name
  group : Name
  shape : Shape
  /-- The premises the proof never reads, or `none` when the proof is not in
  the environment. -/
  unused : Option (Array Name)
  /-- Premises whose witness passes its re-check, with the witness. -/
  witnesses : Array (Name × Name)
  /-- Inhabitants that pass their re-check, with their instances. An
  instance is closed, so the export can print it later. -/
  inhabitants : Array (Name × Array (Name × Expr))
  /-- The automatic instance, tried only when no registered inhabitant
  passes. -/
  auto : Option (Array (Name × Expr))
  /-- Registered rows whose re-check refuses. -/
  stale : Array MessageData
deriving Inhabited

private def readClaim (group claim : Name) : MetaM ClaimAudit := do
  let info ← getConstInfo claim
  let shape ← shapeOf info.type
  let unused ←
    if shape.premises.isEmpty then pure (some #[]) else unusedPremises info
  let environment ← getEnv
  let mut witnesses := #[]
  let mut stale := #[]
  for row in necessityRows environment claim do
    match ← checkNecessity claim row.premise row.witness with
    | .ok () => witnesses := witnesses.push (row.premise, row.witness)
    | .error reason =>
        stale := stale.push m!"stale necessity {claim} {row.premise} by \
          {row.witness}: {reason}"
  let mut inhabitants := #[]
  for row in inhabitantRows environment claim do
    match ← checkInhabitant claim row.inhabitant with
    | .ok parameters =>
        inhabitants := inhabitants.push (row.inhabitant, parameters)
    | .error reason =>
        stale := stale.push m!"stale inhabitant {claim} by {row.inhabitant}: \
          {reason}"
  let auto ←
    if !inhabitants.isEmpty then pure none
    else
      -- A binder type that the instance search cannot handle leaves the
      -- claim without an automatic instance, so its inhabitant stays owed.
      try autoInstance? info shape catch _ => pure none
  return { claim, group, shape, unused, witnesses, inhabitants, auto, stale }

/-- Every obligation the claim owes: an inhabitant when it has binders, a
witness per premise, and the unbundling of each bundled binder. -/
private def ClaimAudit.owed (audit : ClaimAudit) : Array Obligation :=
  match audit.shape.kind with
  | .definition | .closed => #[]
  | .unconditional | .conditional =>
      #[Obligation.inhabitant] ++
        audit.shape.premises.map (fun premise => .necessity premise.id) ++
        audit.shape.bundled.map .bundled

private def ClaimAudit.meets (audit : ClaimAudit) : Obligation → Bool
  | .inhabitant => !audit.inhabitants.isEmpty || audit.auto.isSome
  | .necessity premise => audit.witnesses.any (·.1 == premise)
  | .bundled _ => false

/-- The owed obligations that no row meets. -/
private def ClaimAudit.unmet (audit : ClaimAudit) : Array Obligation :=
  audit.owed.filter fun obligation => !audit.meets obligation

/-- A claim's unmet obligations checked against its baseline row. -/
private structure Verdict where
  exempt : Array Obligation
  pending : Array Obligation
  details : Array MessageData

private def labels (obligations : Array Obligation) : String :=
  ", ".intercalate (obligations.map Obligation.label).toList

private def openDetail (audit : ClaimAudit) (pending : Array Obligation) :
    MessageData :=
  let unused := audit.unused.getD #[]
  let shown := pending.map fun obligation =>
    match obligation with
    | .necessity premise =>
        if unused.contains premise then s!"{obligation.label} (unused)"
        else obligation.label
    | _ => obligation.label
  m!"open {audit.claim}: [{", ".intercalate shown.toList}]"

private def verdictOf (environment : Environment) (audit : ClaimAudit)
    (row? : Option BaselineRow) : Verdict := Id.run do
  let unmet := audit.unmet
  let listed := (row?.map (·.obligations)).getD #[]
  let exempt := unmet.filter listed.contains
  let pending := unmet.filter fun obligation => !listed.contains obligation
  let mut details := audit.stale
  unless pending.isEmpty do
    details := details.push (openDetail audit pending)
  if let some row := row? then
    let extra := listed.filter fun obligation => !unmet.contains obligation
    if unmet.isEmpty then
      details := details.push m!"stale baseline {audit.claim}: remove the \
        row, since the claim owes nothing"
    else if !extra.isEmpty then
      details := details.push m!"stale baseline {audit.claim}: remove \
        [{labels extra}]"
    if let some previous := row.previous then
      if environment.contains previous then
        details := details.push m!"stale baseline {audit.claim} (was \
          {previous}): {previous} is still declared"
  return { exempt, pending, details }

/-- The counts that one audit line reports. -/
private structure Tally where
  claims : Nat := 0
  definitions : Nat := 0
  conditional : Nat := 0
  premises : Nat := 0
  witnessed : Nat := 0
  unused : Nat := 0
  required : Nat := 0
  inhabited : Nat := 0
  auto : Nat := 0
  bundled : Nat := 0
  wrapped : Nat := 0
  exempt : Nat := 0
  pending : Nat := 0

private def count (holds : Bool) : Nat :=
  if holds then 1 else 0

private def Tally.add (tally : Tally) (audit : ClaimAudit)
    (verdict : Verdict) : Tally :=
  let kind := audit.shape.kind
  let obliged := kind == .unconditional || kind == .conditional
  let witnessed := audit.shape.premises.filter fun premise =>
    audit.meets (.necessity premise.id)
  { claims := tally.claims + 1
    definitions := tally.definitions + count (kind == .definition)
    conditional := tally.conditional + count (kind == .conditional)
    premises := tally.premises + audit.shape.premises.size
    witnessed := tally.witnessed + witnessed.size
    unused := tally.unused + (audit.unused.getD #[]).size
    required := tally.required + count obliged
    inhabited := tally.inhabited + count (obliged && audit.meets .inhabitant)
    auto := tally.auto + count (obliged && audit.auto.isSome)
    bundled := tally.bundled + audit.shape.bundled.size
    wrapped := tally.wrapped + count audit.shape.wrapped
    exempt := tally.exempt + verdict.exempt.size
    pending := tally.pending + verdict.pending.size }

private def Tally.merge (left right : Tally) : Tally :=
  { claims := left.claims + right.claims
    definitions := left.definitions + right.definitions
    conditional := left.conditional + right.conditional
    premises := left.premises + right.premises
    witnessed := left.witnessed + right.witnessed
    unused := left.unused + right.unused
    required := left.required + right.required
    inhabited := left.inhabited + right.inhabited
    auto := left.auto + right.auto
    bundled := left.bundled + right.bundled
    wrapped := left.wrapped + right.wrapped
    exempt := left.exempt + right.exempt
    pending := left.pending + right.pending }

private def Tally.line (tally : Tally) : String :=
  s!"{tally.claims} claims, {tally.definitions} definitions, \
    {tally.conditional} conditional, necessity {tally.witnessed} of \
    {tally.premises} premises ({tally.unused} unused), inhabited \
    {tally.inhabited} of {tally.required} ({tally.auto} auto), bundled \
    {tally.bundled}, wrapped {tally.wrapped}, exempt {tally.exempt}, open \
    {tally.pending}"

/-- The details under one audit line: the first `limit` in full, and a count
of the rest, so that a package with many open claims holds at most `limit`
messages per line. -/
structure Details where
  limit : Nat
  shown : Array MessageData := #[]
  hidden : Nat := 0

def Details.push (details : Details) (detail : MessageData) : Details :=
  if details.shown.size < details.limit then
    { details with shown := details.shown.push detail }
  else
    { details with hidden := details.hidden + 1 }

def Details.isEmpty (details : Details) : Bool :=
  details.shown.isEmpty && details.hidden == 0

/-- `line`, then the shown details one per line, then the number left out. -/
def Details.message (details : Details) (line : MessageData) : MessageData :=
  let tail :=
    if details.hidden == 0 then #[] else #[m!"and {details.hidden} more"]
  MessageData.joinSep (#[line] ++ details.shown ++ tail).toList "\n"

/-- `line`, then at most `limit` of `details` one per line, then the number
of details left out. -/
def withDetails (limit : Nat) (line : MessageData)
    (details : Array MessageData) : MessageData :=
  (details.foldl Details.push { limit }).message line

/-- Logs `line` with its details. The message is an error when the details
are not empty and `enforce` holds, and information otherwise. -/
private def report (enforce : Bool) (line : MessageData) (details : Details) :
    CommandElabM Unit := do
  let message := details.message line
  if enforce && !details.isEmpty then logError message else logInfo message

private def declaringModule (environment : Environment) (declaration : Name) :
    Name :=
  match environment.getModuleIdxFor? declaration with
  | some index =>
      environment.header.moduleNames[index.toNat]?.getD environment.mainModule
  | none => environment.mainModule

private def exportRow (audit : ClaimAudit) (verdict : Verdict) :
    MetaM ClaimRow := do
  let environment ← getEnv
  let premises := audit.shape.premises.map fun premise => {
    id := premise.id
    used :=
      match audit.unused with
      | some unused => if unused.contains premise.id then .no else .yes
      | none => .unknown
    witness := (audit.witnesses.find? (·.1 == premise.id)).map (·.2)
    : PremiseEntry }
  let registered ← audit.inhabitants.mapM fun (name, parameters) => do
    return { name := some name, instanceText := ← instanceText parameters
      : InhabitantEntry }
  let automatic ← audit.auto.toArray.mapM fun parameters => do
    return { name := none, instanceText := ← instanceText parameters
      : InhabitantEntry }
  return {
    name := audit.claim
    moduleName := declaringModule environment audit.claim
    group := audit.group
    kind := audit.shape.kind
    arity := audit.shape.arity
    axioms := sortedNames (← collectAxioms audit.claim)
    premises
    dependent := audit.shape.dependent
    bundled := audit.shape.bundled
    wrapped := audit.shape.wrapped
    inhabitants := registered ++ automatic
    exempt := verdict.exempt
    pending := verdict.pending
  }

/-- The claim groups registered under `roots`, sorted by module. -/
private def groupsUnder (roots : Array Name) :
    CommandElabM (Array ClaimGroup) := do
  let groups := (claimGroups (← getEnv)).filter fun group =>
    roots.any (·.isPrefixOf group.moduleName)
  unless !groups.isEmpty do
    throwError m!"premise ledger: no claim groups are registered under \
      [{formatNames roots}]"
  let claims := groups.foldl (init := #[]) fun names group =>
    names ++ group.claimNames
  let duplicates := duplicateNames claims
  unless duplicates.isEmpty do
    throwError m!"premise ledger: claims registered in multiple groups \
      [{formatNames duplicates}]"
  return groups.qsort fun left right =>
    Name.lt left.moduleName right.moduleName

syntax (name := auditPremiseLedgerCommand)
  "#audit_premise_ledger " "[" ident,* "]" : command

@[command_elab auditPremiseLedgerCommand]
def elabAuditPremiseLedger : CommandElab
  | `(#audit_premise_ledger [$rootSyntaxes,*]) => do
      let roots := rootSyntaxes.getElems.map (·.getId.eraseMacroScopes)
      unless !roots.isEmpty do
        throwError "premise ledger: the audit names no root"
      let duplicates := duplicateNames roots
      unless duplicates.isEmpty do
        throwError m!"premise ledger: duplicate roots \
          [{formatNames duplicates}]"
      let options ← getOptions
      let enforce := trust.ledger.enforce.get options
      let exporting := trust.ledger.export.get options
      let emitting := trust.ledger.emitBaseline.get options
      let revision := trust.ledger.revision.get options
      if exporting && !validRevision revision then
        throwError m!"premise ledger: export needs trust.ledger.revision to \
          hold 40 lowercase hexadecimal characters, not \"{revision}\""
      let environment ← getEnv
      let groups ← groupsUnder roots
      let baseline := (baselineExtension.getState environment).getD #[]
      let rows : NameMap BaselineRow := baseline.foldl (init := {})
        fun rows row => rows.insert row.claim row
      let mut total : Tally := {}
      let mut audited : NameSet := {}
      let mut needed := #[]
      let mut exported := #[]
      for group in groups do
        let mut tally : Tally := {}
        let mut details : Details := { limit := detailLimit }
        for claim in group.claimNames do
          let audit ← liftTermElabM (readClaim group.moduleName claim)
          let row? := rows.find? claim
          let verdict := verdictOf environment audit row?
          tally := tally.add audit verdict
          details := verdict.details.foldl Details.push details
          audited := audited.insert claim
          let unmet := audit.unmet
          if emitting && !unmet.isEmpty then
            needed := needed.push {
              claim
              previous := row?.bind (·.previous)
              obligations := unmet }
          if exporting then
            let claimRow ← liftTermElabM (exportRow audit verdict)
            exported := exported.push claimRow
        report enforce m!"premise ledger {group.moduleName}: {tally.line}"
          details
        total := total.merge tally
      let noStrays : Details := { limit := detailLimit }
      let strays := baseline.foldl (init := noStrays) fun strays row =>
        if audited.contains row.claim then strays
        else strays.push m!"stale baseline {row.claim}: no audited claim has \
          this name"
      report enforce m!"premise ledger total [{formatNames roots}]: \
        {groups.size} groups, {total.line}" strays
      if emitting then
        logInfo <| linesMessage <| baselineLines <| sortByName (·.claim) needed
      if exporting then
        match renderRows revision (trust.ledger.clean.get options) exported with
        | .ok lines => logInfo (linesMessage lines)
        | .error problem => throwError m!"premise ledger export: {problem}"
  | _ => throwUnsupportedSyntax

end Trust.Ledger
