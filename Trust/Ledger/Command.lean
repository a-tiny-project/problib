import Lean.Elab.App
import Lean.Elab.Command
import Trust.Ledger.Premises

/-! Commands of the premise ledger.

`#premises C` prints how the ledger reads claim `C`. `drop% C p` elaborates to
`C` without premise `p`. The registration commands add rows when their check
accepts. In report mode a refused registration is a warning, and under
`set_option trust.ledger.enforce true` it is an error. The `#check_*` commands
print one verdict and register nothing. -/

namespace Trust.Ledger

open Lean Elab Command Term Meta

private def resolveName (nameSyntax : Syntax) : CommandElabM Name :=
  withRef nameSyntax <| liftCoreM <|
    realizeGlobalConstNoOverloadWithInfo nameSyntax

/-- Reports a refusal: a warning in report mode, and an error under
`set_option trust.ledger.enforce true`. -/
def refuse (message : MessageData) : CommandElabM Unit := do
  if trust.ledger.enforce.get (← getOptions) then
    logError message
  else
    logWarning message

private def necessityMessage (claim premise witness : Name) :
    Except MessageData Unit → MessageData
  | .ok () =>
      m!"premise ledger: accept necessity {claim} {premise} by {witness}"
  | .error reason =>
      m!"premise ledger: refuse necessity {claim} {premise} by {witness}: \
        {reason}"

/-- The instance an inhabitant names, on its own indented line so that a long
claim name never wraps an argument. -/
private def instanceMessage (parameters : Array (Name × Expr)) :
    MessageData :=
  if parameters.isEmpty then
    m!""
  else
    let bindings := parameters.toList.map fun (id, argument) =>
      m!"{id} := {argument}"
    m!" at{indentD m!"[{MessageData.joinSep bindings ", "}]"}"

private def inhabitantMessage (claim inhabitant : Name) :
    Except MessageData (Array (Name × Expr)) → MessageData
  | .ok parameters =>
      m!"premise ledger: accept inhabitant {claim} by {inhabitant}\
        {instanceMessage parameters}"
  | .error reason =>
      m!"premise ledger: refuse inhabitant {claim} by {inhabitant}: {reason}"

private def premiseLine (claim : ConstantInfo) (unused : Option (Array Name))
    (premise : Premise) : MetaM MessageData := do
  let flags :=
    if (unused.getD #[]).contains premise.id then
      s!"{premise.sort.label}, unused"
    else
      premise.sort.label
  match ← dropType claim.type premise.id with
  | .ok dropped => return m!"- {premise.id} ({flags}):{indentExpr dropped}"
  | .error reason => return m!"- {premise.id} ({flags}): {reason}"

/-- Every line `#premises` prints: the kind and arity, each premise with its
flags and its `drop%` type, then the dependent, bundled and negated
binders. -/
private def premisesMessage (claim : Name) : MetaM MessageData := do
  let info ← getConstInfo claim
  let shape ← shapeOf info.type
  let mut header := m!"premises {claim}: {shape.kind.label}"
  if shape.kind == .definition then return header
  header := header ++ m!", arity {shape.arity}"
  if shape.wrapped then
    header := header ++ m!", wrapped"
  let unused ← unusedPremises info
  if unused.isNone && !shape.premises.isEmpty then
    header := header ++ m!", unused unknown"
  let mut lines := #[header]
  for premise in shape.premises do
    lines := lines.push (← premiseLine info unused premise)
  unless shape.dependent.isEmpty do
    lines := lines.push m!"dependent [{formatNames shape.dependent}]"
  unless shape.bundled.isEmpty do
    lines := lines.push m!"bundled [{formatNames shape.bundled}]"
  if let some negated := shape.negated then
    lines := lines.push m!"negated {negated}"
  return MessageData.joinSep lines.toList "\n"

syntax (name := premisesCommand) "#premises " ident : command

@[command_elab premisesCommand]
def elabPremises : CommandElab
  | `(#premises $claimSyntax:ident) => do
      let claim ← resolveName claimSyntax
      logInfo (← liftTermElabM (premisesMessage claim))
  | _ => throwUnsupportedSyntax

syntax (name := registerPremiseRecordCommand)
  "#register_premise_record " ident : command

@[command_elab registerPremiseRecordCommand]
def elabRegisterPremiseRecord : CommandElab
  | `(#register_premise_record $recordSyntax:ident) => do
      let structName ← resolveName recordSyntax
      match ← liftTermElabM (premiseRecordProblem? structName) with
      | some problem =>
          refuse m!"premise ledger: refuse premise record {structName}: \
            {problem}"
      | none =>
          modifyEnv fun environment => addPremiseRecord environment {
            structName
            moduleName := environment.mainModule
          }
  | _ => throwUnsupportedSyntax

syntax (name := registerNecessityCommand)
  "#register_necessity " ident ident " := " ident : command

@[command_elab registerNecessityCommand]
def elabRegisterNecessity : CommandElab
  | `(#register_necessity $claimSyntax:ident $premiseSyntax:ident :=
      $witnessSyntax:ident) => do
      let claim ← resolveName claimSyntax
      let witness ← resolveName witnessSyntax
      let premise := premiseSyntax.getId.eraseMacroScopes
      let existing := (necessityRows (← getEnv) claim).find? fun row =>
        row.premise == premise
      let verdict ← match existing with
        | some row =>
            pure (.error m!"{premise} already has witness {row.witness}")
        | none => liftTermElabM (checkNecessity claim premise witness)
      match verdict with
      | .ok () =>
          modifyEnv fun environment => addNecessityRow environment {
            claim
            premise
            witness
            moduleName := environment.mainModule
          }
      | .error reason =>
          refuse (necessityMessage claim premise witness (.error reason))
  | _ => throwUnsupportedSyntax

syntax (name := registerInhabitantCommand)
  "#register_inhabitant " ident " := " ident : command

@[command_elab registerInhabitantCommand]
def elabRegisterInhabitant : CommandElab
  | `(#register_inhabitant $claimSyntax:ident := $inhabitantSyntax:ident) => do
      let claim ← resolveName claimSyntax
      let inhabitant ← resolveName inhabitantSyntax
      let registered := (inhabitantRows (← getEnv) claim).any fun row =>
        row.inhabitant == inhabitant
      let verdict ←
        if registered then
          pure (.error m!"{inhabitant} is already registered")
        else
          liftTermElabM (checkInhabitant claim inhabitant)
      match verdict with
      | .ok _ =>
          modifyEnv fun environment => addInhabitantRow environment {
            claim
            inhabitant
            moduleName := environment.mainModule
          }
      | .error reason =>
          refuse (inhabitantMessage claim inhabitant (.error reason))
  | _ => throwUnsupportedSyntax

syntax (name := checkNecessityCommand)
  "#check_necessity " ident ident " := " ident : command

@[command_elab checkNecessityCommand]
def elabCheckNecessity : CommandElab
  | `(#check_necessity $claimSyntax:ident $premiseSyntax:ident :=
      $witnessSyntax:ident) => do
      let claim ← resolveName claimSyntax
      let witness ← resolveName witnessSyntax
      let premise := premiseSyntax.getId.eraseMacroScopes
      let verdict ← liftTermElabM (checkNecessity claim premise witness)
      logInfo (necessityMessage claim premise witness verdict)
  | _ => throwUnsupportedSyntax

syntax (name := checkInhabitantCommand)
  "#check_inhabitant " ident " := " ident : command

@[command_elab checkInhabitantCommand]
def elabCheckInhabitant : CommandElab
  | `(#check_inhabitant $claimSyntax:ident := $inhabitantSyntax:ident) => do
      let claim ← resolveName claimSyntax
      let inhabitant ← resolveName inhabitantSyntax
      let verdict ← liftTermElabM (checkInhabitant claim inhabitant)
      logInfo (inhabitantMessage claim inhabitant verdict)
  | _ => throwUnsupportedSyntax

/-- `drop% C p` is the statement of claim `C` without premise `p`, and
`drop% C.{u, v} p` fixes its universe levels. Without levels, each level is a
fresh metavariable. -/
syntax (name := dropTerm) "drop% " term:max ident : term

private def elabDropOf (claimSyntax : Syntax) (levels? : Option (Array Syntax))
    (premiseSyntax : Syntax) : TermElabM Expr := do
  let claim ← realizeGlobalConstNoOverloadWithInfo claimSyntax
  let info ← getConstInfo claim
  let levels ← match levels? with
    | some levelSyntaxes =>
        let levels ← elabExplicitUnivs levelSyntaxes
        unless levels.length == info.levelParams.length do
          throwErrorAt claimSyntax m!"drop%: {claim} takes \
            {info.levelParams.length} universe levels, not {levels.length}"
        pure levels
    | none => info.levelParams.mapM fun _ => mkFreshLevelMVar
  let premise := premiseSyntax.getId.eraseMacroScopes
  match ← dropType (info.instantiateTypeLevelParams levels) premise with
  | .ok dropped => return dropped
  | .error reason => throwErrorAt premiseSyntax m!"drop% {claim}: {reason}"

@[term_elab dropTerm]
def elabDrop : TermElab := fun syntaxNode _ => do
  match syntaxNode with
  | `(drop% $claimSyntax:ident $premiseSyntax:ident) =>
      elabDropOf claimSyntax none premiseSyntax
  | `(drop% $claimSyntax:ident.{$levels,*} $premiseSyntax:ident) =>
      elabDropOf claimSyntax (some levels.getElems) premiseSyntax
  | _ => throwErrorAt syntaxNode[1]
      "drop% takes a claim name, with optional universe levels"

end Trust.Ledger
