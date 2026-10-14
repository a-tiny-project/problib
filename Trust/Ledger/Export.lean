import Lean.Data.Json
import Trust.Ledger.Premises

/-! Claim/v2 rows of the premise ledger.

A claim/v2 row keeps every field of the claim/v1 row that `Trust.Command`
exports: the name, the declaring module, the axioms, and the source revision
and cleanliness. It adds the ledger's reading of the claim: the group that
registers it, its kind and arity, each premise with its use and witness, the
dependent and bundled binders, whether the statement is wrapped, the
inhabitants with the instances they name, and the obligations the claim still
owes. An owed obligation is either exempt, because the package baseline lists
it, or open. Rows render one per line in byte order of their names, and an
export stays within fixed bounds so that a reader can hold it in fixed
buffers. -/

namespace Trust.Ledger

open Lean

/-- An obligation a claim owes the premise ledger. -/
inductive Obligation where
  /-- An inhabitant: a closed application of the claim, which names the
  instance where its premises hold together. -/
  | inhabitant
  /-- A witness that breaks the claim once the premise is dropped. -/
  | necessity (premise : Name)
  /-- A dependent binder of a registered record, which no witness can break
  the claim without until the record is unbundled. -/
  | bundled (binder : Name)
deriving Inhabited, BEq, Repr

/-- The obligation as a baseline row spells it. A premise named `inhabitant`
is quoted, so that it does not read as the inhabitant obligation. -/
def Obligation.label : Obligation → String
  | .inhabitant => "inhabitant"
  | .necessity premise =>
      if premise == `inhabitant then "«inhabitant»" else premise.toString
  | .bundled binder => s!"bundled {binder}"

/-- Whether a claim's proof reads a premise. The answer is unknown when the
proof is not in the environment. -/
inductive Use where
  | yes
  | no
  | unknown
deriving Inhabited, BEq, Repr

def Use.label : Use → String
  | .yes => "yes"
  | .no => "no"
  | .unknown => "unknown"

/-- One premise of an exported claim. -/
structure PremiseEntry where
  id : Name
  used : Use
  /-- The witness that passed its check, if the premise has one. -/
  witness : Option Name
deriving Inhabited, Repr

/-- One inhabitant of an exported claim. -/
structure InhabitantEntry where
  /-- The registered inhabitant, or `none` for the automatic one. -/
  name : Option Name
  /-- The instance, as `id := argument` pairs on one line. -/
  instanceText : String
deriving Inhabited, Repr

/-- One exported claim. -/
structure ClaimRow where
  name : Name
  moduleName : Name
  /-- The module that registers the claim's group. -/
  group : Name
  kind : ClaimKind
  arity : Nat
  axioms : Array Name
  premises : Array PremiseEntry
  dependent : Array Name
  bundled : Array Name
  wrapped : Bool
  inhabitants : Array InhabitantEntry
  /-- Owed obligations that the package baseline lists. -/
  exempt : Array Obligation
  /-- Owed obligations that the package baseline does not list. -/
  pending : Array Obligation
deriving Inhabited, Repr

/-- The schema every exported row names. -/
def claimSchemaV2 : String := "tiny.verification.claim/v2"

/-- The bounds of one export. A reader holds a whole export in fixed buffers
of these sizes. -/
structure ExportLimits where
  /-- Rows per export. -/
  rows : Nat := 16384
  /-- Bytes per export. -/
  bytes : Nat := 16 * 1024 * 1024
  /-- Premises per row. -/
  premises : Nat := 64
  /-- Bytes per name, premise id, or obligation label. -/
  idBytes : Nat := 512
  /-- Bytes per instance. A longer instance is cut at a character boundary
  and ends in `...`. -/
  instanceBytes : Nat := 512
deriving Inhabited, Repr

/-- Whether `revision` names a commit: 40 lowercase hexadecimal
characters. -/
def validRevision (revision : String) : Bool :=
  revision.length == 40 && revision.all fun character =>
    ('0' ≤ character && character ≤ '9') ||
      ('a' ≤ character && character ≤ 'f')

/-- The longest prefix of `text` made of whole characters that fits in
`limit` bytes. -/
private def prefixWithin (text : String) (limit : Nat) : String := Id.run do
  let mut result := ""
  for character in text.toList do
    if result.utf8ByteSize + character.utf8Size > limit then
      return result
    result := result.push character
  return result

/-- `text` within `limit` bytes: whole when it fits, and otherwise cut at a
character boundary and ended with `...` when the limit has room for it. -/
def withinBytes (limit : Nat) (text : String) : String :=
  if text.utf8ByteSize ≤ limit then text
  else if limit < 3 then prefixWithin text limit
  else prefixWithin text (limit - 3) ++ "..."

private def nameJson (name : Name) : Json :=
  .str name.toString

private def optionalNameJson : Option Name → Json
  | some name => nameJson name
  | none => .null

private def PremiseEntry.toJson (entry : PremiseEntry) : Json :=
  Json.mkObj
    [("id", nameJson entry.id),
     ("used", .str entry.used.label),
     ("witness", optionalNameJson entry.witness)]

private def InhabitantEntry.toJson (limit : Nat) (entry : InhabitantEntry) :
    Json :=
  Json.mkObj
    [("auto", .bool entry.name.isNone),
     ("instance", .str (withinBytes limit entry.instanceText)),
     ("name", optionalNameJson entry.name)]

private def obligationsJson (obligations : Array Obligation) : Json :=
  .arr <| obligations.map fun obligation => .str obligation.label

/-- The claim/v2 object of one row, its instances cut to `instanceBytes`
bytes. -/
def ClaimRow.toJson (instanceBytes : Nat) (sourceRevision : String)
    (sourceClean : Bool) (row : ClaimRow) : Json :=
  Json.mkObj
    [("schema", .str claimSchemaV2),
     ("name", nameJson row.name),
     ("module", nameJson row.moduleName),
     ("group", nameJson row.group),
     ("kind", .str row.kind.label),
     ("arity", Lean.toJson row.arity),
     ("axioms", .arr <| row.axioms.map nameJson),
     ("premises", .arr <| row.premises.map PremiseEntry.toJson),
     ("dependent", .arr <| row.dependent.map nameJson),
     ("bundled", .arr <| row.bundled.map nameJson),
     ("wrapped", .bool row.wrapped),
     ("inhabitants", .arr <|
        row.inhabitants.map (InhabitantEntry.toJson instanceBytes)),
     ("exempt", obligationsJson row.exempt),
     ("open", obligationsJson row.pending),
     ("source_revision", .str sourceRevision),
     ("source_clean", .bool sourceClean)]

/-- Every name and label a row exports. -/
private def ClaimRow.ids (row : ClaimRow) : Array String :=
  #[row.name.toString, row.moduleName.toString, row.group.toString] ++
    row.axioms.map toString ++
    row.premises.map (fun entry => entry.id.toString) ++
    row.premises.filterMap (fun entry => entry.witness.map toString) ++
    row.dependent.map toString ++
    row.bundled.map toString ++
    row.inhabitants.filterMap (fun entry => entry.name.map toString) ++
    (row.exempt ++ row.pending).map Obligation.label

/-- Why `row` cannot be exported within `limits`, if it cannot. Names and
ids print within 64 bytes. -/
private def rowProblem? (limits : ExportLimits) (row : ClaimRow) :
    Option String :=
  let name := withinBytes 64 row.name.toString
  if row.premises.size > limits.premises then
    some s!"{name} has {row.premises.size} premises, above the limit of \
      {limits.premises}"
  else
    (row.ids.find? fun id => id.utf8ByteSize > limits.idBytes).map fun id =>
      s!"{name} exports an id of {id.utf8ByteSize} bytes, above the limit of \
        {limits.idBytes}: {withinBytes 64 id}"

/-- `items` in byte order of their names. Each name is rendered once, so the
sort's comparisons read strings and render nothing. -/
def sortByName {α : Type} (name : α → Name) (items : Array α) : Array α :=
  let keyed := items.map fun item => ((name item).toString, item)
  (keyed.qsort fun left right => left.1 < right.1).map (·.2)

/-- The rows as claim/v2 JSON lines in byte order of their names, without
line breaks. An export writes each line and a newline. Fails when the export
would exceed one of `limits`. -/
def renderRows (sourceRevision : String) (sourceClean : Bool)
    (rows : Array ClaimRow) (limits : ExportLimits := {}) :
    Except String (Array String) := do
  unless rows.size ≤ limits.rows do
    throw s!"{rows.size} rows exceed the limit of {limits.rows}"
  if let some problem := rows.findSome? (rowProblem? limits) then
    throw problem
  let lines := (sortByName (·.name) rows).map fun row =>
    (row.toJson limits.instanceBytes sourceRevision sourceClean).compress
  let bytes := lines.foldl (init := 0) fun bytes line =>
    bytes + line.utf8ByteSize + 1
  unless bytes ≤ limits.bytes do
    throw s!"{bytes} bytes exceed the limit of {limits.bytes}"
  return lines

end Trust.Ledger
