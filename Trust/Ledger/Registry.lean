import Lean.Data.NameMap
import Lean.EnvExtension
import Trust.Registry

/-! Persistent rows of the premise ledger: registered premise records,
necessity witnesses, and inhabitants. Rows are keyed by claim, so a
registration or an audit reads one claim's rows without walking the rest. -/

namespace Trust.Ledger

open Lean

/-- A structure whose non-dependent binders split into one premise per field,
and whose dependent binders are bundled obligations. -/
structure PremiseRecord where
  structName : Name
  moduleName : Name
deriving Inhabited, BEq, Repr

/-- A witness that breaks `claim` once `premise` is dropped. -/
structure NecessityRow where
  claim : Name
  premise : Name
  witness : Name
  moduleName : Name
deriving Inhabited, BEq, Repr

/-- A declaration that applies `claim`, closed, to every binder but a negated
conclusion, so the claim's premises hold together at one instance. -/
structure InhabitantRow where
  claim : Name
  inhabitant : Name
  moduleName : Name
deriving Inhabited, BEq, Repr

/-- Rows grouped by the claim they name. -/
abbrev ClaimRows (α : Type) := NameMap (Array α)

private def pushClaimRow {α : Type} (rows : ClaimRows α) (claim : Name)
    (row : α) : ClaimRows α :=
  rows.insert claim (((rows.find? claim).getD #[]).push row)

private def addImportedRows {α σ : Type} (add : σ → α → σ) (initial : σ)
    (modules : Array (Array α)) : σ :=
  modules.foldl (init := initial) fun state rows => rows.foldl add state

private def addRecord (records : NameMap PremiseRecord)
    (record : PremiseRecord) : NameMap PremiseRecord :=
  records.insert record.structName record

private def addNecessity (rows : ClaimRows NecessityRow)
    (row : NecessityRow) : ClaimRows NecessityRow :=
  pushClaimRow rows row.claim row

private def addInhabitant (rows : ClaimRows InhabitantRow)
    (row : InhabitantRow) : ClaimRows InhabitantRow :=
  pushClaimRow rows row.claim row

initialize premiseRecordsExtension :
    SimplePersistentEnvExtension PremiseRecord (NameMap PremiseRecord) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := addRecord
    addImportedFn := addImportedRows addRecord {}
  }

initialize necessityExtension :
    SimplePersistentEnvExtension NecessityRow (ClaimRows NecessityRow) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := addNecessity
    addImportedFn := addImportedRows addNecessity {}
  }

initialize inhabitantExtension :
    SimplePersistentEnvExtension InhabitantRow (ClaimRows InhabitantRow) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := addInhabitant
    addImportedFn := addImportedRows addInhabitant {}
  }

register_option trust.ledger.enforce : Bool := {
  defValue := false
  descr := "report refused premise ledger registrations as errors, \
    not warnings"
}

def isPremiseRecord (environment : Environment) (structName : Name) : Bool :=
  (premiseRecordsExtension.getState environment).contains structName

def addPremiseRecord (environment : Environment) (record : PremiseRecord) :
    Environment :=
  premiseRecordsExtension.addEntry environment record

def necessityRows (environment : Environment) (claim : Name) :
    Array NecessityRow :=
  ((necessityExtension.getState environment).find? claim).getD #[]

def addNecessityRow (environment : Environment) (row : NecessityRow) :
    Environment :=
  necessityExtension.addEntry environment row

def inhabitantRows (environment : Environment) (claim : Name) :
    Array InhabitantRow :=
  ((inhabitantExtension.getState environment).find? claim).getD #[]

def addInhabitantRow (environment : Environment) (row : InhabitantRow) :
    Environment :=
  inhabitantExtension.addEntry environment row

/-- The policy of the claim group that registers `claim`, or the trust ceiling
for a tagged claim. Group rosters are sorted at registration and tag entries at
export, so each lookup is a binary search. -/
def claimPolicy? (environment : Environment) (claim : Name) : Option Policy :=
  let registered := (registeredClaimGroups environment).findSome? fun group =>
    if group.claimNames.binSearchContains claim Name.lt then
      some { allowed := group.allowed }
    else none
  registered <|> if claimAttribute.hasTag environment claim then
    some { allowed := sortedNames trustCeiling }
  else none

end Trust.Ledger
