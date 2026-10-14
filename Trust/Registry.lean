import Lean.EnvExtension
import Trust.Claim
import Trust.Policy

namespace Trust

open Lean

/-- A roster of claims audited under one policy. A registered group comes from
`#register_trust_claims`, and a tagged group holds the `@[trust_claim]`
declarations of one module under the trust ceiling. `reppl-scan` mirrors this
layout to read registered groups from `.olean` files. -/
structure ClaimGroup where
  moduleName : Name
  allowed : Array Name
  claimNames : Array Name
deriving Inhabited, BEq, Repr

private def addImportedGroups (modules : Array (Array ClaimGroup)) :
    Array ClaimGroup :=
  modules.foldl (init := #[]) fun groups moduleGroups =>
    moduleGroups.foldl (init := groups) Array.push

initialize claimGroupsExtension :
    SimplePersistentEnvExtension ClaimGroup (Array ClaimGroup) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := addImportedGroups
  }

def registeredClaimGroups (environment : Environment) : Array ClaimGroup :=
  claimGroupsExtension.getState environment

private def taggedGroup (moduleName : Name) (claimNames : Array Name) :
    ClaimGroup :=
  { moduleName
    allowed := sortedNames trustCeiling
    claimNames := sortedNames claimNames }

/-- One group per module that tags a claim, the current module last. -/
def taggedClaimGroups (environment : Environment) : Array ClaimGroup := Id.run do
  let moduleNames := environment.header.moduleNames
  let mut groups := #[]
  for index in [:moduleNames.size] do
    let claimNames := claimAttribute.ext.getModuleEntries environment index
    unless claimNames.isEmpty do
      groups := groups.push (taggedGroup moduleNames[index]! claimNames)
  let current := (claimAttribute.ext.getState environment).toArray
  unless current.isEmpty do
    groups := groups.push (taggedGroup environment.mainModule current)
  return groups

def claimGroups (environment : Environment) : Array ClaimGroup :=
  registeredClaimGroups environment ++ taggedClaimGroups environment

def addClaimGroup (environment : Environment) (group : ClaimGroup) :
    Environment :=
  claimGroupsExtension.addEntry environment group

end Trust
