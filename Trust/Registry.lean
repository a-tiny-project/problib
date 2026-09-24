import Lean.EnvExtension
import Trust.Policy

namespace Trust

open Lean

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

def claimGroups (environment : Environment) : Array ClaimGroup :=
  claimGroupsExtension.getState environment

def addClaimGroup (environment : Environment) (group : ClaimGroup) :
    Environment :=
  claimGroupsExtension.addEntry environment group

end Trust
