import Lean.Elab.Command
import Lean.Linter.EnvLinter.Frontend
import Lean.Util.CollectAxioms
import Lean.Util.Path
import Trust.Policy

namespace Trust

open Lean Elab Command

structure PackageEvidence where
  root : Name
  declarationCount : Nat
  axioms : Array Name

structure ClaimEvidence where
  claim : Name
  axioms : Array Name

private def insertName (names : Array Name) (name : Name) : Array Name :=
  if names.contains name then names else names.push name

private def insertNames (names additions : Array Name) : Array Name :=
  additions.foldl insertName names

/-- Source directories, searched in order: the source root of the module that
runs the audit, then `LEAN_SRC_PATH`. Lake builds a dependency from its
consumer's directory and sets no `LEAN_SRC_PATH`, so the audit takes its own
root from the file Lake compiles and never from the working directory. -/
private def sourceSearchPath : CommandElabM SearchPath := do
  let file : System.FilePath := ← getFileName
  let main := (← getEnv).mainModule
  let base := main.components.foldl (fun path _ => path.parent.getD path) file
  let own := if Lean.modToFilePath base main "lean" == file then [base] else []
  return own ++ (← liftIO getSrcSearchPath)

private def sourceModules (searchPath : SearchPath) (root : Name) :
    IO (Array Name) := do
  let base? ← searchPath.findM? fun base =>
    (Lean.modToFilePath base root "lean").pathExists <||>
      (Lean.modToFilePath base root "").isDir
  let some base := base? | return #[]
  let directory := Lean.modToFilePath base root ""
  let modules ← IO.mkRef #[]
  if ← (Lean.modToFilePath base root "lean").pathExists then
    modules.modify (·.push root)
  if ← directory.isDir then
    Lean.forEachModuleInDir directory fun suffix =>
      modules.modify (·.push (root ++ suffix))
  return sortedNames (← modules.get)

private def ownedDeclarations (root : Name) : CommandElabM (Array Name) := do
  let env ← getEnv
  let sources ← liftIO <| sourceModules (← sourceSearchPath) root
  unless !sources.isEmpty do
    throwError m!"trust audit: package root {root} has no Lean sources"
  let loaded := env.header.moduleNames.push env.mainModule
  let missing := sources.filter fun moduleName =>
    !loaded.contains moduleName
  unless missing.isEmpty do
    throwError m!"trust audit: package root {root} has unloaded source modules [{formatNames missing}]"
  let declarations ← liftCoreM <|
    Lean.Linter.EnvLinter.getDeclsInPackage root
  return sortedNames declarations

def auditPackage (root : Name) (policy : Policy) :
    CommandElabM PackageEvidence := do
  let env ← getEnv
  let declarations ← ownedDeclarations root
  let mut ownedAxioms := #[]
  let mut unsafeDeclarations := #[]
  for declaration in declarations do
    let some info := env.find? declaration
      | throwError m!"trust audit: unknown owned declaration {declaration}"
    if info.isUnsafe then
      unsafeDeclarations := unsafeDeclarations.push declaration
    if let .axiomInfo _ := info then
      ownedAxioms := ownedAxioms.push declaration
  unless ownedAxioms.isEmpty do
    throwError m!"trust audit: package {root} owns axiom declarations [{formatNames ownedAxioms}]"
  unless unsafeDeclarations.isEmpty do
    throwError m!"trust audit: package {root} owns unsafe declarations [{formatNames unsafeDeclarations}]"
  let mut usedAxioms := #[]
  for declaration in declarations do
    let axioms := sortedNames (← collectAxioms declaration)
    let rejected := axioms.filter fun name => !policy.permits name
    unless rejected.isEmpty do
      throwError m!"trust audit: declaration {declaration} has unapproved axioms [{formatNames rejected}]"
    usedAxioms := insertNames usedAxioms axioms
  return {
    root
    declarationCount := declarations.size
    axioms := sortedNames usedAxioms
  }

def auditClaim (policy : Policy) (claim : Name) :
    CommandElabM ClaimEvidence := do
  let env ← getEnv
  let some info := env.find? claim
    | throwError m!"trust audit: unknown claim {claim}"
  if info.isUnsafe then
    throwError m!"trust audit: unsafe claim {claim}"
  let axioms := sortedNames (← collectAxioms claim)
  let rejected := axioms.filter fun name => !policy.permits name
  unless rejected.isEmpty do
    throwError m!"trust audit: claim {claim} has unapproved axioms [{formatNames rejected}]"
  return { claim, axioms }

end Trust
