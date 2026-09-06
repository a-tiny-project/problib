import Trust.Audit
import Trust.Registry
import Lean.Data.Json

namespace Trust

open Lean Elab Command

declare_syntax_cat trustNameList

syntax "[" ident,* "]" : trustNameList

private def nameSyntaxes (list : TSyntax `trustNameList) :
    Array (TSyntax `ident) :=
  match list with
  | `(trustNameList| [$[$names:ident],*]) => names
  | _ => #[]

private def literalNames (list : TSyntax `trustNameList) : Array Name :=
  (nameSyntaxes list).map fun nameSyntax =>
    nameSyntax.getId.eraseMacroScopes

private def resolveNames (nameSyntaxes : Array (TSyntax `ident)) :
    CommandElabM (Array Name) := do
  let mut names := #[]
  for nameSyntax in nameSyntaxes do
    let name ← withRef nameSyntax <| liftCoreM <|
      realizeGlobalConstNoOverloadWithInfo nameSyntax
    names := names.push name
  return names

private def createPolicy (nameSyntaxes : Array (TSyntax `ident)) :
    CommandElabM Policy := do
  let allowed ← resolveNames nameSyntaxes
  match Policy.create allowed with
  | .ok policy => return policy
  | .error message => throwError m!"trust audit: {message}"

private def auditClaimNames (policy : Policy) (claimNames : Array Name) :
    CommandElabM Unit := do
  for claim in sortedNames claimNames do
    let evidence ← auditClaim policy claim
    logInfo m!"trust claim {evidence.claim}: axioms [{formatNames evidence.axioms}]"

private structure RegisteredClaimEvidence where
  moduleName : Name
  evidence : ClaimEvidence

structure ExportClaim where
  name : String
  moduleName : String
  axioms : Array String

instance : Quote ExportClaim `term where
  quote claim := Syntax.mkCApp ``ExportClaim.mk
    #[quote claim.name, quote claim.moduleName, quote claim.axioms]

private def registeredGroups : CommandElabM (Array ClaimGroup) := do
  let groups := (claimGroups (← getEnv)).qsort fun left right =>
    Name.lt left.moduleName right.moduleName
  unless !groups.isEmpty do
    throwError "trust audit: no claim groups are registered"
  let allClaims := groups.foldl (init := #[]) fun names group =>
    names ++ group.claimNames
  let duplicates := duplicateNames allClaims
  unless duplicates.isEmpty do
    throwError m!"trust audit: claims registered in multiple groups [{formatNames duplicates}]"
  return groups

private def groupPolicy (group : ClaimGroup) : CommandElabM Policy := do
  match Policy.create group.allowed with
  | .ok policy => return policy
  | .error message =>
      throwError m!"trust audit: invalid policy in {group.moduleName}: {message}"

private def declarationModule (claim : Name) : CommandElabM Name := do
  let environment ← getEnv
  let some moduleIndex := environment.getModuleIdxFor? claim
    | throwError m!"trust export: claim {claim} is not from an imported module"
  let some moduleName := environment.header.moduleNames[moduleIndex.toNat]?
    | throwError m!"trust export: claim {claim} has an invalid module index"
  return moduleName

private def auditRegisteredClaims :
    CommandElabM (Array RegisteredClaimEvidence) := do
  let mut result := #[]
  for group in ← registeredGroups do
    let policy ← groupPolicy group
    for claim in group.claimNames do
      let moduleName ← declarationModule claim
      let evidence ← auditClaim policy claim
      result := result.push { moduleName, evidence }
  return result.qsort fun left right =>
    Name.lt left.evidence.claim right.evidence.claim

private def claimJson
    (sourceRevision : String)
    (sourceClean : Bool)
    (claim : ExportClaim) : Json :=
  Json.mkObj
    [("schema", .str "tiny.verification.claim/v1"),
     ("name", .str claim.name),
     ("module", .str claim.moduleName),
     ("axioms", .arr <| claim.axioms.map Json.str),
     ("source_revision", .str sourceRevision),
     ("source_clean", toJson sourceClean)]

def renderClaims
    (sourceRevision : String)
    (sourceClean : Bool)
    (claims : Array ExportClaim) : String :=
  String.intercalate "\n" (claims.toList.map fun claim =>
    (claimJson sourceRevision sourceClean claim).compress) ++ "\n"

private def exportClaims
    (claims : Array RegisteredClaimEvidence) : Array ExportClaim :=
  claims.map fun claim => {
    name := claim.evidence.claim.toString
    moduleName := claim.moduleName.toString
    axioms := claim.evidence.axioms.map Name.toString
  }

syntax (name := auditPackageCommand)
  "#audit_package" trustNameList "allowing" trustNameList : command

@[command_elab auditPackageCommand]
def elabAuditPackage : CommandElab
  | `(#audit_package $roots:trustNameList allowing $allowed:trustNameList) => do
      let rootNames := literalNames roots
      unless !rootNames.isEmpty do
        throwError "trust audit: package root roster is empty"
      let duplicates := duplicateNames rootNames
      unless duplicates.isEmpty do
        throwError m!"trust audit: duplicate package roots [{formatNames duplicates}]"
      let environment ← getEnv
      let primary := rootNames[0]!
      let expectedModule := primary ++ `Axioms
      unless environment.mainModule == expectedModule do
        throwError m!"trust audit: package audit for {primary} must run from \
          {expectedModule}, not {environment.mainModule}"
      let policy ← createPolicy <| nameSyntaxes allowed
      for root in sortedNames rootNames do
        let evidence ← auditPackage root policy
        logInfo m!"trust package {evidence.root}: {evidence.declarationCount} \
          declarations, axioms [{formatNames evidence.axioms}]"
  | _ => throwUnsupportedSyntax

syntax (name := auditClaimsCommand)
  "#audit_claims" "allowing" trustNameList
    "claims" trustNameList : command

@[command_elab auditClaimsCommand]
def elabAuditClaims : CommandElab
  | `(#audit_claims allowing $allowed:trustNameList
      claims $roster:trustNameList) => do
      let policy ← createPolicy <| nameSyntaxes allowed
      let claimNames ← resolveNames <| nameSyntaxes roster
      unless !claimNames.isEmpty do
        throwError "trust audit: claim roster is empty"
      let duplicates := duplicateNames claimNames
      unless duplicates.isEmpty do
        throwError m!"trust audit: duplicate claims [{formatNames duplicates}]"
      auditClaimNames policy claimNames
  | _ => throwUnsupportedSyntax

syntax (name := registerTrustClaimsCommand)
  "#register_trust_claims" "allowing" trustNameList
    "claims" trustNameList : command

@[command_elab registerTrustClaimsCommand]
def elabRegisterTrustClaims : CommandElab
  | `(#register_trust_claims allowing $allowed:trustNameList
      claims $roster:trustNameList) => do
      let environment ← getEnv
      let moduleName := environment.mainModule
      if (claimGroups environment).any fun group =>
          group.moduleName == moduleName then
        throwError m!"trust audit: claims already registered for module {moduleName}"
      let policy ← createPolicy <| nameSyntaxes allowed
      let claimNames ← resolveNames <| nameSyntaxes roster
      unless !claimNames.isEmpty do
        throwError "trust audit: claim roster is empty"
      let duplicates := duplicateNames claimNames
      unless duplicates.isEmpty do
        throwError m!"trust audit: duplicate claims [{formatNames duplicates}]"
      modifyEnv fun environment =>
        addClaimGroup environment {
          moduleName
          allowed := policy.allowed
          claimNames := sortedNames claimNames
        }
  | _ => throwUnsupportedSyntax

syntax (name := auditRegisteredTrustClaimsCommand)
  "#audit_registered_claims" : command

@[command_elab auditRegisteredTrustClaimsCommand]
def elabAuditRegisteredTrustClaims : CommandElab
  | `(#audit_registered_claims) => do
      for group in ← registeredGroups do
        let policy ← groupPolicy group
        logInfo m!"trust group {group.moduleName}: {group.claimNames.size} claims, \
          allowing [{formatNames policy.allowed}]"
        auditClaimNames policy group.claimNames
  | _ => throwUnsupportedSyntax

syntax (name := defineRegisteredClaimsCommand)
  "#define_registered_claims" ident : command

@[command_elab defineRegisteredClaimsCommand]
def elabDefineRegisteredClaims : CommandElab
  | `(#define_registered_claims $name:ident) => do
      let rows := exportClaims (← auditRegisteredClaims)
      let declaration ← `(def $name : Array ExportClaim := $(quote rows))
      elabCommand declaration
  | _ => throwUnsupportedSyntax

end Trust
