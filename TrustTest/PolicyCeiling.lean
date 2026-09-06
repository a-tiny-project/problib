import Trust
import TrustTest.External

namespace TrustTest.PolicyCeiling

theorem claim : True :=
  True.intro

/--
error: trust audit: allowed axioms exceed trust ceiling [TrustTest.External.alphaAxiom]
-/
#guard_msgs(error) in
#audit_claims allowing [
  TrustTest.External.alphaAxiom
] claims [
  TrustTest.PolicyCeiling.claim
]

end TrustTest.PolicyCeiling
