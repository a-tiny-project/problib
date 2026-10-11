import Trust
import TrustTest.External

namespace TrustTest.Ordering

theorem mixedAxioms : True ∧ True :=
  ⟨TrustTest.External.zetaAxiom, TrustTest.External.alphaAxiom⟩

/--
error: trust audit: claim TrustTest.Ordering.mixedAxioms has unapproved axioms [TrustTest.External.alphaAxiom, TrustTest.External.zetaAxiom]
-/
#guard_msgs(error) in
#audit_claims allowing [] claims [
  TrustTest.Ordering.mixedAxioms
]

end TrustTest.Ordering
