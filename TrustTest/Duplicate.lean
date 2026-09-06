import Trust

namespace TrustTest.Duplicate

theorem claim : True :=
  True.intro

/--
error: trust audit: duplicate claims [TrustTest.Duplicate.claim]
-/
#guard_msgs(error) in
#audit_claims allowing [] claims [
  TrustTest.Duplicate.claim,
  TrustTest.Duplicate.claim
]

end TrustTest.Duplicate
