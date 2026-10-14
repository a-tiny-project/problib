import Trust

namespace TrustTest.Tagged.Duplicate

@[trust_claim]
theorem twice : True :=
  True.intro

#register_trust_claims allowing [] claims [
  TrustTest.Tagged.Duplicate.twice
]

/--
error: trust audit: claims registered in multiple groups [TrustTest.Tagged.Duplicate.twice]
-/
#guard_msgs(error) in
#audit_registered_claims

end TrustTest.Tagged.Duplicate
