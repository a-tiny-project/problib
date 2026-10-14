import Trust

namespace TrustTest.Registry.DuplicateRegistration

theorem first : True :=
  True.intro

theorem second : True :=
  True.intro

#register_trust_claims allowing [] claims [
  TrustTest.Registry.DuplicateRegistration.first
]

/--
error: trust audit: claims already registered for module TrustTest.Registry.DuplicateRegistration
-/
#guard_msgs(error) in
#register_trust_claims allowing [] claims [
  TrustTest.Registry.DuplicateRegistration.second
]

end TrustTest.Registry.DuplicateRegistration
