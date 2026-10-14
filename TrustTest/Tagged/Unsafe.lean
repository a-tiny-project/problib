import Trust

namespace TrustTest.Tagged.Unsafe

@[trust_claim]
unsafe def shortcut : Nat :=
  0

/--
info: trust group TrustTest.Tagged.Unsafe (tagged): 1 claims, allowing [propext, Classical.choice, Quot.sound]
---
error: trust audit: unsafe claim TrustTest.Tagged.Unsafe.shortcut
-/
#guard_msgs in
#audit_registered_claims

end TrustTest.Tagged.Unsafe
