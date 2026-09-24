import Trust

namespace TrustTest.Unsafe

unsafe def unsafeValue : Nat :=
  0

/--
error: trust audit: package TrustTest.Unsafe owns unsafe declarations [TrustTest.Unsafe.unsafeValue]
-/
#guard_msgs(error) in
#audit_package [TrustTest.Unsafe] allowing []

end TrustTest.Unsafe
