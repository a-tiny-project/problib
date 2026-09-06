import Trust

namespace TrustTest.NativeDecide

theorem generatedAxiom :
    (List.range 32).reverse.reverse = List.range 32 := by
  native_decide

/--
error: trust audit: package TrustTest.NativeDecide owns axiom declarations [TrustTest.NativeDecide.generatedAxiom._native.native_decide.ax_1_1]
-/
#guard_msgs(error) in
#audit_package [TrustTest.NativeDecide] allowing []

end TrustTest.NativeDecide
