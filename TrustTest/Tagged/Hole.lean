import Trust

namespace TrustTest.Tagged.Hole

/--
warning: declaration uses `sorry`
-/
#guard_msgs(warning) in
@[trust_claim]
theorem hole : True := by
  sorry

end TrustTest.Tagged.Hole
