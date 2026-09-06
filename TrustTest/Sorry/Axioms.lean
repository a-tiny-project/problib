import Trust

namespace TrustTest.Sorry

/--
warning: declaration uses `sorry`
-/
#guard_msgs(warning) in
theorem projectHole : True := by
  sorry

/--
error: trust audit: declaration TrustTest.Sorry.projectHole has unapproved axioms [sorryAx]
-/
#guard_msgs(error) in
#audit_package [TrustTest.Sorry] allowing []

end TrustTest.Sorry
