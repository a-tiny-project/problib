import Trust

namespace TrustTest.Tagged.Refusal

/--
error: trust audit: claim TrustTest.Tagged.Refusal.hidden is private
-/
#guard_msgs(error) in
@[trust_claim]
private theorem hidden : True :=
  True.intro

/--
error: Cannot add attribute `[trust_claim]` to declaration `True.intro` because it is in an imported module
-/
#guard_msgs(error) in
attribute [trust_claim] True.intro

end TrustTest.Tagged.Refusal
