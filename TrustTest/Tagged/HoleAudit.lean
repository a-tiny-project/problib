import Trust
import TrustTest.Tagged.Hole

/-! A proof hole in a tagged claim fails the audit of a module that imports it. -/

/--
info: trust group TrustTest.Tagged.Hole (tagged): 1 claims, allowing [propext, Classical.choice, Quot.sound]
---
error: trust audit: claim TrustTest.Tagged.Hole.hole has unapproved axioms [sorryAx]
-/
#guard_msgs in
#audit_registered_claims
