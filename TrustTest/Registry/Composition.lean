import Trust
import TrustTest.Registry.Gamma
import TrustTest.Registry.Beta

/--
info: trust group TrustTest.Registry.Alpha: 1 claims, allowing [Classical.choice]
---
info: trust claim TrustTest.Registry.Alpha.choose: axioms [Classical.choice]
---
info: trust group TrustTest.Registry.Beta: 1 claims, allowing [propext]
---
info: trust claim TrustTest.Registry.Beta.propositional: axioms [propext]
---
info: trust group TrustTest.Registry.Gamma: 1 claims, allowing [Quot.sound]
---
info: trust claim TrustTest.Registry.Gamma.quotient: axioms [Quot.sound]
-/
#guard_msgs(info) in
#audit_registered_claims
