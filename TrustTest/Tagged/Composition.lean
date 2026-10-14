import Trust
import TrustTest.Registry.Alpha
import TrustTest.Tagged.Clean
import TrustTest.Tagged.Module

/-! A tagged claim is audited and exported as a listed one is, including one
tagged in a `module` file. -/

/--
info: trust group TrustTest.Registry.Alpha: 1 claims, allowing [Classical.choice]
---
info: trust claim TrustTest.Registry.Alpha.choose: axioms [Classical.choice]
---
info: trust group TrustTest.Tagged.Clean (tagged): 2 claims, allowing [propext, Classical.choice, Quot.sound]
---
info: trust claim TrustTest.Tagged.Clean.choose: axioms [Classical.choice]
---
info: trust claim TrustTest.Tagged.Clean.plain: axioms []
---
info: trust group TrustTest.Tagged.Module (tagged): 1 claims, allowing [propext, Classical.choice, Quot.sound]
---
info: trust claim TrustTest.Tagged.Module.exported: axioms []
-/
#guard_msgs(info) in
#audit_registered_claims

#define_registered_claims taggedClaims

#guard (taggedClaims.map (·.name)) == #[
  "TrustTest.Registry.Alpha.choose",
  "TrustTest.Tagged.Clean.choose",
  "TrustTest.Tagged.Clean.plain",
  "TrustTest.Tagged.Module.exported"
]

#guard (taggedClaims.map (·.moduleName)) == #[
  "TrustTest.Registry.Alpha",
  "TrustTest.Tagged.Clean",
  "TrustTest.Tagged.Clean",
  "TrustTest.Tagged.Module"
]
