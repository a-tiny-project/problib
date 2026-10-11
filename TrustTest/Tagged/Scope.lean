import Trust
import TrustTest.Registry.Alpha
import TrustTest.Tagged.Clean

/-! An audit run from another root leaves `TrustTest` tags to `TrustTest`'s own
audit and still audits every registered group it imports. -/

open Lean Elab Command in
elab "#audit_registered_claims_from " root:ident : command => do
  let mainModule := (← getEnv).mainModule
  modifyEnv (·.setMainModule root.getId)
  try elabCommand (← `(#audit_registered_claims))
  finally modifyEnv (·.setMainModule mainModule)

/--
info: trust group TrustTest.Registry.Alpha: 1 claims, allowing [Classical.choice]
---
info: trust claim TrustTest.Registry.Alpha.choose: axioms [Classical.choice]
-/
#guard_msgs(info) in
#audit_registered_claims_from Outside.Axioms
