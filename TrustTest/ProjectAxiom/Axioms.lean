import Trust

namespace TrustTest.ProjectAxiom

axiom projectAxiom : True

/--
error: trust audit: package TrustTest.ProjectAxiom owns axiom declarations [TrustTest.ProjectAxiom.projectAxiom]
-/
#guard_msgs(error) in
#audit_package [TrustTest.ProjectAxiom] allowing []

end TrustTest.ProjectAxiom
