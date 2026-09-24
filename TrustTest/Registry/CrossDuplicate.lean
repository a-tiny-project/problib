import Trust
import TrustTest.Registry.CrossLeft
import TrustTest.Registry.CrossRight

/--
error: trust audit: claims registered in multiple groups [True.intro]
-/
#guard_msgs(error) in
#audit_registered_claims
