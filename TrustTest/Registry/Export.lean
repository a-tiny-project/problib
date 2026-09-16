import Trust
import TrustTest.Registry.Gamma
import TrustTest.Registry.Beta

#define_registered_claims registryClaims

private def expected :=
  "{\"axioms\":[\"Classical.choice\"],\"module\":\"TrustTest.Registry.Alpha\"," ++
  "\"name\":\"TrustTest.Registry.Alpha.choose\"," ++
  "\"schema\":\"tiny.verification.claim/v1\",\"source_clean\":true," ++
  "\"source_revision\":\"0000000000000000000000000000000000000000\"}\n" ++
  "{\"axioms\":[\"propext\"],\"module\":\"TrustTest.Registry.Beta\"," ++
  "\"name\":\"TrustTest.Registry.Beta.propositional\"," ++
  "\"schema\":\"tiny.verification.claim/v1\",\"source_clean\":true," ++
  "\"source_revision\":\"0000000000000000000000000000000000000000\"}\n" ++
  "{\"axioms\":[\"Quot.sound\"],\"module\":\"TrustTest.Registry.Gamma\"," ++
  "\"name\":\"TrustTest.Registry.Gamma.quotient\"," ++
  "\"schema\":\"tiny.verification.claim/v1\",\"source_clean\":true," ++
  "\"source_revision\":\"0000000000000000000000000000000000000000\"}\n"

#guard Trust.renderClaims
  "0000000000000000000000000000000000000000" true registryClaims == expected
