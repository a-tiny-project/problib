module

meta import Trust.Claim

namespace TrustTest.Tagged.Module

@[trust_claim]
public theorem exported : True :=
  True.intro

end TrustTest.Tagged.Module
