module

public import Problib.Measure.Exchangeable.Conjugate.GammaPoisson

/-!
# Conjugate urns

Conjugate pairs as urns with a local latent: the prior's parameters are the
statistic, the predictive is the marginal likelihood of the next observation,
and the step is the pair's conjugacy. The Gamma–Poisson urn carries the Gamma
parameters through counts, with the negative binomial predictive.
-/
