module

public import Problib.Measure.Exchangeable.Perm
public import Problib.Measure.Exchangeable.History
public import Problib.Measure.Exchangeable.Urn
public import Problib.Measure.Exchangeable.Sampled
public import Problib.Measure.Exchangeable.Trace
public import Problib.Measure.Exchangeable.View
public import Problib.Measure.Exchangeable.Family
public import Problib.Measure.Exchangeable.Power
public import Problib.Measure.Exchangeable.Density
public import Problib.Measure.Exchangeable.Latent
public import Problib.Measure.Exchangeable.Witness
public import Problib.Measure.Exchangeable.Delete
public import Problib.Measure.Exchangeable.Finite
public import Problib.Measure.Exchangeable.Sufficient
public import Problib.Measure.Exchangeable.Normal
public import Problib.Measure.Exchangeable.Site
public import Problib.Measure.Exchangeable.Keyed
public import Problib.Measure.Exchangeable.Gibbs
public import Problib.Measure.Exchangeable.Summary
public import Problib.Measure.Exchangeable.NormalTable
public import Problib.Measure.Exchangeable.DirichletCategorical
public import Problib.Measure.Exchangeable.Seated
public import Problib.Measure.Exchangeable.Conjugate
public import Problib.Measure.Exchangeable.KeyedSite

/-!
# Exchangeable urns

Permutations of finite slots, finite histories, sequential predictives (urns),
their sampling kernels and the laws of their histories, equivariant views of
histories, and Markov law families. Product powers are permutation invariant,
history laws have the chain as their density, latent presentations witness
exchangeability, keyed urns lift local latent tables, and exchangeable views
survive deletion. Urns run on summaries of their statistics, the Normal and
Dirichlet–categorical urns carry local latent tables, and an allocation urn
seats a keyed likelihood urn. Conjugate pairs carry their latent parameters as
local latent values whose steps are the pairs' conjugacy identities.
-/
