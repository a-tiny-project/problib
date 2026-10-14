module

public import Problib.Inference.Reciprocal
public import Problib.Inference.PseudoMarginal
public import Problib.Measure.Integral.Density.AlmostEverywhere
public import Problib.Measure.Integral.Density.Finite
public import Problib.Measure.Integral.Lebesgue.Zero
set_option autoImplicit false

/-! A weighted sampler paired with its density estimator.

Lew's stochastic probability interface pairs a density estimator `ξ`, whose
mean at `x` is a density `q(x)` of the target against a reference `ν`, with a
weighted sampler `χ` whose law is `ν(dx) ξ(x, dw)` weighted by `w`
(`Paired`). The sampler's weighted law is the pseudo-marginal extended target
read at the estimate itself, so the correspondence is a single equation between
the two delivered laws, not two separate facts about each.

- The drawn point follows the target (`Paired.marginal`, Lew's Prop. 1(1)).
- Read at the reciprocal weight `1/w`, the draws are properly weighted for `ν`
  weighted at `x` by the probability that the estimate is positive
  (`Paired.reciprocal`, Prop. 1(2)). Where the density vanishes the estimate is
  almost surely zero, so that weight vanishes there too
  (`estimate_null_of_density_zero`).
- When the estimate is almost surely positive wherever the density is, that
  weight is the indicator of the density's support, and the reciprocal draws
  are a strict reciprocal sampler (`Paired.strictReciprocal`).
- An exact density, read as a Dirac estimate, pairs with the target's draws at
  that density (`paired_exact`).

Strict reciprocity alone does not give this correspondence: Problib's
`Necessity.Reciprocal.unpaired_strict` exhibits a strict reciprocal sampler for
a fair proposal that no exact estimator pairs with. -/

namespace Problib.Inference

open Problib.Real Problib.Measure

universe u

variable {α : Type u} {space : Space α}

public section

/-! ### The paired law -/

/-- Lew's stochastic probability interface. The estimator is unbiased for a
density of the target against the reference, and the sampler's weighted law is
the reference's draw paired with an estimate, weighted by that estimate. -/
structure Paired (reference target : Measure space) (density : α → ENNReal)
    (estimate : Kernel space weightSpace) (estimateFinite : Kernel.IsSFinite estimate)
    (weighted : Measure (Space.product space weightSpace)) : Prop where
  isDensity : Measure.IsDensity target reference density
  unbiased : UnbiasedEstimate density estimate
  joint : weighted = extendedTarget reference estimate estimateFinite Prod.snd

/-- Reading the estimate off its own draw returns the estimator. -/
theorem readEstimate_snd (estimate : Kernel space weightSpace)
    (estimateFinite : Kernel.IsSFinite estimate) :
    readEstimate estimate estimateFinite Prod.snd (Space.second_measurable space weightSpace) =
      estimate :=
  Kernel.ext fun input =>
    (readEstimate_apply estimate estimateFinite (Space.second_measurable space weightSpace)
      input).trans (Measure.map_id (estimate input))

/-- The paired sampler's drawn point follows the target, Lew's Prop. 1(1). -/
theorem Paired.marginal {reference target : Measure space} {density : α → ENNReal}
    {estimate : Kernel space weightSpace} {estimateFinite : Kernel.IsSFinite estimate}
    {weighted : Measure (Space.product space weightSpace)}
    (paired : Paired reference target density estimate estimateFinite weighted) :
    weighted.map Prod.fst (Space.first_measurable space weightSpace) = target := by
  have unbiased := paired.unbiased
  rw [← readEstimate_snd estimate estimateFinite] at unbiased
  rw [paired.joint, paired.isDensity.eq_withDensity]
  exact pseudo_marginal_marginal estimateFinite (Space.second_measurable space weightSpace)
    unbiased

/-! ### Reciprocal weights -/

/-- The reciprocal of each draw's weight, read as zero at zero. -/
theorem reciprocal_draw_measurable (space : Space α) :
    MeasurableMap (Space.product space weightSpace) (Space.product space weightSpace)
      (fun draw => (draw.1, NNReal.div NNReal.one draw.2)) :=
  Space.pair_measurable (Space.first_measurable space weightSpace)
    (weight_inverse_measurable (Space.second_measurable space weightSpace))

/-- A weight times its reciprocal, read as zero at zero, keeps a value exactly
where the weight is positive. -/
theorem finite_mul_reciprocal (weight : NNReal) (value : ENNReal) :
    ENNReal.mul (ENNReal.finite weight)
        (ENNReal.mul (ENNReal.finite (NNReal.div NNReal.one weight)) value) =
      ennrealIndicator (fun weight : NNReal => weight ≠ NNReal.zero) (fun _ => value) weight := by
  by_cases vanishing : weight = NNReal.zero
  · rw [ennrealIndicator_of_not_mem (region := fun weight : NNReal => weight ≠ NNReal.zero)
      (fun nonzero => nonzero vanishing), vanishing]
    exact ENNReal.zero_mul _
  · rw [ennrealIndicator_of_mem (region := fun weight : NNReal => weight ≠ NNReal.zero) vanishing,
      ← ENNReal.mul_assoc, ENNReal.finite_mul_finite, NNReal.mul_div_cancel NNReal.one vanishing]
    exact ENNReal.one_mul value

/-- The probability that an estimate is positive is measurable in the point. -/
theorem positive_measurable (estimate : Kernel space weightSpace) :
    ENNRealMeasurable space
      (fun input => estimate input fun weight => weight ≠ NNReal.zero) :=
  estimate.measurable (weight_support_measurable (MeasurableMap.identity weightSpace))

/-- The paired sampler's draws, read at the reciprocal weight, are properly
weighted for the reference weighted at `x` by the probability that the estimate
there is positive, Lew's Prop. 1(2). -/
theorem Paired.reciprocal {reference target : Measure space} {density : α → ENNReal}
    {estimate : Kernel space weightSpace} {estimateFinite : Kernel.IsSFinite estimate}
    {weighted : Measure (Space.product space weightSpace)}
    (paired : Paired reference target density estimate estimateFinite weighted)
    (probability : Measure.IsProbability target) :
    ProperlyWeighted
      (reference.withDensity fun input => estimate input fun weight => weight ≠ NNReal.zero)
      (weighted.map (fun draw => (draw.1, NNReal.div NNReal.one draw.2))
        (reciprocal_draw_measurable space)) := by
  have mass : weighted Set.univ = target Set.univ := by
    rw [← paired.marginal, Measure.map_apply _ _ _ space.univ, Set.preimage_univ]
  refine properlyWeighted_iff_lintegral.mpr ⟨⟨?_⟩, fun function measurable => ?_⟩
  · rw [Measure.map_apply _ _ _ (Space.product space weightSpace).univ, Set.preimage_univ, mass]
    exact probability.univ_eq_one
  have integrand := weighted_integrand_measurable measurable
  have reciprocal := integrand.comp (reciprocal_draw_measurable space)
  rw [lintegral_map _ _ _ integrand, paired.joint, extendedTarget,
    lintegral_withDensity _ (finite_weight_measurable (Space.second_measurable space weightSpace))
      reciprocal,
    lintegral_semiproduct _ _ _ (ENNRealMeasurable.mul
      (finite_weight_measurable (Space.second_measurable space weightSpace)) reciprocal),
    lintegral_withDensity _ (positive_measurable estimate) measurable]
  apply lintegral_congr
  intro input
  have pointwise : (fun weight : NNReal => ENNReal.mul (ENNReal.finite weight)
      (ENNReal.mul (ENNReal.finite (NNReal.div NNReal.one weight)) (function input))) =
      ennrealIndicator (fun weight : NNReal => weight ≠ NNReal.zero)
        (fun _ => function input) :=
    funext fun weight => finite_mul_reciprocal weight (function input)
  change lintegral (estimate input) (fun weight : NNReal => ENNReal.mul (ENNReal.finite weight)
      (ENNReal.mul (ENNReal.finite (NNReal.div NNReal.one weight)) (function input))) = _
  rw [pointwise, lintegral_indicator _ _
      (weight_support_measurable (MeasurableMap.identity weightSpace)),
    lintegral_const, Measure.restrict_apply_univ]
  exact ENNReal.mul_comm _ _

/-- Where the density vanishes, its unbiased estimate is almost surely zero. -/
theorem estimate_null_of_density_zero {density : α → ENNReal}
    {estimate : Kernel space weightSpace} (unbiased : UnbiasedEstimate density estimate)
    {input : α} (vanishing : density input = ENNReal.zero) :
    estimate input (fun weight => weight ≠ NNReal.zero) = ENNReal.zero := by
  have mean := unbiased.mean_eq input
  rw [vanishing] at mean
  have null := (lintegral_eq_zero_iff
    (finite_weight_measurable (MeasurableMap.identity weightSpace))).mp mean
  have same : (fun weight : NNReal => weight ≠ NNReal.zero) =
      Set.complement (fun weight : NNReal => ENNReal.finite weight = ENNReal.zero) := by
    funext weight
    exact propext ⟨fun nonzero equal => nonzero (ENNReal.finite_injective equal),
      fun nonzero equal => nonzero (congrArg ENNReal.finite equal)⟩
  rw [same]
  exact null

/-- When the estimate is almost surely positive wherever the density is, the
reference weighted by the probability of a positive estimate is the reference
restricted to the density's support. -/
theorem positive_reference_eq_restrict {reference : Measure space} {density : α → ENNReal}
    {estimate : Kernel space weightSpace} (unbiased : UnbiasedEstimate density estimate)
    (positive : reference.AE fun input => density input ≠ ENNReal.zero →
      estimate input (fun weight => weight ≠ NNReal.zero) = ENNReal.one) :
    (reference.withDensity fun input => estimate input fun weight => weight ≠ NNReal.zero) =
      reference.restrict fun input => density input ≠ ENNReal.zero := by
  have supportMeasurable : space.Measurable (fun input => density input ≠ ENNReal.zero) :=
    space.complement (ENNRealMeasurable.eq_set unbiased.mean_measurable
      (ENNRealMeasurable.constant space ENNReal.zero))
  calc (reference.withDensity fun input => estimate input fun weight => weight ≠ NNReal.zero)
      = reference.withDensity (ennrealIndicator (fun input => density input ≠ ENNReal.zero)
          (fun _ => ENNReal.one)) := by
        refine Measure.withDensity_congr_ae (positive.mono fun input onSupport => ?_)
        by_cases vanishing : density input = ENNReal.zero
        · rw [ennrealIndicator_of_not_mem (region := fun input => density input ≠ ENNReal.zero)
            (fun nonzero => nonzero vanishing)]
          exact estimate_null_of_density_zero unbiased vanishing
        · rw [ennrealIndicator_of_mem (region := fun input => density input ≠ ENNReal.zero)
            vanishing]
          exact onSupport vanishing
    _ = (reference.restrict fun input => density input ≠ ENNReal.zero).withDensity
          (fun _ => ENNReal.one) := reference.withDensity_indicator _ supportMeasurable
    _ = reference.restrict fun input => density input ≠ ENNReal.zero :=
        Measure.withDensity_one _

/-- When the estimate is almost surely positive wherever the density is, the
paired sampler's draws at the reciprocal weight are a strict reciprocal sampler
for the target. -/
theorem Paired.strictReciprocal {reference target : Measure space} {density : α → ENNReal}
    {estimate : Kernel space weightSpace} {estimateFinite : Kernel.IsSFinite estimate}
    {weighted : Measure (Space.product space weightSpace)}
    (paired : Paired reference target density estimate estimateFinite weighted)
    (probability : Measure.IsProbability target)
    (positive : reference.AE fun input => density input ≠ ENNReal.zero →
      estimate input (fun weight => weight ≠ NNReal.zero) = ENNReal.one) :
    StrictReciprocal reference target
      (weighted.map (fun draw => (draw.1, NNReal.div NNReal.one draw.2))
        (reciprocal_draw_measurable space)) where
  reciprocal := by
    refine ⟨density, paired.unbiased.mean_measurable, paired.isDensity,
      Measure.finite_ae_of_density paired.unbiased.mean_measurable paired.isDensity ?_, ?_⟩
    · rw [probability.univ_eq_one]
      exact True.intro
    · rw [← positive_reference_eq_restrict paired.unbiased positive]
      exact paired.reciprocal probability
  marginal := by
    rw [Measure.map_comp]
    exact paired.marginal

/-! ### Exact densities -/

/-- An exact density, read as a Dirac estimate, pairs with the target's draws
at that density. -/
theorem paired_exact {reference target : Measure space} {density : α → NNReal}
    (measurable : MeasurableMap space weightSpace density)
    (isDensity : Measure.IsDensity target reference
      (fun input => ENNReal.finite (density input))) :
    Paired reference target (fun input => ENNReal.finite (density input))
      (Kernel.deterministic density measurable) (Kernel.IsSFinite.deterministic density measurable)
      (target.map (fun input => (input, density input))
        (Space.pair_measurable (MeasurableMap.identity space) measurable)) where
  isDensity := isDensity
  unbiased := unbiased_deterministic measurable
  joint := by
    rw [isDensity.eq_withDensity]
    refine (Measure.eq_iff_lintegral _ _).mpr fun function functionMeasurable => ?_
    have pairMeasurable : MeasurableMap space (Space.product space weightSpace)
        (fun input => (input, density input)) :=
      Space.pair_measurable (MeasurableMap.identity space) measurable
    rw [lintegral_map _ _ _ functionMeasurable,
      lintegral_withDensity _ (finite_weight_measurable measurable)
        (functionMeasurable.comp pairMeasurable),
      extendedTarget,
      lintegral_withDensity _ (finite_weight_measurable (Space.second_measurable space weightSpace))
        functionMeasurable,
      lintegral_semiproduct _ _ _ (ENNRealMeasurable.mul
        (finite_weight_measurable (Space.second_measurable space weightSpace)) functionMeasurable)]
    apply lintegral_congr
    intro input
    rw [Kernel.deterministic_apply, lintegral_dirac _ _ (ENNRealMeasurable.mul
      (finite_weight_measurable (MeasurableMap.identity weightSpace))
      (functionMeasurable.comp (Kernel.pair_left_measurable input)))]

end

end Problib.Inference
