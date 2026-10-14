module

public import Problib.Inference.Weighting
public import Problib.Measure.Additive.Dirac
public import Problib.Measure.Integral.Density.Algebra
public import Problib.Measure.Integral.Lebesgue.Transport
public import Problib.Measure.Kernel.Product.Basic
public import Problib.Measure.Real.Arithmetic
set_option autoImplicit false

/-! Exact estimates and reciprocal weights.

Two relaxations of an exact density compose where the density does not. An
unbiased estimate is read at a point the caller supplies, and its mean there is
the density. A reciprocal weight is read at a sampler's own draw, and it
divides by the density there. This file states the measure-level laws that
carry exact answers into both.

- An exact value is an unbiased estimate of itself: its Dirac law has the
  value as its mean (`unbiased_deterministic`). A joint estimate over
  parameters and points is unbiased at each parameter's section
  (`UnbiasedEstimate.section`).
- Reweighting a density's measure by the density's reciprocal, read as zero
  where the density vanishes, restricts the base measure to the density's
  support (`withDensity_reciprocal`). So weights properly weighted for
  `ν.withDensity q` and multiplied by `1/q` at the draw are properly weighted
  for `ν` restricted to `{q ≠ 0}` (`properlyWeighted_weighted_reciprocal`), and
  an exact draw from `q`'s law at weight `1/q` is one such sampler
  (`properlyWeighted_reciprocal_of_exact`).
- A reciprocal weight asks the density to be finite at almost every point of
  the reference. A density read from finite code is finite everywhere
  (`finite_ae_of_code`), and a measurable density of a finite measure is
  finite almost everywhere (`Measure.finite_ae_of_density`).
- A reciprocal sampler leaves the law of its drawn point free
  (`ReciprocallyWeighted`). A strict one also draws its point from the target
  (`StrictReciprocal`), so the target is a probability
  (`StrictReciprocal.probability`). An exact draw at `1/q` is strict
  (`strictReciprocal_of_exact`). Reweighting by `1/q` keeps the law of the
  drawn point (`map_first_reweight`), so it is strict only when its input
  already draws from the target (`strictReciprocal_weighted_reciprocal`). -/

namespace Problib.Inference

open Problib.Real Problib.Measure

universe u v

variable {α : Type u} {β : Type v}

public section

/-! ### Measurable reciprocals -/

/-- The reciprocal of a measurable weight, read as zero at zero, is
measurable: its extended value is `ofReal` of the real quotient. -/
theorem weight_inverse_measurable {space : Space α} {density : α → NNReal}
    (measurable : MeasurableMap space weightSpace density) :
    MeasurableMap space weightSpace (fun input => NNReal.div NNReal.one (density input)) := by
  refine weight_measurable_of_finite ?_
  have equal : (fun input => ENNReal.finite (NNReal.div NNReal.one (density input))) =
      fun input => ENNReal.ofReal (Construction.Dedekind.div
        (NNReal.toReal NNReal.one) (NNReal.toReal (density input))) := by
    funext input
    exact congrArg ENNReal.finite (NNReal.ofReal_of_nonnegative _).symm
  rw [equal]
  exact Real.ofReal_measurable.comp (Real.measurable_div
    (MeasurableMap.constant space Real.borel (NNReal.toReal NNReal.one))
    (MeasurableMap.comp weight_toReal_measurable measurable))

/-- The support of a measurable weight is a measurable set. -/
theorem weight_support_measurable {space : Space α} {density : α → NNReal}
    (measurable : MeasurableMap space weightSpace density) :
    space.Measurable (fun input => density input ≠ NNReal.zero) := by
  have vanishing := ENNRealMeasurable.eq_set (finite_weight_measurable measurable)
    (ENNRealMeasurable.constant space ENNReal.zero)
  have equal : (fun input => density input ≠ NNReal.zero) =
      Set.complement (fun input => ENNReal.finite (density input) = ENNReal.zero) := by
    apply Set.ext
    intro input
    exact ⟨fun nonzero equal => nonzero (ENNReal.finite_injective equal),
      fun nonzero equal => nonzero (congrArg ENNReal.finite equal)⟩
  rw [equal]
  exact space.complement vanishing

/-! ### Exact estimates -/

/-- A Dirac kernel at a measurable finite value is an unbiased estimate of
that value. -/
theorem unbiased_deterministic {space : Space α} {value : α → NNReal}
    (measurable : MeasurableMap space weightSpace value) :
    UnbiasedEstimate (fun input => ENNReal.finite (value input))
      (Kernel.deterministic value measurable) where
  probability := fun input => Measure.IsProbability.dirac weightSpace (value input)
  mean_eq := fun input => lintegral_dirac weightSpace (value input)
    (finite_weight_measurable (MeasurableMap.identity weightSpace))

/-- Each parameter's section of an unbiased joint kernel over parameters and
points is an unbiased estimate of the mean's section. -/
theorem UnbiasedEstimate.section {source : Space α} {target : Space β}
    {mean : α × β → ENNReal} {estimate : Kernel (Space.product source target) weightSpace}
    (unbiased : UnbiasedEstimate mean estimate) (parameter : α) :
    UnbiasedEstimate (fun point => mean (parameter, point))
      (estimate.precomp (fun point => (parameter, point))
        (Kernel.pair_left_measurable parameter)) where
  probability := fun point => unbiased.probability (parameter, point)
  mean_eq := fun point => unbiased.mean_eq (parameter, point)

/-! ### Reciprocal weights -/

/-- Reweighting a density's measure by the density's reciprocal, read as zero
at zero, restricts the base to where the density is positive. -/
theorem withDensity_reciprocal {space : Space α} (base : Measure space)
    {density : α → NNReal} (measurable : MeasurableMap space weightSpace density) :
    (base.withDensity fun input => ENNReal.finite (density input)).withDensity
        (fun input => ENNReal.finite (NNReal.div NNReal.one (density input))) =
      base.restrict fun input => density input ≠ NNReal.zero := by
  rw [Measure.withDensity_withDensity base (finite_weight_measurable measurable)
    (finite_weight_measurable (weight_inverse_measurable measurable))]
  have product : (fun input => ENNReal.mul (ENNReal.finite (density input))
      (ENNReal.finite (NNReal.div NNReal.one (density input)))) =
      ennrealIndicator (fun input => density input ≠ NNReal.zero)
        (fun _ => ENNReal.one) := by
    funext input
    by_cases vanishing : density input = NNReal.zero
    · rw [ennrealIndicator_of_not_mem (fun nonzero => nonzero vanishing), vanishing]
      exact ENNReal.zero_mul _
    · rw [ennrealIndicator_of_mem (region := fun input => density input ≠ NNReal.zero)
        vanishing, ENNReal.finite_mul_finite,
        NNReal.mul_div_cancel NNReal.one vanishing]
      rfl
  rw [product, base.withDensity_indicator _ (weight_support_measurable measurable),
    Measure.withDensity_one]

/-- A probability drawn at weight one is properly weighted for itself. -/
theorem properlyWeighted_unitWeight {space : Space α} {measure : Measure space}
    (probability : Measure.IsProbability measure) :
    ProperlyWeighted measure (measure.map (fun input => (input, NNReal.one))
      (unit_weight_measurable space)) := by
  refine properlyWeighted_iff_lintegral.mpr ⟨probability.map _ _, fun function measurable => ?_⟩
  rw [lintegral_map _ _ _ (weighted_integrand_measurable measurable)]
  apply lintegral_congr
  intro input
  exact ENNReal.one_mul (function input)

/-- Weights properly weighted for a target with density `q` against a reference,
multiplied by `1/q` at the draw, are properly weighted for the reference
restricted to `{q ≠ 0}`. -/
theorem properlyWeighted_weighted_reciprocal {space : Space α} {target reference : Measure space}
    {weighted : Measure (Space.product space weightSpace)} {density : α → NNReal}
    (measurable : MeasurableMap space weightSpace density)
    (isDensity : Measure.IsDensity target reference
      (fun input => ENNReal.finite (density input)))
    (properlyWeighted : ProperlyWeighted target weighted) :
    ProperlyWeighted (reference.restrict fun input => density input ≠ NNReal.zero)
      (weighted.map
        (fun draw => (draw.1, NNReal.mul draw.2 (NNReal.div NNReal.one (density draw.1))))
        (density_weight_measurable (weight_inverse_measurable measurable))) := by
  rw [← withDensity_reciprocal reference measurable, ← isDensity.eq_withDensity]
  exact weighted_density (weight_inverse_measurable measurable) properlyWeighted

/-- An exact draw from a probability with density `q` against a reference,
paired with `1/q`, is properly weighted for the reference restricted to
`{q ≠ 0}`. -/
theorem properlyWeighted_reciprocal_of_exact {space : Space α} {law reference : Measure space}
    (probability : Measure.IsProbability law) {density : α → NNReal}
    (measurable : MeasurableMap space weightSpace density)
    (isDensity : Measure.IsDensity law reference
      (fun input => ENNReal.finite (density input))) :
    ProperlyWeighted (reference.restrict fun input => density input ≠ NNReal.zero)
      (law.map (fun input => (input, NNReal.div NNReal.one (density input)))
        (Space.pair_measurable (MeasurableMap.identity space)
          (weight_inverse_measurable measurable))) := by
  have mapCongr : ∀ {left right : α → α × NNReal}
      (leftMeasurable : MeasurableMap space (Space.product space weightSpace) left)
      (rightMeasurable : MeasurableMap space (Space.product space weightSpace) right),
      left = right → law.map left leftMeasurable = law.map right rightMeasurable := by
    intro left right leftMeasurable rightMeasurable same
    subst same
    rfl
  have composed : law.map (fun input => (input, NNReal.div NNReal.one (density input)))
      (Space.pair_measurable (MeasurableMap.identity space)
        (weight_inverse_measurable measurable)) =
      (law.map (fun input => (input, NNReal.one)) (unit_weight_measurable space)).map
        (fun draw => (draw.1, NNReal.mul draw.2 (NNReal.div NNReal.one (density draw.1))))
        (density_weight_measurable (weight_inverse_measurable measurable)) := by
    rw [Measure.map_comp]
    exact mapCongr _ _
      (funext fun input => (congrArg (Prod.mk input) (NNReal.one_mul _)).symm)
  rw [composed]
  exact properlyWeighted_weighted_reciprocal measurable isDensity (properlyWeighted_unitWeight probability)

/-- A density read from finite code is finite at every point, so it is finite
at almost every point of any reference. -/
theorem finite_ae_of_code {space : Space α} (reference : Measure space) (value : α → NNReal) :
    reference.AE (fun point => ENNReal.finite (value point) ≠ ENNReal.top) :=
  Measure.ae_of_forall fun point => ENNReal.finite_ne_top (value point)

/-! ### Strict reciprocal samplers -/

/-- Weighted draws that reciprocally weigh a target against a reference: some
measurable density of the target, finite at almost every point of the
reference, has a support on which the draws are properly weighted for the
reference. The law of the drawn point is free. -/
@[expose] def ReciprocallyWeighted {space : Space α} (reference target : Measure space)
    (weighted : Measure (Space.product space weightSpace)) : Prop :=
  ∃ density : α → ENNReal, ENNRealMeasurable space density ∧
    Measure.IsDensity target reference density ∧
    reference.AE (fun point => density point ≠ ENNReal.top) ∧
    ProperlyWeighted (reference.restrict fun point => density point ≠ ENNReal.zero) weighted

/-- A reciprocal sampler whose drawn point follows the target. -/
structure StrictReciprocal {space : Space α} (reference target : Measure space)
    (weighted : Measure (Space.product space weightSpace)) : Prop where
  reciprocal : ReciprocallyWeighted reference target weighted
  marginal : weighted.map Prod.fst (Space.first_measurable space weightSpace) = target

/-- The target of a strict reciprocal sampler is a probability: it is the law
of the drawn point. -/
theorem StrictReciprocal.probability {space : Space α} {reference target : Measure space}
    {weighted : Measure (Space.product space weightSpace)}
    (strict : StrictReciprocal reference target weighted) : Measure.IsProbability target := by
  obtain ⟨_, _, _, _, properlyWeighted⟩ := strict.reciprocal
  rw [← strict.marginal]
  exact properlyWeighted.probability.map _ _

/-- A finite density's support, read in the extended weights, is its support. -/
theorem finite_support (density : α → NNReal) :
    (fun input => ENNReal.finite (density input) ≠ ENNReal.zero) =
      fun input => density input ≠ NNReal.zero := by
  funext input
  exact propext ⟨fun nonzero vanishing => nonzero (congrArg ENNReal.finite vanishing),
    fun nonzero equal => nonzero (ENNReal.finite_injective equal)⟩

/-- Draws properly weighted on the support of a measurable finite density of
the target reciprocally weigh the target. -/
theorem reciprocallyWeighted_of_finite {space : Space α} {reference target : Measure space}
    {weighted : Measure (Space.product space weightSpace)} {density : α → NNReal}
    (measurable : MeasurableMap space weightSpace density)
    (isDensity : Measure.IsDensity target reference
      (fun input => ENNReal.finite (density input)))
    (properlyWeighted : ProperlyWeighted
      (reference.restrict fun input => density input ≠ NNReal.zero) weighted) :
    ReciprocallyWeighted reference target weighted := by
  refine ⟨fun input => ENNReal.finite (density input), finite_weight_measurable measurable,
    isDensity, finite_ae_of_code reference density, ?_⟩
  rw [finite_support]
  exact properlyWeighted

/-- Multiplying each weight by a factor at its draw keeps the law of the drawn
point. -/
theorem map_first_reweight {space : Space α}
    (weighted : Measure (Space.product space weightSpace)) {factor : α → NNReal}
    (measurable : MeasurableMap space weightSpace factor) :
    (weighted.map (fun draw => (draw.1, NNReal.mul draw.2 (factor draw.1)))
        (density_weight_measurable measurable)).map Prod.fst
        (Space.first_measurable space weightSpace) =
      weighted.map Prod.fst (Space.first_measurable space weightSpace) := by
  rw [Measure.map_comp]

/-- Weights properly weighted for a target with density `q`, multiplied by
`1/q` at the draw, are a strict reciprocal sampler when the draws already
follow the target. Proper weighting alone does not give that law. -/
theorem strictReciprocal_weighted_reciprocal {space : Space α}
    {target reference : Measure space} {weighted : Measure (Space.product space weightSpace)}
    {density : α → NNReal} (measurable : MeasurableMap space weightSpace density)
    (isDensity : Measure.IsDensity target reference
      (fun input => ENNReal.finite (density input)))
    (properlyWeighted : ProperlyWeighted target weighted)
    (marginal : weighted.map Prod.fst (Space.first_measurable space weightSpace) = target) :
    StrictReciprocal reference target
      (weighted.map
        (fun draw => (draw.1, NNReal.mul draw.2 (NNReal.div NNReal.one (density draw.1))))
        (density_weight_measurable (weight_inverse_measurable measurable))) where
  reciprocal := reciprocallyWeighted_of_finite measurable isDensity
    (properlyWeighted_weighted_reciprocal measurable isDensity properlyWeighted)
  marginal := (map_first_reweight weighted (weight_inverse_measurable measurable)).trans marginal

/-- An exact draw from a probability with density `q` against a reference,
paired with `1/q`, is a strict reciprocal sampler. -/
theorem strictReciprocal_of_exact {space : Space α} {law reference : Measure space}
    (probability : Measure.IsProbability law) {density : α → NNReal}
    (measurable : MeasurableMap space weightSpace density)
    (isDensity : Measure.IsDensity law reference
      (fun input => ENNReal.finite (density input))) :
    StrictReciprocal reference law
      (law.map (fun input => (input, NNReal.div NNReal.one (density input)))
        (Space.pair_measurable (MeasurableMap.identity space)
          (weight_inverse_measurable measurable))) where
  reciprocal := reciprocallyWeighted_of_finite measurable isDensity
    (properlyWeighted_reciprocal_of_exact probability measurable isDensity)
  marginal := by
    rw [Measure.map_comp]
    exact law.map_id

end

end Problib.Inference
