import Problib.Inference.Weighting
import Problib.Measure.Normalization
import Problib.Measure.Additive.Algebra

set_option autoImplicit false

namespace Problib.Inference

open Problib.Measure Problib.Real

universe u v

/-- Attach the exact finite mass of a solved block to its conditional draw. -/
noncomputable def blockDraw {α : Type u} {β : Type v}
    {source : Space α} {result : Space β} (sampler : Kernel source result)
    (markov : ∀ input, Measure.IsProbability (sampler input))
    (mass : α → NNReal) (massMeasurable : MeasurableMap source weightSpace mass) :
    Kernel source (Space.product result weightSpace) :=
  (sampler.attach (Kernel.IsSFinite.ofMarkov markov)).map
    (fun point => (point.2, mass point.1))
    (Space.pair_measurable (Space.second_measurable source result)
      (MeasurableMap.comp massMeasurable (Space.first_measurable source result)))

theorem blockDraw_apply {α : Type u} {β : Type v}
    {source : Space α} {result : Space β} (sampler : Kernel source result)
    (markov : ∀ input, Measure.IsProbability (sampler input))
    (mass : α → NNReal) (massMeasurable : MeasurableMap source weightSpace mass) (input : α) :
    blockDraw sampler markov mass massMeasurable input =
      (sampler input).map (fun value => (value, mass input))
        (Space.pair_measurable (MeasurableMap.identity result)
          (MeasurableMap.constant result weightSpace (mass input))) := by
  rw [blockDraw, Kernel.map_apply, Kernel.attach_apply, Measure.map_comp]
  exact Space.pair_measurable (Space.second_measurable source result)
    (MeasurableMap.comp massMeasurable (Space.first_measurable source result))

/-- A normalized draw at its original mass is properly weighted. At zero mass
any probability fallback is sound, since its returned weight is zero. The input
laws describe only the local mass and conditional sampler. -/
theorem normalized_properlyWeighted {β : Type v} {result : Space β}
    {target sampler : Measure result} (probability : Measure.IsProbability sampler)
    (mass : NNReal) (total : target Set.univ = ENNReal.finite mass)
    (conditional : ∀ nonzero : mass ≠ NNReal.zero,
      sampler = Measure.normalize target (Measure.IsNormalizable.of_finite_mass total nonzero)) :
    ProperlyWeighted target (sampler.map (fun value => (value, mass))
      (Space.pair_measurable (MeasurableMap.identity result)
        (MeasurableMap.constant result weightSpace mass))) := by
  have reconstruct : Measure.smul (ENNReal.finite mass) sampler = target := by
    by_cases zero : mass = NNReal.zero
    · have targetZero := (Measure.eq_zero_iff_univ_eq_zero target).mpr
        (total.trans (congrArg ENNReal.finite zero))
      rw [zero, targetZero]
      exact Measure.zero_smul sampler
    · rw [conditional zero, ← total]
      exact Measure.smul_normalize _ _
  refine properlyWeighted_iff_lintegral.mpr ⟨probability.map _ _, fun function measurable => ?_⟩
  rw [lintegral_map _ _ _ (weighted_integrand_measurable measurable), ← reconstruct,
    lintegral_smul_measure]
  exact lintegral_smul sampler (ENNReal.finite mass) measurable

/-- The local construction is valid at every context, including null fibers. -/
theorem blockDraw_properlyWeighted {α : Type u} {β : Type v}
    {source : Space α} {result : Space β} (target sampler : Kernel source result)
    (markov : ∀ input, Measure.IsProbability (sampler input))
    (mass : α → NNReal) (massMeasurable : MeasurableMap source weightSpace mass)
    (total : ∀ input, target input Set.univ = ENNReal.finite (mass input))
    (conditional : ∀ input, ∀ nonzero : mass input ≠ NNReal.zero,
      sampler input = Measure.normalize (target input)
        (Measure.IsNormalizable.of_finite_mass (total input) nonzero)) (input : α) :
    ProperlyWeighted (target input) (blockDraw sampler markov mass massMeasurable input) := by
  rw [blockDraw_apply]
  exact normalized_properlyWeighted (markov input) (mass input) (total input) (conditional input)

/-- Exact finite blocks compose under an arbitrary outer properly weighted law.
The outer correction and the block normalizer multiply through `reweight`. No
positivity premise is imposed on null fibers or on the outer target. -/
theorem blockDraw_bind {α : Type u} {β : Type v}
    {source : Space α} {result : Space β} (target sampler : Kernel source result)
    (markov : ∀ input, Measure.IsProbability (sampler input))
    (mass : α → NNReal) (massMeasurable : MeasurableMap source weightSpace mass)
    (total : ∀ input, target input Set.univ = ENNReal.finite (mass input))
    (conditional : ∀ input, ∀ nonzero : mass input ≠ NNReal.zero,
      sampler input = Measure.normalize (target input)
        (Measure.IsNormalizable.of_finite_mass (total input) nonzero))
    {outer : Measure source} {weighted : Measure (Space.product source weightSpace)}
    (properlyWeighted : ProperlyWeighted outer weighted) :
    ProperlyWeighted (outer.bind target)
      (weighted.bind (reweight (blockDraw sampler markov mass massMeasurable)
        (Kernel.IsSFinite.ofMarkov fun input =>
          (blockDraw_properlyWeighted target sampler markov mass massMeasurable total conditional input).probability))) := by
  have localLaw := blockDraw_properlyWeighted target sampler markov mass massMeasurable total conditional
  have same : barycenterKernel (blockDraw sampler markov mass massMeasurable) = target :=
    Kernel.ext fun input => (localLaw input).change
  have composed := weighted_bind (fun input => (localLaw input).probability)
    (Kernel.IsSFinite.ofMarkov fun input => (localLaw input).probability) properlyWeighted
  rw [same] at composed
  exact composed

end Problib.Inference
