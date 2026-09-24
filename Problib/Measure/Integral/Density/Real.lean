module

public import Problib.Measure.Integral.Density.Change
public import Problib.Measure.Integral.Real

/-! Certified real integrals against a density.

A finite signed integral against `measure.withDensity density` is the same
integral against `measure` of the integrand weighted by the density. Both
nonnegative parts are weighted pointwise, and the change of variables for lower
integrals keeps each part's evaluated mass, so the value does not move.
-/

set_option autoImplicit false

namespace Problib.Measure

open Problib.Real Problib.Real.Construction.Dedekind Problib.Measure.Real

universe u
variable {α : Type u} {space : Space α}

/-- Weight a certified decomposition against a density measure by the density. -/
@[expose] public noncomputable def IntegralParts.ofWithDensity {measure : Measure space}
    {density : α → NNReal}
    (densityMeasurable : ENNRealMeasurable space (fun x => ENNReal.finite (density x)))
    {integrand : α → Carrier}
    (parts : IntegralParts (measure.withDensity (fun x => ENNReal.finite (density x)))
      integrand) :
    IntegralParts measure (fun x => mul (integrand x) (density x).toReal) where
  positive := fun x => NNReal.mul (parts.positive x) (density x)
  negative := fun x => NNReal.mul (parts.negative x) (density x)
  positive_measurable := by
    simp only [← ENNReal.finite_mul_finite]
    exact parts.positive_measurable.mul densityMeasurable
  negative_measurable := by
    simp only [← ENNReal.finite_mul_finite]
    exact parts.negative_measurable.mul densityMeasurable
  decomposition := fun x => by
    rw [parts.decomposition x, NNReal.toReal_mul, NNReal.toReal_mul, sub_eq_add_neg, sub_eq_add_neg]
    exact (multiplicativeSelection.ring.add_mul _ _ _).trans
      (congrArg (add _) (multiplicativeSelection.ring.neg_mul _ _))
  positiveMass := parts.positiveMass
  negativeMass := parts.negativeMass
  positive_integral := by
    rw [← parts.positive_integral,
      lintegral_withDensity measure densityMeasurable parts.positive_measurable]
    apply lintegral_congr
    intro x
    rw [ENNReal.finite_mul_finite, NNReal.mul_comm]
  negative_integral := by
    rw [← parts.negative_integral,
      lintegral_withDensity measure densityMeasurable parts.negative_measurable]
    apply lintegral_congr
    intro x
    rw [ENNReal.finite_mul_finite, NNReal.mul_comm]

/-- A certified integral against a density measure is the certified integral of
the density-weighted integrand against the base measure, at the same value. -/
public theorem HasRealIntegral.of_withDensity {measure : Measure space}
    {density : α → NNReal}
    (densityMeasurable : ENNRealMeasurable space (fun x => ENNReal.finite (density x)))
    {integrand : α → Carrier} {value : Carrier}
    (integral : HasRealIntegral (measure.withDensity (fun x => ENNReal.finite (density x)))
      integrand value) :
    HasRealIntegral measure (fun x => mul (integrand x) (density x).toReal) value := by
  obtain ⟨parts, same⟩ := integral
  exact ⟨parts.ofWithDensity densityMeasurable, same⟩

end Problib.Measure
