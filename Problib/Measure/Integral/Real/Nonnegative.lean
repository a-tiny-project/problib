module

public import Problib.Measure.Integral.Real

set_option autoImplicit false

/-! A nonnegative measurable integrand with a finite lower integral has that
integral as its certified signed integral. This is the converse of
`HasRealIntegral.lintegral_ofReal`. -/

namespace Problib.Measure

open Problib.Real Problib.Real.Construction.Dedekind Problib.Measure.Real

universe u
variable {α : Type u} {space : Space α}

/-- A nonnegative measurable integrand whose lower integral is a finite
nonnegative real has that real as its signed integral. Its negative part
vanishes, so the canonical decomposition's value is the positive mass. -/
public theorem HasRealIntegral.of_lintegral_ofReal {measure : Measure space}
    {integrand : α → Carrier} {value : Carrier}
    (measurable : MeasurableMap space borel integrand)
    (nonnegative : ∀ x, le zero (integrand x)) (valueNonnegative : le zero value)
    (integral : lintegral measure (fun x => ENNReal.ofReal (integrand x)) = ENNReal.ofReal value) :
    HasRealIntegral measure integrand value := by
  have vanishes : (fun x => ENNReal.ofReal (Construction.Dedekind.neg (integrand x))) = fun _ => ENNReal.zero := by
    funext x
    apply ENNReal.le_antisymm _ (ENNReal.zero_le _)
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.ofReal_monotone (neg_nonpositive_iff.mp (nonnegative x))
  have positiveFinite : ENNReal.Finite
      (lintegral measure (fun x => ENNReal.ofReal (integrand x))) := by
    rw [integral]
    exact ENNReal.ofReal_finite value
  have negativeFinite : ENNReal.Finite
      (lintegral measure (fun x => ENNReal.ofReal (Construction.Dedekind.neg (integrand x)))) := by
    rw [vanishes, lintegral_zero]
    exact True.intro
  let canonical := IntegralParts.canonical measurable positiveFinite negativeFinite
  refine ⟨canonical, ?_⟩
  have negativeMass : canonical.negativeMass = NNReal.zero := by
    have integralZero := canonical.negative_integral
    change lintegral measure (fun x => ENNReal.ofReal (Construction.Dedekind.neg (integrand x))) = _ at integralZero
    rw [vanishes, lintegral_zero] at integralZero
    exact (ENNReal.finite_injective integralZero).symm
  have positiveMass := canonical.positive_integral
  change lintegral measure (fun x => ENNReal.ofReal (integrand x)) = _ at positiveMass
  rw [integral] at positiveMass
  unfold IntegralParts.value
  rw [negativeMass]
  change Construction.Dedekind.sub canonical.positiveMass.toReal zero = value
  rw [sub_eq_add_neg, neg_zero, add_zero]
  have projected := congrArg ENNReal.toReal positiveMass
  rw [ENNReal.toReal_ofReal valueNonnegative] at projected
  exact projected.symm

end Problib.Measure
