module

public import Problib.Measure.Integral.Real

set_option autoImplicit false

/-! Bounded integrands under a probability.

A measurable real function bounded above and below by one constant has a finite
signed integral under any probability measure: each nonnegative part lies under
the constant, and the constant integrates to itself. The bound is two-sided and
stated with `neg` rather than an absolute value, so the leaf needs nothing from
analysis.
-/

namespace Problib.Measure

open Problib.Real Problib.Real.Construction.Dedekind Problib.Measure.Real

universe u
variable {α : Type u} {space : Space α}

/-- A measurable integrand between `neg bound` and `bound` has a finite signed
integral under a probability. -/
public theorem hasRealIntegral_of_bounded {measure : Measure space}
    (probability : Measure.IsProbability measure) {integrand : α → Carrier} {bound : Carrier}
    (measurable : MeasurableMap space borel integrand)
    (below : ∀ x, le (neg bound) (integrand x)) (above : ∀ x, le (integrand x) bound) :
    ∃ value, HasRealIntegral measure integrand value := by
  have constantFinite : ENNReal.Finite (lintegral measure (fun _ => ENNReal.ofReal bound)) := by
    rw [lintegral_const, probability.univ_eq_one, ENNReal.mul_one]
    exact ENNReal.ofReal_finite bound
  have positiveFinite : ENNReal.Finite
      (lintegral measure (fun x => ENNReal.ofReal (integrand x))) :=
    ENNReal.finite_of_le (lintegral_mono _ fun x => ENNReal.ofReal_monotone (above x))
      constantFinite
  have negativeFinite : ENNReal.Finite
      (lintegral measure (fun x => ENNReal.ofReal (neg (integrand x)))) := by
    refine ENNReal.finite_of_le (lintegral_mono _ fun x => ?_) constantFinite
    have flipped := neg_le_neg_iff.mpr (below x)
    rw [neg_neg] at flipped
    exact ENNReal.ofReal_monotone flipped
  exact ⟨_, IntegralParts.canonical measurable positiveFinite negativeFinite, rfl⟩

end Problib.Measure
