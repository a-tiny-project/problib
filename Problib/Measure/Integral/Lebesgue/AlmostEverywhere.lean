module

public import Problib.Measure.AlmostEverywhere
public import Problib.Measure.Integral.Lebesgue.Algebra
public import Problib.Measure.Integral.Simple.Integral.Operations

set_option autoImplicit false

namespace Problib.Measure

open Problib.Real

universe u

variable {alpha : Type u} {space : Space alpha} {measure : Measure space}

/-- Lower integrals are monotone under almost-everywhere ordering for arbitrary
nonnegative extended-real integrands without measurability assumptions. -/
public theorem lintegral_mono_ae {left right : alpha → ENNReal}
    (included : measure.AE (fun value => ENNReal.le (left value) (right value))) :
    ENNReal.le (lintegral measure left) (lintegral measure right) := by
  classical
  rcases included.exists_null_exception with
    ⟨exceptional, exceptionalMeasurable, nullExceptional, outsideBound⟩
  let region := Set.complement exceptional
  have regionMeasurable : space.Measurable region :=
    space.complement exceptionalMeasurable
  have sameMeasure : measure.restrict region = measure := by
    apply measure.restrict_eq_self_of_complement_null
    apply nullExceptional.mono
    intro value member
    exact Classical.not_not.mp member
  apply lintegral_le
  intro lower lowerBound
  have sameIntegral : (lower.restrict region regionMeasurable).integral measure =
      lower.integral measure := by
    rw [SimpleFunction.integral_restrict, sameMeasure]
  rw [← sameIntegral]
  apply SimpleFunction.integral_le_lintegral
  intro value
  by_cases outside : region value
  · rw [lower.restrict_apply_of_mem region regionMeasurable value outside]
    exact ENNReal.le_trans (lowerBound value) (outsideBound value outside)
  · rw [lower.restrict_apply_of_not_mem region regionMeasurable value outside]
    exact ENNReal.zero_le _

/-- Lower integrals are congruent under almost-everywhere equality for arbitrary
nonnegative extended-real integrands without measurability assumptions. -/
public theorem lintegral_congr_ae {left right : alpha → ENNReal}
    (equal : measure.AEEq left right) :
    lintegral measure left = lintegral measure right := by
  apply ENNReal.le_antisymm
  · apply lintegral_mono_ae
    exact Measure.AE.mono equal (fun _ equality => by
      rw [equality]
      exact ENNReal.le_refl _)
  · apply lintegral_mono_ae
    exact Measure.AE.mono equal.symm (fun _ equality => by
      rw [equality]
      exact ENNReal.le_refl _)

/-- An almost-everywhere zero integrand has zero lower integral. -/
public theorem lintegral_eq_zero_of_ae_zero {function : alpha → ENNReal}
    (zero : measure.AEEq function (fun _ => ENNReal.zero)) :
    lintegral measure function = ENNReal.zero := by
  rw [lintegral_congr_ae zero, lintegral_zero]

end Problib.Measure
