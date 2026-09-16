module

public import Foundations.Measure.Integral.Lebesgue.AlmostEverywhere
public import Foundations.Measure.Integral.Lebesgue.Markov
public import Foundations.Real.Series.Basis

set_option autoImplicit false

namespace Foundations.Measure

open Foundations.Real

universe u

variable {alpha : Type u} {space : Space alpha} {measure : Measure space}

/-- Any strictly positive upper-level set of a measurable function with zero
lower integral is null. -/
public theorem null_upperLevel_of_lintegral_eq_zero {function : alpha → ENNReal}
    (measurable : ENNRealMeasurable space function)
    {threshold : ENNReal} (nonzero : threshold ≠ ENNReal.zero)
    (integralZero : lintegral measure function = ENNReal.zero) :
    measure.NullSet (upperLevel function threshold) := by
  have bound := markov measure measurable threshold
  rw [integralZero] at bound
  rcases ENNReal.mulEqZeroIff.mp (ENNReal.eqZeroOfLeZero bound) with
    thresholdZero | measureZero
  · exact False.elim (nonzero thresholdZero)
  · exact measureZero

/-- A measurable function with zero lower integral vanishes almost everywhere. -/
public theorem ae_zero_of_lintegral_eq_zero {function : alpha → ENNReal}
    (measurable : ENNRealMeasurable space function)
    (integralZero : lintegral measure function = ENNReal.zero) :
    measure.AEEq function (fun _ => ENNReal.zero) := by
  classical
  let events : Nat → Set alpha := fun index value =>
    ENNReal.lt ENNReal.zero (ENNReal.rationalBasis index) ∧
      ENNReal.le (ENNReal.rationalBasis index) (function value)
  have nullEvents : ∀ index, measure.NullSet (events index) := by
    intro index
    by_cases positive : ENNReal.lt ENNReal.zero (ENNReal.rationalBasis index)
    · exact (null_upperLevel_of_lintegral_eq_zero measurable
        (ENNReal.zeroLtIffNeZero.mp positive) integralZero).mono
        (fun {_} member => member.2)
    · apply measure.null_empty.mono
      intro value member
      exact positive member.1
  apply (Measure.NullSet.iUnion nullEvents).mono
  intro value nonzero
  rcases ENNReal.existsRationalBasisBetween
    (ENNReal.zeroLtIffNeZero.mpr nonzero) with ⟨index, positive, below⟩
  exact ⟨index, positive, below.1⟩

/-- For measurable integrands, the lower Lebesgue integral vanishes if and only
if the function vanishes almost everywhere. -/
public theorem lintegral_eq_zero_iff {function : alpha → ENNReal}
    (measurable : ENNRealMeasurable space function) :
    lintegral measure function = ENNReal.zero ↔
      measure.AEEq function (fun _ => ENNReal.zero) :=
  ⟨ae_zero_of_lintegral_eq_zero measurable, lintegral_eq_zero_of_ae_zero⟩

end Foundations.Measure
