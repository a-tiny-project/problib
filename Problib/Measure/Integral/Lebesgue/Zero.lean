module

public import Problib.Measure.Integral.Lebesgue.AlmostEverywhere
public import Problib.Measure.Integral.Lebesgue.Markov
public import Problib.Real.Series.Basis

set_option autoImplicit false

namespace Problib.Measure

open Problib.Real

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
  rcases ENNReal.mul_eq_zero_iff.mp (ENNReal.eq_zero_of_le_zero bound) with
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
        (ENNReal.zero_lt_iff_ne_zero.mp positive) integralZero).mono
        (fun {_} member => member.2)
    · apply measure.null_empty.mono
      intro value member
      exact positive member.1
  apply (Measure.NullSet.iUnion nullEvents).mono
  intro value nonzero
  rcases ENNReal.exists_rationalBasis_between
    (ENNReal.zero_lt_iff_ne_zero.mpr nonzero) with ⟨index, positive, below⟩
  exact ⟨index, positive, below.1⟩

/-- For measurable integrands, the lower Lebesgue integral vanishes if and only
if the function vanishes almost everywhere. -/
public theorem lintegral_eq_zero_iff {function : alpha → ENNReal}
    (measurable : ENNRealMeasurable space function) :
    lintegral measure function = ENNReal.zero ↔
      measure.AEEq function (fun _ => ENNReal.zero) :=
  ⟨ae_zero_of_lintegral_eq_zero measurable, lintegral_eq_zero_of_ae_zero⟩

/-- A function at least `bound` on a measurable region integrates to at least
`bound` times the region's measure. -/
public theorem lintegral_lower_on (measure : Measure space) {region : Set alpha}
    (measurable : space.Measurable region) {function : alpha → ENNReal} {bound : ENNReal}
    (lower : ∀ value, region value → ENNReal.le bound (function value)) :
    ENNReal.le (ENNReal.mul bound (measure region)) (lintegral measure function) := by
  have pointwise : ∀ value, ENNReal.le
      (ennrealIndicator region (fun _ => bound) value) (function value) := by
    intro value
    by_cases member : region value
    · rw [ennrealIndicator_of_mem member]
      exact lower value member
    · rw [ennrealIndicator_of_not_mem member]
      exact ENNReal.zero_le _
  have integral := lintegral_mono measure pointwise
  rw [lintegral_indicator measure region measurable, lintegral_const,
    Measure.restrict_apply_univ] at integral
  exact integral

/-- A measurable function with zero integral is positive only on a null set. -/
public theorem positive_null_of_lintegral_zero (measure : Measure space)
    {function : alpha → ENNReal} (measurable : ENNRealMeasurable space function)
    (vanished : lintegral measure function = ENNReal.zero) :
    measure.NullSet (fun input => ENNReal.lt ENNReal.zero (function input)) :=
  Measure.NullSet.mono ((lintegral_eq_zero_iff measurable).mp vanished)
    (fun {_} positive equal => (ENNReal.zero_lt_iff_ne_zero.mp positive) equal)

/-- A measurable function positive on a charged region has a positive
integral. -/
public theorem lintegral_positive (measure : Measure space) {region : Set alpha}
    (charged : ENNReal.lt ENNReal.zero (measure region))
    {function : alpha → ENNReal} (measurable : ENNRealMeasurable space function)
    (positive : ∀ value, region value → ENNReal.lt ENNReal.zero (function value)) :
    ENNReal.lt ENNReal.zero (lintegral measure function) := by
  apply ENNReal.zero_lt_iff_ne_zero.mpr
  intro vanished
  have null : measure.NullSet region :=
    (positive_null_of_lintegral_zero measure measurable vanished).mono
      (fun {value} member => positive value member)
  exact (ENNReal.zero_lt_iff_ne_zero.mp charged) null

/-- A function whose integral is positive is positive on a charged set. -/
public theorem charged_of_lintegral_positive (measure : Measure space)
    {function : alpha → ENNReal}
    (positive : ENNReal.lt ENNReal.zero (lintegral measure function)) :
    ENNReal.lt ENNReal.zero
      (measure (fun input => ENNReal.lt ENNReal.zero (function input))) := by
  apply ENNReal.zero_lt_iff_ne_zero.mpr
  intro null
  apply ENNReal.zero_lt_iff_ne_zero.mp positive
  apply lintegral_eq_zero_of_ae_zero
  apply Measure.NullSet.mono null
  intro input nonzero
  exact ENNReal.zero_lt_iff_ne_zero.mpr nonzero

end Problib.Measure
