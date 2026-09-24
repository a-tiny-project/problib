module

public import Problib.Analysis.Logarithm.Basic
public import Problib.Analysis.Real.Composition

/-! The derivative of the integral logarithm.

The logarithm is the oriented integral of the reciprocal, and on a short
interval the reciprocal lies between its values at the two endpoints. The
increment of the logarithm is therefore squeezed between two reciprocal
rectangles, `interval_bounds`, and its secant between `1 / x` and `1 / (x + d)`.
The second approaches the first, so the secant does too. No fundamental theorem
of calculus is used.
-/

set_option autoImplicit false

namespace Problib.Analysis.Logarithm

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real

noncomputable section

/-- The logarithm's increment over ordered positive endpoints lies between the
two reciprocal rectangles. -/
public theorem log_increment_bounds {lower upper : Carrier} (positive : lt zero lower)
    (ordered : le lower upper) :
    le (div (sub upper lower) upper) (sub (logIntegral upper) (logIntegral lower)) ∧
      le (sub (logIntegral upper) (logIntegral lower)) (div (sub upper lower) lower) := by
  have increment : sub (logIntegral upper) (logIntegral lower) =
      ENNReal.toReal (J lower upper) := by
    rw [log_difference lower upper positive ordered, add_sub_self]
  have gap : le zero (sub upper lower) := by
    have shifted := add_le_add_right_iff (shift := neg lower) |>.mpr ordered
    rwa [add_neg, ← sub_eq_add_neg] at shifted
  have bounds := interval_bounds lower upper positive ordered
  rw [increment]
  exact ⟨(ENNReal.ofReal_le_iff_le_toReal (interval_finite lower upper positive)).mp bounds.left,
    (ENNReal.le_ofReal_iff_toReal_le (interval_finite lower upper positive)
      (div_nonnegative gap (le_of_lt positive))).mp bounds.right⟩

/-- Dividing a quotient's numerator back out leaves the reciprocal. -/
private theorem div_div_self {step : Carrier} (nonzero : step ≠ zero) (other : Carrier) :
    div (div step other) step = inverse other := by
  rw [div_eq_mul_inverse, div_eq_mul_inverse, mul_comm step (inverse other), mul_assoc,
    mul_inverse_cancel nonzero, mul_one]

/-- The logarithm differentiates to the reciprocal at every positive point. -/
public theorem hasDerivative_log {point : Carrier} (positive : lt zero point) :
    HasDerivative logIntegral point (inverse point) := by
  have pointNonzero : point ≠ zero := by
    intro vanished
    rw [vanished] at positive
    exact lt_irrefl zero positive
  have reciprocalApproaches :
      Approaches (fun displacement => inverse (add point displacement)) (inverse point) := by
    have shifted := approaches_add (approaches_const point) approaches_displacement
    rw [add_zero] at shifted
    exact approaches_inverse shifted pointNonzero
  refine approaches_of_closer positive (fun displacement nonzero inside => ?_)
    reciprocalApproaches
  apply abs_sub_le_of_between
  have shiftedPositive : lt zero (add point displacement) := by
    have below := (abs_lt.mp inside).left
    have shifted := add_lt_add_left point below
    rwa [add_neg] at shifted
  rcases lt_or_lt_of_ne nonzero with negative | positiveStep
  · left
    have ordered : le (add point displacement) point := by
      have shifted := add_le_add_left_iff (shift := point) |>.mpr (le_of_lt negative)
      rwa [add_zero] at shifted
    have bounds := log_increment_bounds shiftedPositive ordered
    have width : sub point (add point displacement) = neg displacement := by
      rw [sub_eq_add_neg, neg_add, ← add_assoc, add_neg, add_comm zero, add_zero]
    rw [width] at bounds
    have flipped : lt zero (neg displacement) := neg_positive_iff.mpr negative
    have flippedNonzero : neg displacement ≠ zero := by
      intro vanished
      rw [vanished] at flipped
      exact lt_irrefl zero flipped
    have secantEqual : secant logIntegral point displacement =
        div (sub (logIntegral point) (logIntegral (add point displacement)))
          (neg displacement) := by
      rw [secant, ← neg_sub, div_eq_mul_inverse, div_eq_mul_inverse, inverse_neg, mul_neg, neg_mul]
    rw [secantEqual]
    have lowerBound := div_le_div_right flipped bounds.left
    have upperBound := div_le_div_right flipped bounds.right
    rw [div_div_self flippedNonzero] at lowerBound upperBound
    exact ⟨lowerBound, upperBound⟩
  · right
    have ordered : le point (add point displacement) := by
      have shifted := add_le_add_left_iff (shift := point) |>.mpr (le_of_lt positiveStep)
      rwa [add_zero] at shifted
    have bounds := log_increment_bounds positive ordered
    rw [add_sub_self] at bounds
    have lowerBound := div_le_div_right positiveStep bounds.left
    have upperBound := div_le_div_right positiveStep bounds.right
    rw [div_div_self nonzero] at lowerBound upperBound
    exact ⟨lowerBound, upperBound⟩

end

end Problib.Analysis.Logarithm
