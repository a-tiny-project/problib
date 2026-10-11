module

public import Problib.Analysis.Enclosure.Exp
public import Problib.Analysis.Arctangent
import Problib.Real.Grind

/-! Certified dyadic enclosures of the integral pi.

The arctangent module identifies pi with four times its unit-interval integral.
It approximates that integral by a finite rational geometric polynomial, with
error at most `2^-count`. Four guard bits put the analytic error below half a
requested grid step. Outward rounding adds at most two more grid steps.
-/

set_option autoImplicit false

namespace Problib.Analysis.Enclosure

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real

/-- The centre of the pi enclosure, with four guard bits. -/
@[expose] public def piApproximation (precision : Nat) : Rat :=
  4 * Arctangent.unitApproximation (precision + 4)

/-- The analytic error before outward rounding. -/
@[expose] public def piError (precision : Nat) : Rat :=
  4 / scale (precision + 4)

public theorem piError_nonnegative (precision : Nat) : 0 ≤ piError precision := by
  exact (le_div_iff_mul_le (scale_positive (precision + 4))).mpr (by grind)

private theorem half_power_scale (count : Nat) : (1 / 2 : Rat) ^ count = 1 / scale count := by
  induction count with
  | zero => rw [Rat.pow_zero, scale_zero]; decide +kernel
  | succ count induction =>
      rw [Rat.pow_succ, induction, scale_succ]
      have positive := scale_positive count
      grind

private theorem pi_bounds (precision : Nat) :
    le (selection.ofRat (piApproximation precision - piError precision)) Problib.Analysis.pi ∧
      le Problib.Analysis.pi (selection.ofRat (piApproximation precision + piError precision)) := by
  have error := Arctangent.unitApproximation_error (precision + 4)
  rw [half_power_scale] at error
  have fourNonnegative : le zero (selection.ofRat 4) := by real_grind
  have scaled := mul_le_mul_nonnegative_left error fourNonnegative
  rw [← abs_of_nonnegative fourNonnegative, ← Problib.Analysis.Real.abs_mul] at scaled
  rw [abs_of_nonnegative fourNonnegative, mul_sub, ← Arctangent.pi_eq_four] at scaled
  have centre : mul (selection.ofRat 4)
      (selection.ofRat (Arctangent.unitApproximation (precision + 4))) =
      selection.ofRat (piApproximation precision) := by
    rw [piApproximation, ofRat_mul]
  have radius : mul (selection.ofRat 4) (selection.ofRat (1 / scale (precision + 4))) =
      selection.ofRat (piError precision) := by
    rw [piError, ofRat_div, ofRat_div, ofRat_one]
    real_grind
  rw [centre, radius] at scaled
  have between := Problib.Analysis.Real.abs_le.mp scaled
  rw [ofRat_sub, ofRat_add]
  constructor <;> real_grind

namespace Interval

/-- Enclose pi on the requested dyadic grid. -/
@[expose] public def pi (precision : Nat) : Interval :=
  (⟨piApproximation precision - piError precision,
    piApproximation precision + piError precision, by
      have nonnegative := piError_nonnegative precision
      grind⟩ : Interval).round precision

/-- The dyadic enclosure contains Problib's real pi. -/
public theorem contains_pi (precision : Nat) : (pi precision).Contains Problib.Analysis.pi := by
  apply Contains.round
  exact pi_bounds precision

/-- The width is at most three requested grid steps. -/
public theorem width_pi_le (precision : Nat) : (pi precision).width ≤ 3 / scale precision := by
  have rounded := width_round_le precision
    (⟨piApproximation precision - piError precision,
      piApproximation precision + piError precision, by
        have nonnegative := piError_nonnegative precision
        grind⟩ : Interval)
  change (pi precision).width ≤ _ at rounded
  have scaleSplit : scale (precision + 4) = scale precision * 16 := by
    rw [scale_add]
    rfl
  simp only [width] at rounded ⊢
  unfold piError at rounded
  rw [scaleSplit] at rounded
  have positive := scale_positive precision
  have radius : (4 : Rat) / (scale precision * 16) = (1 / 4) / scale precision := by
    simp only [Rat.div_def, Rat.inv_mul_rev]
    rw [show (16 : Rat)⁻¹ = 1 / 16 from by decide +kernel]
    grind
  rw [radius] at rounded
  have inverseNonnegative := Rat.le_of_lt (Rat.inv_pos.mpr positive)
  grind

end Interval

/-- The enclosure contains the real pi. -/
public theorem contains_pi (precision : Nat) : (Interval.pi precision).Contains Problib.Analysis.pi :=
  Interval.contains_pi precision

end Problib.Analysis.Enclosure
