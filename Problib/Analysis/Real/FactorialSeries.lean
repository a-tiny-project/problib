module

public import Problib.Analysis.Real.RatioTest

/-! Convergence of the factorial power series for every sealed real argument. -/

set_option autoImplicit false

open scoped Problib.Real.AC

namespace Problib.Analysis.Real.SignedSeries

open Problib.Real.Construction.Dedekind

noncomputable section

/-- The coefficients `radius^n / n!`, given by their one-step recurrence. -/
@[expose] public def factorialTerm (radius : selection.Carrier) :
    Nat → selection.Carrier
  | 0 => one
  | count + 1 =>
      div (mul radius (factorialTerm radius count))
        (selection.ofRat ((count + 1 : Nat) : Rat))

public theorem factorialTerm_zero (radius : selection.Carrier) :
    factorialTerm radius 0 = one := rfl

public theorem factorialTerm_succ (radius : selection.Carrier) (count : Nat) :
    factorialTerm radius (count + 1) =
      div (mul radius (factorialTerm radius count))
        (selection.ofRat ((count + 1 : Nat) : Rat)) := rfl

/-- After a natural number exceeds the argument magnitude, each coefficient
shrinks by a fixed ratio below one. -/
public theorem factorial_summable (radius : selection.Carrier) :
    Summable (factorialTerm radius) := by
  rcases exists_nat_strict_upper (abs radius) with ⟨start, magnitudeBelow⟩
  have startPositive : 0 < start := by
    cases start with
    | zero =>
        change lt (abs radius) (selection.ofRat (0 : Rat)) at magnitudeBelow
        rw [ofRat_zero] at magnitudeBelow
        exact False.elim (magnitudeBelow.right (abs_nonnegative radius))
    | succ count => exact Nat.succ_pos count
  have denominatorPositive :
      lt zero (selection.ofRat (start : Rat)) := by
    have embedded := (ofRat_lt_iff 0 (start : Rat)).mpr
      (Rat.natCast_pos.mpr startPositive)
    rwa [ofRat_zero] at embedded
  have denominatorNonzero : selection.ofRat (start : Rat) ≠ zero := by
    intro vanished
    have copy := denominatorPositive
    rw [vanished] at copy
    exact lt_irrefl zero copy
  let ratio := div (abs radius) (selection.ofRat (start : Rat))
  have ratioNonnegative : le zero ratio :=
    div_nonnegative (abs_nonnegative radius) denominatorPositive.left
  have ratioBelowOne : lt ratio one := by
    have scaled := mul_lt_mul_positive_right magnitudeBelow
      (inverse_of_positive_positive denominatorPositive)
    rw [mul_inverse_cancel denominatorNonzero] at scaled
    exact scaled
  apply summable_of_ratio ratioNonnegative ratioBelowOne start
  intro index later
  let denominator := selection.ofRat ((index + 1 : Nat) : Rat)
  have denominatorPositiveAt : lt zero denominator :=
    ofRat_succ_positive index
  have denominatorOrder : le (selection.ofRat (start : Rat)) denominator := by
    apply (ofRat_le_iff _ _).mpr
    exact Rat.natCast_le_natCast.mpr (Nat.le_succ_of_le later)
  have ratioBound := div_le_div_of_positive (abs_nonnegative radius)
    denominatorPositive denominatorOrder
  have scaled := mul_le_mul_nonnegative_right ratioBound
    (abs_nonnegative (factorialTerm radius index))
  rw [factorialTerm_succ, abs_div, abs_mul,
    abs_of_nonnegative denominatorPositiveAt.left]
  have associate : div (mul (abs radius) (abs (factorialTerm radius index)))
      denominator =
      mul (div (abs radius) denominator)
        (abs (factorialTerm radius index)) := by
    rw [div_eq_mul_inverse, div_eq_mul_inverse]
    rw [mul_assoc, mul_comm (abs (factorialTerm radius index))
      (inverse denominator), ← mul_assoc]
  rw [associate]
  exact scaled

/-- The coefficient `radius^n / n!` is the reciprocal factorial `1/n!` times the
power `radius^n`. -/
public theorem factorialTerm_factor (radius : selection.Carrier) (count : Nat) :
    factorialTerm radius count = mul (factorialTerm one count) (power radius count) := by
  induction count with
  | zero => rw [factorialTerm_zero, factorialTerm_zero, power_zero, mul_one]
  | succ count induction =>
      rw [factorialTerm_succ radius, factorialTerm_succ one, power_succ, induction, one_mul,
        div_eq_mul_inverse, div_eq_mul_inverse]
      ac_rfl

/-- The reciprocal factorials `1/n!` are positive. -/
public theorem factorialTerm_one_positive (count : Nat) :
    lt zero (factorialTerm one count) := by
  induction count with
  | zero => exact one_positive
  | succ count induction =>
      rw [factorialTerm_succ, one_mul]
      exact div_positive induction (ofRat_succ_positive count)

end

end Problib.Analysis.Real.SignedSeries
