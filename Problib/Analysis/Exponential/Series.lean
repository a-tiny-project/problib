module

public import Problib.Analysis.Exponential.Derivative
public import Problib.Analysis.Real.Calculus
public import Problib.Analysis.Real.FactorialSeries
public import Problib.Analysis.Real.MeanValue
public import Problib.Analysis.Real.SignedSeries.CauchyProduct

/-! The exponential is the sum of its factorial series.

Write `E(x)` for the sum of `x^n / n!`. The second-order remainder
`E(x + h) - E(x) - h E(x)` is the sum of the termwise gaps
`T_{x+h}(n) - T_x(n) - h T_x(n - 1)`. The gaps obey the one-step recurrence
`(n + 1) D(n + 1) = (x + h) D(n) + h² T_x(n - 1)`, so each is at most `h²`
times the twice-shifted term of any radius above `|x|` and `|x + h|`. The
remainder is then at most `h²` times a fixed sum, and `E` differentiates to
itself. The quotient of `E` by the exponential has zero derivative, and both
are one at zero, so they agree.
-/

set_option autoImplicit false

open scoped Problib.Real.AC

namespace Problib.Analysis

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real
open Problib.Analysis.Real.SignedSeries

noncomputable section

local notation "natural " value => selection.ofRat (((value : Nat)) : Rat)

private theorem natural_succ (value : Nat) :
    (natural (value + 1)) = add (natural value) one := by
  rw [Rat.natCast_add, ofRat_add, show ((1 : Nat) : Rat) = 1 from rfl, ofRat_one]

private theorem natural_positive (value : Nat) : lt zero (natural (value + 1)) := by
  have embedded := (ofRat_lt_iff 0 ((value + 1 : Nat) : Rat)).mpr
    (Rat.natCast_pos.mpr (Nat.succ_pos value))
  rwa [ofRat_zero] at embedded

private theorem natural_nonzero (value : Nat) : (natural (value + 1)) ≠ zero := by
  intro vanished
  have positive := natural_positive value
  rw [vanished] at positive
  exact lt_irrefl zero positive

private theorem natural_le_succ (value : Nat) :
    le (natural value) (natural (value + 1)) :=
  (ofRat_le_iff _ _).mpr (Rat.natCast_le_natCast.mpr (Nat.le_succ value))

private theorem factorial_step (base : selection.Carrier) (index : Nat) :
    mul (natural (index + 1)) (factorialTerm base (index + 1)) =
      mul base (factorialTerm base index) := by
  rw [factorialTerm_succ]
  exact mul_div_cancel _ (natural_nonzero index)

/-- Factorial terms of a nonnegative base are nonnegative. -/
public theorem factorialTerm_nonnegative {base : selection.Carrier}
    (nonnegative : le zero base) :
    ∀ index, le zero (factorialTerm base index)
  | 0 => one_nonnegative
  | index + 1 => by
      rw [factorialTerm_succ]
      exact div_nonnegative
        (mul_nonnegative nonnegative (factorialTerm_nonnegative nonnegative index))
        (natural_positive index).left

/-- The magnitude of a factorial term is the term of the magnitude. -/
public theorem abs_factorialTerm (base : selection.Carrier) :
    ∀ index, abs (factorialTerm base index) = factorialTerm (abs base) index
  | 0 => abs_of_nonnegative one_nonnegative
  | index + 1 => by
      rw [factorialTerm_succ, factorialTerm_succ, abs_div, abs_mul,
        abs_factorialTerm base index,
        abs_of_nonnegative (natural_positive index).left]

private theorem factorialTerm_mono {lower upper : selection.Carrier}
    (nonnegative : le zero lower) (included : le lower upper) :
    ∀ index, le (factorialTerm lower index) (factorialTerm upper index)
  | 0 => le_refl one
  | index + 1 => by
      rw [factorialTerm_succ, factorialTerm_succ, div_eq_mul_inverse,
        div_eq_mul_inverse]
      apply mul_le_mul_nonnegative_right _
        (le_of_lt (inverse_of_positive_positive (natural_positive index)))
      exact le_trans
        (mul_le_mul_nonnegative_left
          (factorialTerm_mono nonnegative included index) nonnegative)
        (mul_le_mul_nonnegative_right included
          (factorialTerm_nonnegative (le_trans nonnegative included) index))

/-- A sequence moved one place later, with a zero in front. -/
private def shifted (values : Nat → selection.Carrier) : Nat → selection.Carrier
  | 0 => zero
  | index + 1 => values index

private theorem shifted_nonnegative {values : Nat → selection.Carrier}
    (nonnegative : ∀ index, le zero (values index)) :
    ∀ index, le zero (shifted values index)
  | 0 => le_refl zero
  | index + 1 => nonnegative index

private theorem partialSum_shifted (values : Nat → selection.Carrier) :
    ∀ length, partialSum (shifted values) (length + 1) = partialSum values length
  | 0 => by
      change add zero zero = zero
      exact add_zero zero
  | length + 1 => by
      rw [partialSum_succ, partialSum_shifted values length]
      rfl

private theorem partialSum_shifted_le {values : Nat → selection.Carrier}
    (nonnegative : ∀ index, le zero (values index)) :
    ∀ length, le (partialSum (shifted values) length) (partialSum values length)
  | 0 => le_refl zero
  | length + 1 => by
      rw [partialSum_shifted]
      exact partialSum_monotone nonnegative (Nat.le_succ length)

private theorem converges_to_of_shift {values : Nat → selection.Carrier}
    {limit : selection.Carrier}
    (converges : ConvergesTo (fun index => values (index + 1)) limit) :
    ConvergesTo values limit := by
  intro epsilon positive
  rcases converges epsilon positive with ⟨stage, close⟩
  refine ⟨stage + 1, fun index later => ?_⟩
  obtain ⟨previous, rfl⟩ : ∃ previous, index = previous + 1 :=
    ⟨index - 1, by omega⟩
  exact close previous (by omega)

private theorem shifted_converges {values : Nat → selection.Carrier}
    (certificate : Summable values) :
    ConvergesTo (partialSum (shifted values)) (sum values certificate) := by
  apply converges_to_of_shift
  have equal : (fun length => partialSum (shifted values) (length + 1)) =
      partialSum values := funext (partialSum_shifted values)
  rw [equal]
  exact partialSum_converges values certificate

/-- `(n + 1) T(n) = T(n) + y T(n - 1)`, the index form of `y E' = y E`. -/
private theorem factorial_shift (base : selection.Carrier) :
    ∀ index, add (factorialTerm base index)
        (mul base (shifted (factorialTerm base) index)) =
      mul (natural (index + 1)) (factorialTerm base index)
  | 0 => by
      change add one (mul base zero) = mul (selection.ofRat ((1 : Nat) : Rat)) one
      rw [mul_zero, add_zero, mul_one, show ((1 : Nat) : Rat) = 1 from rfl, ofRat_one]
  | index + 1 => by
      change add (factorialTerm base (index + 1))
          (mul base (factorialTerm base index)) = _
      rw [← factorial_step, natural_succ (index + 1), add_mul, one_mul, add_comm]

/-- The termwise second-order gap between the series at `point + step` and
its first-order prediction from `point`. -/
private def gap (point step : selection.Carrier) (index : Nat) :
    selection.Carrier :=
  sub (sub (factorialTerm (add point step) index) (factorialTerm point index))
    (mul step (shifted (factorialTerm point) index))

private theorem sub_add_add_cancel (first second third : selection.Carrier) :
    add (sub first (add second third)) third = sub first second := by
  rw [sub_eq_add_neg, sub_eq_add_neg, neg_add, add_assoc, add_assoc,
    add_comm (neg third) third, add_neg, add_zero]

private theorem gap_algebra (point step moved here earlier : selection.Carrier) :
    sub (sub (mul (add point step) moved) (mul point here))
        (mul step (add here (mul point earlier))) =
      add (mul (add point step) (sub (sub moved here) (mul step earlier)))
        (mul (mul step step) earlier) := by
  rw [mul_sub (add point step) (sub moved here), add_mul point step (mul step earlier),
    mul_assoc step step earlier, sub_add_add_cancel]
  simp only [sub_eq_add_neg, mul_add, add_mul, neg_add, mul_neg]
  ac_rfl

private theorem gap_step (point step : selection.Carrier) (index : Nat) :
    mul (natural (index + 1)) (gap point step (index + 1)) =
      add (mul (add point step) (gap point step index))
        (mul (mul step step) (shifted (factorialTerm point) index)) := by
  change mul (natural (index + 1))
      (sub (sub (factorialTerm (add point step) (index + 1))
        (factorialTerm point (index + 1)))
        (mul step (factorialTerm point index))) = _
  rw [mul_sub, mul_sub, factorial_step, factorial_step, ← mul_assoc,
    mul_comm (natural (index + 1)) step, mul_assoc, ← factorial_shift point index]
  exact gap_algebra _ _ _ _ _

private theorem abs_shifted_le {point bound : selection.Carrier}
    (below : le (abs point) bound) :
    ∀ index, le (abs (shifted (factorialTerm point) index))
      (shifted (factorialTerm bound) index)
  | 0 => by
      change le (abs zero) zero
      rw [abs_zero]
      exact le_refl zero
  | index + 1 => by
      change le (abs (factorialTerm point index)) (factorialTerm bound index)
      rw [abs_factorialTerm]
      exact factorialTerm_mono (abs_nonnegative point) below index

private theorem shift_margin {bound : selection.Carrier}
    (nonnegative : le zero bound) :
    ∀ index, le (add (mul bound (shifted (shifted (factorialTerm bound)) index))
        (shifted (factorialTerm bound) index))
      (mul (natural (index + 1)) (shifted (factorialTerm bound) index))
  | 0 => by
      change le (add (mul bound zero) zero)
        (mul (selection.ofRat ((1 : Nat) : Rat)) zero)
      rw [mul_zero, mul_zero, add_zero]
      exact le_refl zero
  | index + 1 => by
      change le (add (mul bound (shifted (factorialTerm bound) index))
          (factorialTerm bound index))
        (mul (natural (index + 1 + 1)) (factorialTerm bound index))
      rw [add_comm, factorial_shift bound index]
      exact mul_le_mul_nonnegative_right (natural_le_succ (index + 1))
        (factorialTerm_nonnegative nonnegative index)

private theorem gap_bound {point step bound : selection.Carrier}
    (pointBelow : le (abs point) bound)
    (movedBelow : le (abs (add point step)) bound) :
    ∀ index, le (abs (gap point step index))
      (mul (mul step step) (shifted (shifted (factorialTerm bound)) index))
  | 0 => by
      change le (abs (sub (sub one one) (mul step zero)))
        (mul (mul step step) zero)
      rw [sub_self, mul_zero, mul_zero, sub_zero, abs_zero]
      exact le_refl zero
  | index + 1 => by
      have boundNonnegative := le_trans (abs_nonnegative point) pointBelow
      have squareNonnegative : le zero (mul step step) := mul_self_nonnegative step
      apply (mul_le_mul_left_iff (natural_positive index)).mp
      have scaled : abs (mul (natural (index + 1)) (gap point step (index + 1))) =
          mul (natural (index + 1)) (abs (gap point step (index + 1))) := by
        rw [abs_mul, abs_of_nonnegative (natural_positive index).left]
      rw [← scaled, gap_step]
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_mul, abs_mul, abs_of_nonnegative squareNonnegative]
      have first : le (mul (abs (add point step)) (abs (gap point step index)))
          (mul bound (mul (mul step step)
            (shifted (shifted (factorialTerm bound)) index))) :=
        le_trans (mul_le_mul_nonnegative_right movedBelow (abs_nonnegative _))
          (mul_le_mul_nonnegative_left (gap_bound pointBelow movedBelow index)
            boundNonnegative)
      have second : le (mul (mul step step)
            (abs (shifted (factorialTerm point) index)))
          (mul (mul step step) (shifted (factorialTerm bound) index)) :=
        mul_le_mul_nonnegative_left (abs_shifted_le pointBelow index)
          squareNonnegative
      refine le_trans (add_le_add first second) ?_
      have regrouped : add (mul bound (mul (mul step step)
            (shifted (shifted (factorialTerm bound)) index)))
          (mul (mul step step) (shifted (factorialTerm bound) index)) =
          mul (mul step step)
            (add (mul bound (shifted (shifted (factorialTerm bound)) index))
              (shifted (factorialTerm bound) index)) := by
        rw [mul_add]
        ac_rfl
      have target : mul (natural (index + 1)) (mul (mul step step)
            (shifted (shifted (factorialTerm bound)) (index + 1))) =
          mul (mul step step)
            (mul (natural (index + 1)) (shifted (factorialTerm bound) index)) := by
        change mul (natural (index + 1)) (mul (mul step step)
            (shifted (factorialTerm bound) index)) = _
        ac_rfl
      rw [regrouped, target]
      exact mul_le_mul_nonnegative_left (shift_margin boundNonnegative index)
        squareNonnegative

/-- The sum of the factorial series. -/
private def seriesValue (point : selection.Carrier) : selection.Carrier :=
  sum (factorialTerm point) (factorial_summable point)

private theorem seriesValue_nonnegative {point : selection.Carrier}
    (nonnegative : le zero point) : le zero (seriesValue point) := by
  have first := partialSum_le_sum_nonnegative
    (factorialTerm_nonnegative nonnegative) (factorial_summable point) 0
  rwa [partialSum_zero] at first

private theorem gap_converges (point step : selection.Carrier) :
    ConvergesTo (partialSum (gap point step))
      (sub (sub (seriesValue (add point step)) (seriesValue point))
        (mul step (seriesValue point))) := by
  have equal : partialSum (gap point step) = fun length =>
      sub (sub (partialSum (factorialTerm (add point step)) length)
          (partialSum (factorialTerm point) length))
        (mul step (partialSum (shifted (factorialTerm point)) length)) := by
    funext length
    change partialSum (fun index => sub (sub (factorialTerm (add point step) index)
      (factorialTerm point index))
      (mul step (shifted (factorialTerm point) index))) length = _
    rw [partialSum_sub, partialSum_sub, partialSum_scale]
  rw [equal]
  exact converges_to_sub
    (converges_to_sub (partialSum_converges _ _) (partialSum_converges _ _))
    (converges_to_scale step (shifted_converges (factorial_summable point)))

private theorem remainder_bound {point step bound : selection.Carrier}
    (pointBelow : le (abs point) bound)
    (movedBelow : le (abs (add point step)) bound) :
    le (abs (sub (sub (seriesValue (add point step)) (seriesValue point))
        (mul step (seriesValue point))))
      (mul (mul step step) (seriesValue bound)) := by
  have boundNonnegative := le_trans (abs_nonnegative point) pointBelow
  have termsNonnegative := factorialTerm_nonnegative boundNonnegative
  apply abs_le_of_convergesTo (gap_converges point step)
  intro length
  refine le_trans (abs_partialSum_le _ length) ?_
  refine le_trans (partialSum_le (gap_bound pointBelow movedBelow) length) ?_
  rw [partialSum_scale]
  apply mul_le_mul_nonnegative_left _ (mul_self_nonnegative step)
  exact le_trans
    (partialSum_shifted_le (shifted_nonnegative termsNonnegative) length)
    (le_trans (partialSum_shifted_le termsNonnegative length)
      (partialSum_le_sum_nonnegative termsNonnegative
        (factorial_summable bound) length))

private theorem hasDerivative_seriesValue (point : selection.Carrier) :
    HasDerivative seriesValue point (seriesValue point) := by
  let bound := add (abs point) one
  have pointBelow : le (abs point) bound := by
    have shifted := add_le_add (le_refl (abs point)) one_nonnegative
    rwa [add_zero] at shifted
  apply derivative_of_secant_bound seriesValue point (seriesValue point) one
    (seriesValue bound) one_positive
    (seriesValue_nonnegative (le_trans (abs_nonnegative point) pointBelow))
  intro step nonzero small
  have movedBelow : le (abs (add point step)) bound :=
    le_trans (abs_add_le _ _) (add_le_add (le_refl _) (le_of_lt small))
  have remainder := remainder_bound pointBelow movedBelow
  have absoluteNonnegative := abs_nonnegative step
  have absoluteNonzero : abs step ≠ zero := fun vanished =>
    nonzero (abs_eq_zero_iff.mp vanished)
  have rewritten : sub (secant seriesValue point step) (seriesValue point) =
      div (sub (sub (seriesValue (add point step)) (seriesValue point))
        (mul step (seriesValue point))) step := by
    rw [sub_div _ (mul step (seriesValue point)),
      mul_comm step (seriesValue point), mul_div_assoc, div_self nonzero, mul_one]
    rfl
  have square : mul step step = mul (abs step) (abs step) := by
    rw [← abs_mul, abs_of_nonnegative (mul_self_nonnegative step)]
  rw [rewritten, abs_div, div_eq_mul_inverse]
  have scaled := mul_le_mul_nonnegative_right remainder
    (le_of_lt (inverse_of_positive_positive (abs_positive_of_nonzero nonzero)))
  have closing : mul (mul (mul step step) (seriesValue bound)) (inverse (abs step)) =
      mul (seriesValue bound) (abs step) := by
    rw [square]
    have regrouped : mul (mul (mul (abs step) (abs step)) (seriesValue bound))
        (inverse (abs step)) =
        mul (mul (abs step) (inverse (abs step))) (mul (seriesValue bound) (abs step)) := by
      ac_rfl
    rw [regrouped, mul_inverse_cancel absoluteNonzero, one_mul]
  rwa [closing] at scaled

private theorem seriesValue_zero : seriesValue zero = one := by
  apply sum_eq_of_converges
  apply converges_to_of_shift
  have constant : ∀ length,
      partialSum (factorialTerm zero) (length + 1) = one := by
    intro length
    induction length with
    | zero =>
        rw [partialSum_succ, partialSum_zero, factorialTerm_zero, zero_add]
    | succ length previous =>
        rw [partialSum_succ, previous, factorialTerm_succ, zero_mul, zero_div,
          add_zero]
  have equal : (fun length => partialSum (factorialTerm zero) (length + 1)) =
      fun _ => one := funext constant
  rw [equal]
  exact converges_to_const one

private theorem exp_nonzero (point : selection.Carrier) : exp point ≠ zero := by
  intro vanished
  have positive := exp_positive point
  rw [vanished] at positive
  exact lt_irrefl zero positive

/-- The exponential is the sum of its factorial series. -/
public theorem exp_eq_sum (point : selection.Carrier) :
    exp point = sum (factorialTerm point) (factorial_summable point) := by
  have flat : ∀ value, HasDerivative
      (fun input => div (seriesValue input) (exp input)) value zero := by
    intro value
    have quotient := hasDerivative_div (hasDerivative_seriesValue value)
      (hasDerivative_exp value) (exp_nonzero value)
    rwa [sub_self, zero_div] at quotient
  have constant := eq_of_hasDerivative_zero flat point zero
  change div (seriesValue point) (exp point) =
    div (seriesValue zero) (exp zero) at constant
  have oneNonzero : one ≠ zero := by
    intro vanished
    have positive := one_positive
    rw [vanished] at positive
    exact lt_irrefl zero positive
  rw [seriesValue_zero, exp_zero, div_self oneNonzero] at constant
  have recovered := div_mul_cancel (seriesValue point) (exp_nonzero point)
  rw [constant, one_mul] at recovered
  exact recovered

end

end Problib.Analysis
