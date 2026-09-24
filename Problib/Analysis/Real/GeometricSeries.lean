module

public import Problib.Analysis.Real.SignedSeries

/-! Geometric majorants for signed power series. -/

set_option autoImplicit false

namespace Problib.Analysis.Real.SignedSeries

open Problib.Real.Construction.Dedekind

noncomputable section

/-- Natural powers in the sealed signed real carrier. -/
@[expose] public def power (base : selection.Carrier) : Nat → selection.Carrier
  | 0 => one
  | count + 1 => mul base (power base count)

public theorem power_zero (base : selection.Carrier) : power base 0 = one := rfl

public theorem power_succ (base : selection.Carrier) (count : Nat) :
    power base (count + 1) = mul base (power base count) := rfl

public theorem power_add (base : selection.Carrier) (first second : Nat) :
    power base (first + second) =
      mul (power base first) (power base second) := by
  induction first with
  | zero => rw [Nat.zero_add, power_zero, one_mul]
  | succ first induction =>
      rw [Nat.succ_add, power_succ, induction, power_succ, mul_assoc]

public theorem power_nonnegative {base : selection.Carrier}
    (nonnegative : le zero base) (count : Nat) :
    le zero (power base count) := by
  induction count with
  | zero => exact one_nonnegative
  | succ count induction =>
      rw [power_succ]
      exact mul_nonnegative nonnegative induction

public theorem abs_power (base : selection.Carrier) (count : Nat) :
    abs (power base count) = power (abs base) count := by
  induction count with
  | zero =>
      rw [power_zero, power_zero, abs_of_nonnegative one_nonnegative]
  | succ count induction =>
      rw [power_succ, power_succ, abs_mul, induction]

public theorem power_le_one {base : selection.Carrier}
    (nonnegative : le zero base) (atMostOne : le base one) (count : Nat) :
    le (power base count) one := by
  induction count with
  | zero => exact le_refl one
  | succ count induction =>
      rw [power_succ]
      have raised := mul_le_mul_nonnegative_right atMostOne
        (power_nonnegative nonnegative count)
      rw [one_mul] at raised
      exact le_trans raised induction

/-- Multiplying a geometric partial sum by `1 - ratio` telescopes. -/
public theorem geometric_telescope (ratio : selection.Carrier) (count : Nat) :
    mul (sub one ratio) (partialSum (power ratio) count) =
      sub one (power ratio count) := by
  induction count with
  | zero => rw [partial_sum_zero, mul_zero, power_zero, sub_self]
  | succ count induction =>
      rw [partial_sum_succ, mul_add, induction, power_succ,
        sub_mul, one_mul]
      exact sub_add_sub one (power ratio count)
        (mul ratio (power ratio count))

/-- The geometric partial sums are bounded by the reciprocal of their gap. -/
public theorem geometric_bounded {ratio : selection.Carrier}
    (nonnegative : le zero ratio) (belowOne : lt ratio one) :
    ∀ count, le (partialSum (power ratio) count)
      (inverse (sub one ratio)) := by
  have gapPositive : lt zero (sub one ratio) := sub_positive_iff.mpr belowOne
  have inversePositive := inverse_of_positive_positive gapPositive
  have gapNonzero : sub one ratio ≠ zero := by
    intro vanished
    have copy := gapPositive
    rw [vanished] at copy
    exact lt_irrefl zero copy
  intro count
  have powerNonnegative := power_nonnegative nonnegative count
  have targetBound : le (sub one (power ratio count)) one := by
    have reflected := neg_nonpositive_iff.mp powerNonnegative
    have shifted := (add_le_add_left_iff (shift := one)).mpr reflected
    simpa only [sub_eq_add_neg, add_zero] using shifted
  have scaled := mul_le_mul_nonnegative_left
    (show le (mul (sub one ratio) (partialSum (power ratio) count)) one by
      rw [geometric_telescope]
      exact targetBound)
    (le_of_lt inversePositive)
  rw [← mul_assoc, inverse_mul_cancel gapNonzero, one_mul, mul_one] at scaled
  exact scaled

/-- A real geometric series is summable when its magnitude ratio is below one. -/
public theorem geometric_summable {ratio : selection.Carrier}
    (nonnegative : le zero ratio) (belowOne : lt ratio one) :
    Summable (power ratio) :=
  summable_of_nonnegative_bounded
    (fun index => power_nonnegative nonnegative index)
    ⟨inverse (sub one ratio), geometric_bounded nonnegative belowOne⟩

/-- Absolute convergence of a signed geometric series uses its magnitude
ratio as the nonnegative majorant. -/
public theorem geometric_summable_of_abs_lt_one {ratio : selection.Carrier}
    (belowOne : lt (abs ratio) one) :
    Summable (power ratio) := by
  apply summable_of_majorant
    (majorant := power (abs ratio))
  · intro index
    rw [abs_power]
    exact le_refl _
  · exact ⟨inverse (sub one (abs ratio)),
      geometric_bounded (abs_nonnegative ratio) belowOne⟩

end

end Problib.Analysis.Real.SignedSeries
