module

public import Problib.Analysis.Real.GeometricSeries

/-! Absolute convergence from an eventual geometric ratio bound. -/

set_option autoImplicit false

namespace Problib.Analysis.Real.SignedSeries

open Problib.Real.Construction.Dedekind

noncomputable section

/-- An eventual bound by a geometric sequence gives a uniform bound on all
absolute partial sums. -/
public theorem absolutely_summable_of_ratio
    {values : Nat → selection.Carrier} {ratio : selection.Carrier}
    (ratioNonnegative : le zero ratio) (ratioBelowOne : lt ratio one)
    (start : Nat)
    (contract : ∀ index, start ≤ index →
      le (abs (values (index + 1)))
        (mul ratio (abs (values index)))) :
    AbsolutelySummable values := by
  let magnitude := fun index => abs (values index)
  let base := magnitude start
  let tailBound := mul base (inverse (sub one ratio))
  have baseNonnegative : le zero base := abs_nonnegative _
  have gapPositive : lt zero (sub one ratio) := sub_positive_iff.mpr ratioBelowOne
  have tailNonnegative : le zero tailBound :=
    mul_nonnegative baseNonnegative
      (le_of_lt (inverse_of_positive_positive gapPositive))
  have pointwise (length : Nat) :
      le (magnitude (start + length)) (mul base (power ratio length)) := by
    induction length with
    | zero =>
        rw [Nat.add_zero, power_zero, mul_one]
        exact le_refl _
    | succ length induction =>
        rw [Nat.add_succ, power_succ]
        have step := contract (start + length) (Nat.le_add_right _ _)
        have scaled := mul_le_mul_nonnegative_left induction ratioNonnegative
        have commute : mul ratio (mul base (power ratio length)) =
            mul base (mul ratio (power ratio length)) := by
          rw [← mul_assoc, mul_comm ratio base, mul_assoc]
        rw [commute] at scaled
        exact le_trans step scaled
  refine ⟨add (partialSum magnitude start) tailBound, fun count => ?_⟩
  by_cases early : count ≤ start
  · have prefixBound := partial_sum_monotone
      (fun index => abs_nonnegative (values index)) early
    exact le_trans prefixBound (by
      have shifted := (add_le_add_left_iff
        (shift := partialSum magnitude start)).mpr tailNonnegative
      simpa only [add_zero] using shifted)
  · have later : start ≤ count := Nat.le_of_lt (Nat.lt_of_not_ge early)
    have split := partial_sum_append magnitude start (count - start)
    have countEq : start + (count - start) = count := Nat.add_sub_of_le later
    rw [countEq] at split
    rw [split]
    have tailSumBound :
        le (partialSum (fun offset => magnitude (start + offset)) (count - start))
          (partialSum (fun offset => mul base (power ratio offset))
            (count - start)) :=
      partial_sum_le pointwise _
    rw [partial_sum_scale] at tailSumBound
    have geometricBound := geometric_bounded ratioNonnegative ratioBelowOne
      (count - start)
    have scaled := mul_le_mul_nonnegative_left geometricBound baseNonnegative
    have combined := le_trans tailSumBound scaled
    exact add_le_add (le_refl _) combined

/-- The ratio test on the sealed real carrier. -/
public theorem summable_of_ratio
    {values : Nat → selection.Carrier} {ratio : selection.Carrier}
    (ratioNonnegative : le zero ratio) (ratioBelowOne : lt ratio one)
    (start : Nat)
    (contract : ∀ index, start ≤ index →
      le (abs (values (index + 1)))
        (mul ratio (abs (values index)))) :
    Summable values :=
  summable_of_absolute_bound
    (absolutely_summable_of_ratio ratioNonnegative ratioBelowOne start contract)

end

end Problib.Analysis.Real.SignedSeries
