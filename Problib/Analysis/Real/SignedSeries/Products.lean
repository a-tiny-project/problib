module

public import Problib.Analysis.Real.SignedSeries.Extended

/-! Product limits and finite convolution for signed real series. -/

set_option autoImplicit false

namespace Problib.Analysis.Real.SignedSeries

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real

noncomputable section

private instance : Std.Associative (α := selection.Carrier) add :=
  ⟨fun left middle right => add_assoc left middle right⟩

private instance : Std.Commutative (α := selection.Carrier) add :=
  ⟨add_comm⟩

private instance : Std.Associative (α := selection.Carrier) mul :=
  ⟨fun left middle right => mul_assoc left middle right⟩

private instance : Std.Commutative (α := selection.Carrier) mul :=
  ⟨mul_comm⟩

/-- A convergent sequence is eventually bounded by one more than its limit
magnitude. -/
public theorem converges_to_eventually_bounded
    {values : Nat → selection.Carrier} {limit : selection.Carrier}
    (converges : ConvergesTo values limit) :
    ∃ stage, ∀ index, stage ≤ index →
      le (abs (values index)) (add (abs limit) one) := by
  rcases converges one one_positive with ⟨stage, close⟩
  refine ⟨stage, fun index later => ?_⟩
  have triangle := abs_add_le (sub (values index) limit) limit
  rw [sub_add_cancel] at triangle
  have raised := add_lt_add_right (abs limit) (close index later)
  exact le_trans triangle (le_of_lt (by
    simpa only [add_comm one (abs limit)] using raised))

private theorem cancel_middle (left cross right : selection.Carrier) :
    add (add left (neg cross)) (add cross right) = add left right := by
  calc
    add (add left (neg cross)) (add cross right) =
        add (add left right) (add (neg cross) cross) := by ac_rfl
    _ = add (add left right) zero := by rw [add_comm (neg cross) cross, add_neg]
    _ = add left right := add_zero _

/-- Products preserve limits of signed real sequences. -/
public theorem converges_to_mul
    {first second : Nat → selection.Carrier}
    {firstLimit secondLimit : selection.Carrier}
    (firstConverges : ConvergesTo first firstLimit)
    (secondConverges : ConvergesTo second secondLimit) :
    ConvergesTo (fun index => mul (first index) (second index))
      (mul firstLimit secondLimit) := by
  intro epsilon positive
  rcases converges_to_eventually_bounded firstConverges with
    ⟨boundedStage, bounded⟩
  have firstBoundPositive : lt zero (add (abs firstLimit) one) := by
    have raised := add_lt_add_left (abs firstLimit) one_positive
    exact lt_of_le_of_lt (abs_nonnegative firstLimit) (by
      rwa [add_zero] at raised)
  have secondBoundPositive : lt zero (add (abs secondLimit) one) := by
    have raised := add_lt_add_left (abs secondLimit) one_positive
    exact lt_of_le_of_lt (abs_nonnegative secondLimit) (by
      rwa [add_zero] at raised)
  have firstBoundNonzero : add (abs firstLimit) one ≠ zero := by
    intro vanished
    have copy := firstBoundPositive
    rw [vanished] at copy
    exact lt_irrefl zero copy
  have secondBoundNonzero : add (abs secondLimit) one ≠ zero := by
    intro vanished
    have copy := secondBoundPositive
    rw [vanished] at copy
    exact lt_irrefl zero copy
  have secondTolerance : lt zero (div (half epsilon)
      (add (abs firstLimit) one)) :=
    div_positive (half_positive positive) firstBoundPositive
  have firstTolerance : lt zero (div (half epsilon)
      (add (abs secondLimit) one)) :=
    div_positive (half_positive positive) secondBoundPositive
  rcases firstConverges _ firstTolerance with ⟨firstStage, firstClose⟩
  rcases secondConverges _ secondTolerance with ⟨secondStage, secondClose⟩
  let stage := max (max firstStage secondStage) boundedStage
  refine ⟨stage, fun index later => ?_⟩
  have firstLater : firstStage ≤ index :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) later
  have secondLater : secondStage ≤ index :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) later
  have boundedLater : boundedStage ≤ index :=
    Nat.le_trans (Nat.le_max_right _ _) later
  have split : sub (mul (first index) (second index))
      (mul firstLimit secondLimit) =
      add (mul (first index) (sub (second index) secondLimit))
        (mul secondLimit (sub (first index) firstLimit)) := by
    calc
      sub (mul (first index) (second index)) (mul firstLimit secondLimit) =
          add (mul (first index) (second index))
            (neg (mul firstLimit secondLimit)) := sub_eq_add_neg _ _
      _ = add
          (add (mul (first index) (second index))
            (neg (mul (first index) secondLimit)))
          (add (mul (first index) secondLimit)
            (neg (mul firstLimit secondLimit))) := (cancel_middle _ _ _).symm
      _ = add (mul (first index) (sub (second index) secondLimit))
          (mul secondLimit (sub (first index) firstLimit)) := by
        rw [mul_sub, mul_sub, sub_eq_add_neg, sub_eq_add_neg,
          mul_comm secondLimit (first index), mul_comm secondLimit firstLimit]
  rw [split]
  refine lt_of_le_of_lt (abs_add_le _ _) ?_
  have leftPiece :
      lt (abs (mul (first index) (sub (second index) secondLimit)))
        (half epsilon) := by
    rw [abs_mul]
    refine lt_of_le_of_lt
      (mul_le_mul_nonnegative_right (bounded index boundedLater)
        (abs_nonnegative (sub (second index) secondLimit))) ?_
    have scaled := mul_lt_mul_positive_left
      (secondClose index secondLater) firstBoundPositive
    rwa [mul_div_cancel (half epsilon) firstBoundNonzero] at scaled
  have rightPiece :
      lt (abs (mul secondLimit (sub (first index) firstLimit)))
        (half epsilon) := by
    rw [abs_mul]
    refine lt_of_le_of_lt
      (mul_le_mul_nonnegative_right
        (by
          have raised := add_lt_add_left (abs secondLimit) one_positive
          exact le_of_lt (by rwa [add_zero] at raised))
        (abs_nonnegative (sub (first index) firstLimit))) ?_
    have scaled := mul_lt_mul_positive_left
      (firstClose index firstLater) secondBoundPositive
    rwa [mul_div_cancel (half epsilon) secondBoundNonzero] at scaled
  have combined := add_lt_add leftPiece rightPiece
  rwa [add_half] at combined

end

end Problib.Analysis.Real.SignedSeries
