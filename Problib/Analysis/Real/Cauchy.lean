module

public import Problib.Analysis.Real.Sequence

/-! Cauchy completeness of problib's sealed real carrier. -/

set_option autoImplicit false

namespace Problib.Analysis.Real

open Problib.Real.Construction.Dedekind

noncomputable section

private instance : Std.Associative (α := selection.Carrier) add :=
  ⟨fun left middle right => add_assoc left middle right⟩

private instance : Std.Commutative (α := selection.Carrier) add :=
  ⟨add_comm⟩

@[expose] public def Cauchy (values : Nat → selection.Carrier) : Prop :=
  ∀ epsilon : selection.Carrier, lt zero epsilon →
    ∃ stage : Nat, ∀ first second : Nat, stage ≤ first → stage ≤ second →
      lt (abs (sub (values first) (values second))) epsilon

/-- Completeness follows by taking the least upper bound of eventual lower
bounds. The Cauchy condition makes that set nonempty and bounded. -/
public theorem cauchy_converges {values : Nat → selection.Carrier}
    (cauchy : Cauchy values) :
    ∃ limit : selection.Carrier, ConvergesTo values limit := by
  classical
  let eventualLower : selection.Carrier → Prop :=
    fun bound => ∃ stage : Nat, ∀ index, stage ≤ index → le bound (values index)
  rcases cauchy one one_positive with ⟨unitStage, unitClose⟩
  have nonempty : ∃ bound, eventualLower bound := by
    refine ⟨sub (values unitStage) one, unitStage, fun index later => ?_⟩
    have close := (abs_lt.mp (unitClose unitStage index
      (Nat.le_refl _) later)).right
    have shifted := (add_lt_add_right_iff
      (shift := values index)).mpr close
    rw [sub_add_cancel] at shifted
    have moved := (add_lt_add_right_iff (shift := neg one)).mpr shifted
    have simplified : lt (sub (values unitStage) one) (values index) := by
      have canceled : add (add one (values index)) (neg one) = values index := by
        calc
          add (add one (values index)) (neg one) =
              add (add one (neg one)) (values index) := by ac_rfl
          _ = values index := by rw [add_neg, zero_add]
      rw [canceled] at moved
      simpa only [sub_eq_add_neg] using moved
    exact le_of_lt simplified
  have bounded : ∃ upper, Problib.Real.IsUpperBound le eventualLower upper := by
    refine ⟨add (values unitStage) one, fun bound member => ?_⟩
    rcases member with ⟨stage, lower⟩
    let index := max stage unitStage
    have lowerAt := lower index (Nat.le_max_left _ _)
    have close := (abs_lt.mp (unitClose index unitStage
      (Nat.le_max_right _ _) (Nat.le_refl _))).right
    have upperAt : lt (values index) (add (values unitStage) one) := by
      have shifted := (add_lt_add_right_iff
        (shift := values unitStage)).mpr close
      rw [sub_add_cancel] at shifted
      rwa [add_comm one (values unitStage)] at shifted
    exact le_trans lowerAt (le_of_lt upperAt)
  rcases exists_lub eventualLower nonempty bounded with
    ⟨limit, upper, least⟩
  refine ⟨limit, fun epsilon positive => ?_⟩
  have halfPositive := half_positive positive
  have halfLess : lt (half epsilon) epsilon := by
    have raised := add_lt_add_left (half epsilon) halfPositive
    rwa [add_zero, add_half] at raised
  rcases cauchy (half epsilon) halfPositive with ⟨stage, close⟩
  refine ⟨stage, fun index later => ?_⟩
  have upperBound : le limit (add (values index) (half epsilon)) := by
    apply least
    intro bound member
    rcases member with ⟨lowerStage, lower⟩
    let second := max lowerStage stage
    have boundAt := lower second (Nat.le_max_left _ _)
    have closeAt := (abs_lt.mp (close second index
      (Nat.le_max_right _ _) later)).right
    have less : lt (values second) (add (values index) (half epsilon)) := by
      have shifted := (add_lt_add_right_iff
        (shift := values index)).mpr closeAt
      rw [sub_add_cancel] at shifted
      rwa [add_comm (half epsilon) (values index)] at shifted
    exact le_trans boundAt (le_of_lt less)
  have lowerMember : eventualLower (sub (values index) (half epsilon)) := by
    refine ⟨stage, fun second secondLater => ?_⟩
    have closeAt := (abs_lt.mp (close index second later secondLater)).right
    have shifted := (add_lt_add_right_iff
      (shift := values second)).mpr closeAt
    rw [sub_add_cancel] at shifted
    have moved := (add_lt_add_right_iff (shift := neg (half epsilon))).mpr shifted
    have simplified : lt (sub (values index) (half epsilon)) (values second) := by
      have canceled : add (add (half epsilon) (values second))
          (neg (half epsilon)) = values second := by
        calc
          add (add (half epsilon) (values second)) (neg (half epsilon)) =
              add (add (half epsilon) (neg (half epsilon)))
                (values second) := by ac_rfl
          _ = values second := by rw [add_neg, zero_add]
      rw [canceled] at moved
      simpa only [sub_eq_add_neg] using moved
    apply le_of_lt
    exact simplified
  have lowerBound := upper _ lowerMember
  apply abs_lt.mpr
  constructor
  · have shifted := (add_le_add_right_iff
        (shift := neg (half epsilon))).mpr upperBound
    have moved : le (sub limit (half epsilon)) (values index) := by
      simpa only [sub_eq_add_neg, add_assoc, add_neg, add_zero] using shifted
    have opposite : le (neg (half epsilon)) (sub (values index) limit) :=
      (add_le_add_right_iff (shift := limit)).mp (by
        have leftRewrite : add (neg (half epsilon)) limit =
            sub limit (half epsilon) := by
          rw [sub_eq_add_neg, add_comm]
        rw [leftRewrite, sub_add_cancel]
        exact moved)
    exact lt_of_lt_of_le (neg_lt_neg_iff.mpr halfLess) opposite
  · have shifted := (add_le_add_right_iff
        (shift := half epsilon)).mpr lowerBound
    rw [sub_add_cancel] at shifted
    have difference : le (sub (values index) limit) (half epsilon) :=
      (add_le_add_right_iff (shift := limit)).mp (by
        simpa only [sub_add_cancel, add_comm (half epsilon) limit] using shifted)
    exact lt_of_le_of_lt difference halfLess

end

end Problib.Analysis.Real
