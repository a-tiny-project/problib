module

public import Problib.Real.Extended.Indexed
public import Problib.Real.Extended.Lattice

namespace Problib.Real.ENNReal

set_option autoImplicit false

@[expose] public def add : ENNReal → ENNReal → ENNReal
  | .finite left, .finite right => .finite (NNReal.add left right)
  | _, _ => top

/-- The sum of two finite extended-nonnegative values is finite. -/
public theorem add_finite {left right : ENNReal}
    (leftFinite : Finite left) (rightFinite : Finite right) :
    Finite (add left right) := by
  rcases exists_finite_of_finite leftFinite with ⟨leftValue, rfl⟩
  rcases exists_finite_of_finite rightFinite with ⟨rightValue, rfl⟩
  exact True.intro

public theorem add_comm (left right : ENNReal) :
    add left right = add right left := by
  cases left with
  | top =>
      cases right with
      | top => rfl
      | finite _ => rfl
  | finite leftValue =>
      cases right with
      | top => rfl
      | finite rightValue =>
          exact congrArg finite (NNReal.add_comm leftValue rightValue)

public theorem add_assoc (left middle right : ENNReal) :
    add (add left middle) right = add left (add middle right) := by
  cases left with
  | top =>
      cases middle <;> cases right <;> rfl
  | finite leftValue =>
      cases middle with
      | top => cases right <;> rfl
      | finite middleValue =>
          cases right with
          | top => rfl
          | finite rightValue =>
              exact congrArg finite
                (NNReal.add_assoc leftValue middleValue rightValue)

public theorem add_left_comm (first second third : ENNReal) :
    add first (add second third) = add second (add first third) := by
  rw [← add_assoc first second third, add_comm first second, add_assoc]

public theorem add_right_comm (first second third : ENNReal) :
    add (add first second) third = add (add first third) second := by
  rw [add_assoc first second third, add_comm second third, ← add_assoc]

public theorem add_add_comm (first second third fourth : ENNReal) :
    add (add first second) (add third fourth) =
      add (add first third) (add second fourth) := by
  rw [add_assoc first second (add third fourth),
    ← add_assoc second third fourth, add_comm second third,
    add_assoc third second fourth, ← add_assoc first third (add second fourth)]

public theorem add_zero (value : ENNReal) : add value zero = value := by
  cases value with
  | top => rfl
  | finite underlying => exact congrArg finite (NNReal.add_zero underlying)

public theorem zero_add (value : ENNReal) : add zero value = value := by
  rw [add_comm, add_zero]

public theorem add_top (value : ENNReal) : add value top = top := by
  cases value <;> rfl

public theorem top_add (value : ENNReal) : add top value = top := by
  rw [add_comm, add_top]

public def additiveLaws :
    Problib.Algebra.AdditiveCommutativeMonoidLaws ENNReal where
  zero := zero
  add := add
  add_comm := add_comm
  add_assoc := add_assoc
  add_zero := add_zero

public theorem add_le_add_right {left right : ENNReal}
    (included : le left right) (shift : ENNReal) :
    le (add left shift) (add right shift) := by
  cases shift with
  | top =>
      rw [add_top, add_top]
      exact le_refl top
  | finite shiftValue =>
      cases left with
      | top =>
          cases right with
          | top => exact le_refl top
          | finite _ => exact False.elim included
      | finite leftValue =>
          cases right with
          | top => exact le_top _
          | finite rightValue =>
              exact NNReal.add_le_add_right included shiftValue

public theorem add_le_add_left {left right : ENNReal}
    (included : le left right) (shift : ENNReal) :
    le (add shift left) (add shift right) := by
  rw [add_comm shift left, add_comm shift right]
  exact add_le_add_right included shift

public theorem add_le_add {firstLeft firstRight secondLeft secondRight : ENNReal}
    (firstIncluded : le firstLeft firstRight)
    (secondIncluded : le secondLeft secondRight) :
    le (add firstLeft secondLeft) (add firstRight secondRight) :=
  le_trans (add_le_add_right firstIncluded secondLeft)
    (add_le_add_left secondIncluded firstRight)

public theorem add_eq_zero_iff {left right : ENNReal} :
    add left right = zero ↔ left = zero ∧ right = zero := by
  constructor
  · intro equal
    have leftIncluded : le left (add left right) := by
      have shifted := add_le_add_left (zero_le right) left
      rw [add_zero] at shifted
      exact shifted
    have rightIncluded : le right (add left right) := by
      have shifted := add_le_add_right (zero_le left) right
      rw [zero_add] at shifted
      exact shifted
    rw [equal] at leftIncluded rightIncluded
    exact ⟨eq_zero_of_le_zero leftIncluded, eq_zero_of_le_zero rightIncluded⟩
  · rintro ⟨rfl, rfl⟩
    exact zero_add zero

public theorem add_left_cancel_of_finite {factor left right : ENNReal}
    (factorFinite : Finite factor)
    (equal : add factor left = add factor right) : left = right := by
  rcases exists_finite_of_finite factorFinite with ⟨factorValue, rfl⟩
  cases left with
  | top =>
      cases right with
      | top => rfl
      | finite rightValue =>
          exact False.elim (top_ne_finite (NNReal.add factorValue rightValue) equal)
  | finite leftValue =>
      cases right with
      | top =>
          exact False.elim (finite_ne_top (NNReal.add factorValue leftValue) equal)
      | finite rightValue =>
          apply congrArg finite
          apply NNReal.add_left_cancel
          exact finite_injective equal

public theorem add_right_cancel_of_finite {factor left right : ENNReal}
    (factorFinite : Finite factor)
    (equal : add left factor = add right factor) : left = right := by
  apply add_left_cancel_of_finite factorFinite
  rw [add_comm factor left, add_comm factor right]
  exact equal

public theorem le_of_add_le_add_left_of_finite {factor left right : ENNReal}
    (factorFinite : Finite factor)
    (included : le (add factor left) (add factor right)) : le left right := by
  rcases exists_finite_of_finite factorFinite with ⟨factorValue, rfl⟩
  cases left with
  | top =>
      cases right with
      | top => exact le_refl top
      | finite _ => exact False.elim included
  | finite leftValue =>
      cases right with
      | top => exact le_top _
      | finite rightValue =>
          exact (NNReal.add_le_add_left_iff).mp included

public theorem le_of_add_le_add_right_of_finite {factor left right : ENNReal}
    (factorFinite : Finite factor)
    (included : le (add left factor) (add right factor)) : le left right := by
  apply le_of_add_le_add_left_of_finite factorFinite
  rw [add_comm factor left, add_comm factor right]
  exact included

@[expose] public noncomputable def sub : ENNReal → ENNReal → ENNReal
  | .finite left, .finite right => .finite (NNReal.sub left right)
  | .top, .finite _ => top
  | .finite _, .top => zero
  | .top, .top => zero

public theorem sub_finite_of_finite_left {left right : ENNReal}
    (leftFinite : Finite left) : Finite (sub left right) := by
  rcases exists_finite_of_finite leftFinite with ⟨leftValue, rfl⟩
  cases right <;> exact True.intro

public theorem sub_zero (value : ENNReal) : sub value zero = value := by
  cases value with
  | top => rfl
  | finite underlying => exact congrArg finite (NNReal.sub_zero underlying)

public theorem zero_sub (value : ENNReal) : sub zero value = zero := by
  cases value with
  | top => rfl
  | finite underlying => exact congrArg finite (NNReal.zero_sub underlying)

public theorem sub_self (value : ENNReal) : sub value value = zero := by
  cases value with
  | top => rfl
  | finite underlying => exact congrArg finite (NNReal.sub_self underlying)

public theorem sub_add_cancel {left right : ENNReal}
    (included : le right left) : add (sub left right) right = left := by
  cases left with
  | top => cases right <;> rfl
  | finite leftValue =>
      cases right with
      | top => exact False.elim included
      | finite rightValue =>
          exact congrArg finite (NNReal.sub_add_cancel included)

public theorem add_sub_cancel_right {left right : ENNReal}
    (rightFinite : Finite right) : sub (add left right) right = left := by
  rcases exists_finite_of_finite rightFinite with ⟨rightValue, rfl⟩
  cases left with
  | top => rfl
  | finite leftValue =>
      exact congrArg finite (NNReal.add_sub_cancel_right leftValue rightValue)

public theorem add_sub_cancel_left {left right : ENNReal}
    (leftFinite : Finite left) : sub (add left right) left = right := by
  rw [add_comm]
  exact add_sub_cancel_right leftFinite

public theorem sub_eq_zero_iff_le {left right : ENNReal} :
    sub left right = zero ↔ le left right := by
  cases left with
  | top =>
      cases right with
      | top => exact ⟨fun _ => True.intro, fun _ => rfl⟩
      | finite underlying =>
          exact ⟨fun equal => False.elim (top_ne_finite NNReal.zero equal), False.elim⟩
  | finite leftValue =>
      cases right with
      | top => exact ⟨fun _ => True.intro, fun _ => rfl⟩
      | finite rightValue =>
          constructor
          · intro equal
            apply (NNReal.sub_eq_zero_iff_le).mp
            exact finite_injective equal
          · intro included
            exact congrArg finite ((NNReal.sub_eq_zero_iff_le).mpr included)

public theorem sub_le_self (left right : ENNReal) : le (sub left right) left := by
  cases left with
  | top => exact le_top _
  | finite leftValue =>
      cases right with
      | top => exact zero_le _
      | finite rightValue => exact NNReal.sub_le_self leftValue rightValue

public theorem sub_le_iff_le_add {left right upper : ENNReal} :
    le (sub left right) upper ↔ le left (add upper right) := by
  cases left with
  | top =>
      cases right with
      | top =>
          cases upper with
          | top => exact ⟨fun _ => True.intro, fun _ => True.intro⟩
          | finite upperValue =>
              exact ⟨fun _ => True.intro, fun _ => NNReal.zero_le upperValue⟩
      | finite rightValue =>
          cases upper with
          | top => exact ⟨fun _ => True.intro, fun _ => True.intro⟩
          | finite upperValue => exact ⟨False.elim, False.elim⟩
  | finite leftValue =>
      cases right with
      | top =>
          cases upper with
          | top => exact ⟨fun _ => True.intro, fun _ => True.intro⟩
          | finite upperValue =>
              exact ⟨fun _ => True.intro, fun _ => NNReal.zero_le upperValue⟩
      | finite rightValue =>
          cases upper with
          | top => exact ⟨fun _ => True.intro, fun _ => True.intro⟩
          | finite upperValue => exact NNReal.sub_le_iff_le_add

public theorem le_sub_add (left right : ENNReal) :
    le left (add (sub left right) right) :=
  sub_le_iff_le_add.mp (le_refl (sub left right))

public theorem le_sub_iff_add_le_of_finite_right {left middle right : ENNReal}
    (rightFinite : Finite right) (included : le right middle) :
    le left (sub middle right) ↔ le (add left right) middle := by
  rcases exists_finite_of_finite rightFinite with ⟨rightValue, rfl⟩
  cases left with
  | top =>
      cases middle with
      | top => exact ⟨fun _ => True.intro, fun _ => True.intro⟩
      | finite _ => exact ⟨False.elim, False.elim⟩
  | finite leftValue =>
      cases middle with
      | top => exact ⟨fun _ => True.intro, fun _ => True.intro⟩
      | finite middleValue => exact NNReal.le_sub_iff_add_le included

public theorem le_sub_of_add_le_of_finite_left {factor value upper : ENNReal}
    (factorFinite : Finite factor)
    (included : le (add factor value) upper) :
    le value (sub upper factor) := by
  have factorSum : le factor (add factor value) := by
    have shifted := add_le_add_left (zero_le value) factor
    rw [add_zero] at shifted
    exact shifted
  have factorUpper := le_trans factorSum included
  apply (le_sub_iff_add_le_of_finite_right factorFinite factorUpper).mpr
  rw [add_comm]
  exact included

/-- Strict comparison against an extended-nonnegative difference is equivalent
to strict addition without finiteness hypotheses. -/
public theorem lt_sub_iff_add_lt {threshold left right : ENNReal} :
    lt threshold (sub left right) ↔
      lt (add threshold right) left := by
  cases right with
  | top =>
      have difference : sub left top = zero := by
        cases left <;> rfl
      rw [difference, add_top]
      exact ⟨fun less => False.elim (less.2 (zero_le threshold)),
        fun less => False.elim (less.2 (le_top left))⟩
  | finite right =>
      constructor
      · intro less
        have differenceNonzero : sub left (finite right) ≠ zero := by
          intro differenceZero
          rw [differenceZero] at less
          exact less.2 (zero_le threshold)
        have notLeftRight : ¬le left (finite right) :=
          fun included => differenceNonzero (sub_eq_zero_iff_le.mpr included)
        have rightLeft := Or.resolve_right (le_total (finite right) left) notLeftRight
        refine ⟨(le_sub_iff_add_le_of_finite_right (show Finite (finite right) from True.intro) rightLeft).mp less.1, ?_⟩
        exact fun included => less.2 (sub_le_iff_le_add.mpr included)
      · intro less
        have rightSum : le (finite right)
            (add threshold (finite right)) := by
          simpa only [zero_add] using
            add_le_add_right (zero_le threshold) (finite right)
        have rightLeft := le_trans rightSum less.1
        refine ⟨(le_sub_iff_add_le_of_finite_right (show Finite (finite right) from True.intro) rightLeft).mpr less.1, ?_⟩
        exact fun included => less.2 (sub_le_iff_le_add.mp included)

/-- Subtraction is antitone in the subtracted argument without finiteness
hypotheses. -/
public theorem sub_le_sub_left {left right : ENNReal} (included : le left right) (factor : ENNReal) :
    le (sub factor right) (sub factor left) :=
  sub_le_iff_le_add.mpr (le_trans (le_sub_add factor left)
    (add_le_add_left included (sub factor left)))

public theorem add_supremum (factor : ENNReal) {set : ENNReal → Prop}
    (nonempty : ∃ value, set value) :
    add factor (supremum set) =
      supremum (image (add factor) set) := by
  cases factor with
  | top =>
      rcases nonempty with ⟨value, member⟩
      exact (supremum_eq_top_of_member
        (set := image (add top) set) ⟨value, member, rfl⟩).symm
  | finite factorValue =>
      apply le_antisymm
      · rcases nonempty with ⟨witness, witnessMember⟩
        have factorUpper : le (finite factorValue)
            (supremum (image (add (finite factorValue)) set)) := by
          have factorWitness : le (finite factorValue)
              (add (finite factorValue) witness) := by
            have shifted := add_le_add_left (zero_le witness) (finite factorValue)
            rw [add_zero] at shifted
            exact shifted
          exact le_trans factorWitness
            (le_supremum ⟨witness, witnessMember, rfl⟩)
        have setBound : ∀ value, set value →
            le value (sub (supremum (image (add (finite factorValue)) set))
              (finite factorValue)) := by
          intro value member
          exact le_sub_of_add_le_of_finite_left True.intro
            (le_supremum ⟨value, member, rfl⟩)
        have supremumBound := supremum_le setBound
        calc
          le (add (finite factorValue) (supremum set))
              (add (finite factorValue)
                (sub (supremum (image (add (finite factorValue)) set))
                  (finite factorValue))) :=
            add_le_add_left supremumBound _
          _ = add
              (sub (supremum (image (add (finite factorValue)) set))
                (finite factorValue)) (finite factorValue) :=
            add_comm _ _
          _ = supremum (image (add (finite factorValue)) set) :=
            sub_add_cancel factorUpper
      · apply supremum_le
        intro result member
        rcases member with ⟨value, valueMember, rfl⟩
        exact add_le_add_left (le_supremum valueMember) (finite factorValue)

public theorem add_iSup (factor : ENNReal) (values : Nat → ENNReal) :
    add factor (iSup values) = iSup (fun index => add factor (values index)) := by
  unfold iSup
  rw [add_supremum factor (set := fun value => ∃ index, value = values index)
    ⟨values 0, 0, rfl⟩]
  apply congrArg supremum
  funext result
  apply propext
  constructor
  · rintro ⟨value, ⟨index, rfl⟩, rfl⟩
    exact ⟨index, rfl⟩
  · rintro ⟨index, rfl⟩
    exact ⟨values index, ⟨index, rfl⟩, rfl⟩

end Problib.Real.ENNReal
