module

public import Foundations.Real.Extended.Indexed
public import Foundations.Real.Extended.Lattice

namespace Foundations.Real.ENNReal

set_option autoImplicit false

@[expose] public def add : ENNReal → ENNReal → ENNReal
  | .finite left, .finite right => .finite (NNReal.add left right)
  | _, _ => top

/-- The sum of two finite extended-nonnegative values is finite. -/
public theorem addFinite {left right : ENNReal}
    (leftFinite : Finite left) (rightFinite : Finite right) :
    Finite (add left right) := by
  rcases existsFiniteOfFinite leftFinite with ⟨leftValue, rfl⟩
  rcases existsFiniteOfFinite rightFinite with ⟨rightValue, rfl⟩
  exact True.intro

public theorem addComm (left right : ENNReal) :
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
          exact congrArg finite (NNReal.addComm leftValue rightValue)

public theorem addAssoc (left middle right : ENNReal) :
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
                (NNReal.addAssoc leftValue middleValue rightValue)

public theorem addLeftComm (first second third : ENNReal) :
    add first (add second third) = add second (add first third) := by
  rw [← addAssoc first second third, addComm first second, addAssoc]

public theorem addRightComm (first second third : ENNReal) :
    add (add first second) third = add (add first third) second := by
  rw [addAssoc first second third, addComm second third, ← addAssoc]

public theorem addAddComm (first second third fourth : ENNReal) :
    add (add first second) (add third fourth) =
      add (add first third) (add second fourth) := by
  rw [addAssoc first second (add third fourth),
    ← addAssoc second third fourth, addComm second third,
    addAssoc third second fourth, ← addAssoc first third (add second fourth)]

public theorem addZero (value : ENNReal) : add value zero = value := by
  cases value with
  | top => rfl
  | finite underlying => exact congrArg finite (NNReal.addZero underlying)

public theorem zeroAdd (value : ENNReal) : add zero value = value := by
  rw [addComm, addZero]

public theorem addTop (value : ENNReal) : add value top = top := by
  cases value <;> rfl

public theorem topAdd (value : ENNReal) : add top value = top := by
  rw [addComm, addTop]

public def additiveLaws :
    Foundations.Algebra.AdditiveCommutativeMonoidLaws ENNReal where
  zero := zero
  add := add
  add_comm := addComm
  add_assoc := addAssoc
  add_zero := addZero

public theorem addLeAddRight {left right : ENNReal}
    (included : le left right) (shift : ENNReal) :
    le (add left shift) (add right shift) := by
  cases shift with
  | top =>
      rw [addTop, addTop]
      exact leRefl top
  | finite shiftValue =>
      cases left with
      | top =>
          cases right with
          | top => exact leRefl top
          | finite _ => exact False.elim included
      | finite leftValue =>
          cases right with
          | top => exact leTop _
          | finite rightValue =>
              exact NNReal.addLeAddRight included shiftValue

public theorem addLeAddLeft {left right : ENNReal}
    (included : le left right) (shift : ENNReal) :
    le (add shift left) (add shift right) := by
  rw [addComm shift left, addComm shift right]
  exact addLeAddRight included shift

public theorem addLeAdd {firstLeft firstRight secondLeft secondRight : ENNReal}
    (firstIncluded : le firstLeft firstRight)
    (secondIncluded : le secondLeft secondRight) :
    le (add firstLeft secondLeft) (add firstRight secondRight) :=
  leTrans (addLeAddRight firstIncluded secondLeft)
    (addLeAddLeft secondIncluded firstRight)

public theorem addEqZeroIff {left right : ENNReal} :
    add left right = zero ↔ left = zero ∧ right = zero := by
  constructor
  · intro equal
    have leftIncluded : le left (add left right) := by
      have shifted := addLeAddLeft (zeroLe right) left
      rw [addZero] at shifted
      exact shifted
    have rightIncluded : le right (add left right) := by
      have shifted := addLeAddRight (zeroLe left) right
      rw [zeroAdd] at shifted
      exact shifted
    rw [equal] at leftIncluded rightIncluded
    exact ⟨eqZeroOfLeZero leftIncluded, eqZeroOfLeZero rightIncluded⟩
  · rintro ⟨rfl, rfl⟩
    exact zeroAdd zero

public theorem addLeftCancelOfFinite {factor left right : ENNReal}
    (factorFinite : Finite factor)
    (equal : add factor left = add factor right) : left = right := by
  rcases existsFiniteOfFinite factorFinite with ⟨factorValue, rfl⟩
  cases left with
  | top =>
      cases right with
      | top => rfl
      | finite rightValue =>
          exact False.elim (topNeFinite (NNReal.add factorValue rightValue) equal)
  | finite leftValue =>
      cases right with
      | top =>
          exact False.elim (finiteNeTop (NNReal.add factorValue leftValue) equal)
      | finite rightValue =>
          apply congrArg finite
          apply NNReal.addLeftCancel
          exact finiteInjective equal

public theorem addRightCancelOfFinite {factor left right : ENNReal}
    (factorFinite : Finite factor)
    (equal : add left factor = add right factor) : left = right := by
  apply addLeftCancelOfFinite factorFinite
  rw [addComm factor left, addComm factor right]
  exact equal

public theorem leOfAddLeAddLeftOfFinite {factor left right : ENNReal}
    (factorFinite : Finite factor)
    (included : le (add factor left) (add factor right)) : le left right := by
  rcases existsFiniteOfFinite factorFinite with ⟨factorValue, rfl⟩
  cases left with
  | top =>
      cases right with
      | top => exact leRefl top
      | finite _ => exact False.elim included
  | finite leftValue =>
      cases right with
      | top => exact leTop _
      | finite rightValue =>
          exact (NNReal.addLeAddLeftIff).mp included

public theorem leOfAddLeAddRightOfFinite {factor left right : ENNReal}
    (factorFinite : Finite factor)
    (included : le (add left factor) (add right factor)) : le left right := by
  apply leOfAddLeAddLeftOfFinite factorFinite
  rw [addComm factor left, addComm factor right]
  exact included

@[expose] public noncomputable def sub : ENNReal → ENNReal → ENNReal
  | .finite left, .finite right => .finite (NNReal.sub left right)
  | .top, .finite _ => top
  | .finite _, .top => zero
  | .top, .top => zero

public theorem subFiniteOfFiniteLeft {left right : ENNReal}
    (leftFinite : Finite left) : Finite (sub left right) := by
  rcases existsFiniteOfFinite leftFinite with ⟨leftValue, rfl⟩
  cases right <;> exact True.intro

public theorem subZero (value : ENNReal) : sub value zero = value := by
  cases value with
  | top => rfl
  | finite underlying => exact congrArg finite (NNReal.subZero underlying)

public theorem zeroSub (value : ENNReal) : sub zero value = zero := by
  cases value with
  | top => rfl
  | finite underlying => exact congrArg finite (NNReal.zeroSub underlying)

public theorem subSelf (value : ENNReal) : sub value value = zero := by
  cases value with
  | top => rfl
  | finite underlying => exact congrArg finite (NNReal.subSelf underlying)

public theorem subAddCancel {left right : ENNReal}
    (included : le right left) : add (sub left right) right = left := by
  cases left with
  | top => cases right <;> rfl
  | finite leftValue =>
      cases right with
      | top => exact False.elim included
      | finite rightValue =>
          exact congrArg finite (NNReal.subAddCancel included)

public theorem addSubCancelRight {left right : ENNReal}
    (rightFinite : Finite right) : sub (add left right) right = left := by
  rcases existsFiniteOfFinite rightFinite with ⟨rightValue, rfl⟩
  cases left with
  | top => rfl
  | finite leftValue =>
      exact congrArg finite (NNReal.addSubCancelRight leftValue rightValue)

public theorem addSubCancelLeft {left right : ENNReal}
    (leftFinite : Finite left) : sub (add left right) left = right := by
  rw [addComm]
  exact addSubCancelRight leftFinite

public theorem subEqZeroIffLe {left right : ENNReal} :
    sub left right = zero ↔ le left right := by
  cases left with
  | top =>
      cases right with
      | top => exact ⟨fun _ => True.intro, fun _ => rfl⟩
      | finite underlying =>
          exact ⟨fun equal => False.elim (topNeFinite NNReal.zero equal), False.elim⟩
  | finite leftValue =>
      cases right with
      | top => exact ⟨fun _ => True.intro, fun _ => rfl⟩
      | finite rightValue =>
          constructor
          · intro equal
            apply (NNReal.subEqZeroIffLe).mp
            exact finiteInjective equal
          · intro included
            exact congrArg finite ((NNReal.subEqZeroIffLe).mpr included)

public theorem subLeSelf (left right : ENNReal) : le (sub left right) left := by
  cases left with
  | top => exact leTop _
  | finite leftValue =>
      cases right with
      | top => exact zeroLe _
      | finite rightValue => exact NNReal.subLeSelf leftValue rightValue

public theorem subLeIffLeAdd {left right upper : ENNReal} :
    le (sub left right) upper ↔ le left (add upper right) := by
  cases left with
  | top =>
      cases right with
      | top =>
          cases upper with
          | top => exact ⟨fun _ => True.intro, fun _ => True.intro⟩
          | finite upperValue =>
              exact ⟨fun _ => True.intro, fun _ => NNReal.zeroLe upperValue⟩
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
              exact ⟨fun _ => True.intro, fun _ => NNReal.zeroLe upperValue⟩
      | finite rightValue =>
          cases upper with
          | top => exact ⟨fun _ => True.intro, fun _ => True.intro⟩
          | finite upperValue => exact NNReal.subLeIffLeAdd

public theorem leSubAdd (left right : ENNReal) :
    le left (add (sub left right) right) :=
  subLeIffLeAdd.mp (leRefl (sub left right))

public theorem leSubIffAddLeOfFiniteRight {left middle right : ENNReal}
    (rightFinite : Finite right) (included : le right middle) :
    le left (sub middle right) ↔ le (add left right) middle := by
  rcases existsFiniteOfFinite rightFinite with ⟨rightValue, rfl⟩
  cases left with
  | top =>
      cases middle with
      | top => exact ⟨fun _ => True.intro, fun _ => True.intro⟩
      | finite _ => exact ⟨False.elim, False.elim⟩
  | finite leftValue =>
      cases middle with
      | top => exact ⟨fun _ => True.intro, fun _ => True.intro⟩
      | finite middleValue => exact NNReal.leSubIffAddLe included

public theorem leSubOfAddLeOfFiniteLeft {factor value upper : ENNReal}
    (factorFinite : Finite factor)
    (included : le (add factor value) upper) :
    le value (sub upper factor) := by
  have factorSum : le factor (add factor value) := by
    have shifted := addLeAddLeft (zeroLe value) factor
    rw [addZero] at shifted
    exact shifted
  have factorUpper := leTrans factorSum included
  apply (leSubIffAddLeOfFiniteRight factorFinite factorUpper).mpr
  rw [addComm]
  exact included

/-- Strict comparison against an extended-nonnegative difference is equivalent
to strict addition without finiteness hypotheses. -/
public theorem ltSubIffAddLt {threshold left right : ENNReal} :
    lt threshold (sub left right) ↔
      lt (add threshold right) left := by
  cases right with
  | top =>
      have difference : sub left top = zero := by
        cases left <;> rfl
      rw [difference, addTop]
      exact ⟨fun less => False.elim (less.2 (zeroLe threshold)),
        fun less => False.elim (less.2 (leTop left))⟩
  | finite right =>
      constructor
      · intro less
        have differenceNonzero : sub left (finite right) ≠ zero := by
          intro differenceZero
          rw [differenceZero] at less
          exact less.2 (zeroLe threshold)
        have notLeftRight : ¬le left (finite right) :=
          fun included => differenceNonzero (subEqZeroIffLe.mpr included)
        have rightLeft := Or.resolve_right (leTotal (finite right) left) notLeftRight
        refine ⟨(leSubIffAddLeOfFiniteRight (show Finite (finite right) from True.intro) rightLeft).mp less.1, ?_⟩
        exact fun included => less.2 (subLeIffLeAdd.mpr included)
      · intro less
        have rightSum : le (finite right)
            (add threshold (finite right)) := by
          simpa only [zeroAdd] using
            addLeAddRight (zeroLe threshold) (finite right)
        have rightLeft := leTrans rightSum less.1
        refine ⟨(leSubIffAddLeOfFiniteRight (show Finite (finite right) from True.intro) rightLeft).mpr less.1, ?_⟩
        exact fun included => less.2 (subLeIffLeAdd.mp included)

/-- Subtraction is antitone in the subtracted argument without finiteness
hypotheses. -/
public theorem subLeSubLeft {left right : ENNReal} (included : le left right) (factor : ENNReal) :
    le (sub factor right) (sub factor left) :=
  subLeIffLeAdd.mpr (leTrans (leSubAdd factor left)
    (addLeAddLeft included (sub factor left)))

public theorem addSupremum (factor : ENNReal) {set : ENNReal → Prop}
    (nonempty : ∃ value, set value) :
    add factor (supremum set) =
      supremum (image (add factor) set) := by
  cases factor with
  | top =>
      rcases nonempty with ⟨value, member⟩
      exact (supremumEqTopOfMember
        (set := image (add top) set) ⟨value, member, rfl⟩).symm
  | finite factorValue =>
      apply leAntisymm
      · rcases nonempty with ⟨witness, witnessMember⟩
        have factorUpper : le (finite factorValue)
            (supremum (image (add (finite factorValue)) set)) := by
          have factorWitness : le (finite factorValue)
              (add (finite factorValue) witness) := by
            have shifted := addLeAddLeft (zeroLe witness) (finite factorValue)
            rw [addZero] at shifted
            exact shifted
          exact leTrans factorWitness
            (leSupremum ⟨witness, witnessMember, rfl⟩)
        have setBound : ∀ value, set value →
            le value (sub (supremum (image (add (finite factorValue)) set))
              (finite factorValue)) := by
          intro value member
          exact leSubOfAddLeOfFiniteLeft True.intro
            (leSupremum ⟨value, member, rfl⟩)
        have supremumBound := supremumLe setBound
        calc
          le (add (finite factorValue) (supremum set))
              (add (finite factorValue)
                (sub (supremum (image (add (finite factorValue)) set))
                  (finite factorValue))) :=
            addLeAddLeft supremumBound _
          _ = add
              (sub (supremum (image (add (finite factorValue)) set))
                (finite factorValue)) (finite factorValue) :=
            addComm _ _
          _ = supremum (image (add (finite factorValue)) set) :=
            subAddCancel factorUpper
      · apply supremumLe
        intro result member
        rcases member with ⟨value, valueMember, rfl⟩
        exact addLeAddLeft (leSupremum valueMember) (finite factorValue)

public theorem addISup (factor : ENNReal) (values : Nat → ENNReal) :
    add factor (iSup values) = iSup (fun index => add factor (values index)) := by
  unfold iSup
  rw [addSupremum factor (set := fun value => ∃ index, value = values index)
    ⟨values 0, 0, rfl⟩]
  apply congrArg supremum
  funext result
  apply propext
  constructor
  · rintro ⟨value, ⟨index, rfl⟩, rfl⟩
    exact ⟨index, rfl⟩
  · rintro ⟨index, rfl⟩
    exact ⟨values index, ⟨index, rfl⟩, rfl⟩

end Foundations.Real.ENNReal
