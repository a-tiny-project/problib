module

public import Problib.Real.Inverse

set_option autoImplicit false

namespace Problib.Real

local notation "SignedReal" => Construction.Dedekind.selection.Carrier

@[expose] public def NNReal :=
  { value : SignedReal //
    Construction.Dedekind.le Construction.Dedekind.zero value }

namespace NNReal

@[expose] public def toReal (value : NNReal) : SignedReal :=
  value.val

public theorem ext {left right : NNReal}
    (equal : toReal left = toReal right) : left = right := by
  cases left
  cases right
  cases equal
  rfl

@[expose] public def le (left right : NNReal) : Prop :=
  Construction.Dedekind.le (toReal left) (toReal right)

@[expose] public def lt (left right : NNReal) : Prop :=
  le left right ∧ ¬le right left

@[expose] public def zero : NNReal :=
  ⟨Construction.Dedekind.zero, Construction.Dedekind.le_refl Construction.Dedekind.zero⟩

@[expose] public noncomputable def one : NNReal :=
  ⟨Construction.Dedekind.one, Construction.Dedekind.one_nonnegative⟩

@[expose] public def add (left right : NNReal) : NNReal :=
  ⟨Construction.Dedekind.add (toReal left) (toReal right), by
    have rightIncluded :=
      (Construction.Dedekind.add_le_add_left_iff
        (left := Construction.Dedekind.zero)
        (right := toReal right) (shift := toReal left)).mpr right.property
    have leftIncluded : Construction.Dedekind.le (toReal left)
        (Construction.Dedekind.add (toReal left) (toReal right)) := by
      simpa only [Construction.Dedekind.add_zero] using rightIncluded
    exact Construction.Dedekind.le_trans left.property leftIncluded⟩

@[expose] public noncomputable def mul (left right : NNReal) : NNReal :=
  ⟨Construction.Dedekind.mul (toReal left) (toReal right),
    Construction.Dedekind.mul_nonnegative left.property right.property⟩

@[expose] public noncomputable def sub (left right : NNReal) : NNReal := by
  classical
  exact if included : le right left then
    ⟨Construction.Dedekind.sub (toReal left) (toReal right),
      Construction.Dedekind.additive.orderedGroup.sub_nonnegative_of_le included⟩
  else
    zero

@[expose] public noncomputable def ofReal (value : SignedReal) : NNReal := by
  classical
  exact if nonnegative : Construction.Dedekind.le Construction.Dedekind.zero value then
    ⟨value, nonnegative⟩
  else
    zero

public theorem toReal_zero : toReal zero = Construction.Dedekind.zero :=
  rfl

public theorem toReal_one : toReal one = Construction.Dedekind.one :=
  rfl

public theorem toReal_add (left right : NNReal) :
    toReal (add left right) =
      Construction.Dedekind.add (toReal left) (toReal right) :=
  rfl

public theorem toReal_mul (left right : NNReal) :
    toReal (mul left right) =
      Construction.Dedekind.mul (toReal left) (toReal right) :=
  rfl

public theorem le_refl (value : NNReal) : le value value :=
  Construction.Dedekind.le_refl (toReal value)

public theorem le_trans {left middle right : NNReal}
    (leftMiddle : le left middle) (middleRight : le middle right) :
    le left right :=
  Construction.Dedekind.le_trans leftMiddle middleRight

public theorem le_antisymm {left right : NNReal}
    (leftRight : le left right) (rightLeft : le right left) :
    left = right :=
  ext (Construction.Dedekind.le_antisymm leftRight rightLeft)

public theorem le_total (left right : NNReal) :
    le left right ∨ le right left :=
  Construction.Dedekind.le_total (toReal left) (toReal right)

public def linearOrder : Problib.Algebra.LinearOrderLaws NNReal where
  le := le
  refl := le_refl
  trans := le_trans
  antisymm := le_antisymm
  total := le_total

public theorem lt_irrefl (value : NNReal) : ¬lt value value := by
  intro strict
  exact strict.right strict.left

public theorem lt_trans {left middle right : NNReal}
    (leftMiddle : lt left middle) (middleRight : lt middle right) :
    lt left right := by
  constructor
  · exact le_trans leftMiddle.left middleRight.left
  · intro rightLeft
    exact leftMiddle.right (le_trans middleRight.left rightLeft)

public theorem lt_of_le_of_lt {left middle right : NNReal}
    (leftMiddle : le left middle) (middleRight : lt middle right) :
    lt left right := by
  constructor
  · exact le_trans leftMiddle middleRight.left
  · intro rightLeft
    exact middleRight.right (le_trans rightLeft leftMiddle)

public theorem lt_of_lt_of_le {left middle right : NNReal}
    (leftMiddle : lt left middle) (middleRight : le middle right) :
    lt left right := by
  constructor
  · exact le_trans leftMiddle.left middleRight
  · intro rightLeft
    exact leftMiddle.right (le_trans middleRight rightLeft)

public theorem zero_le (value : NNReal) : le zero value :=
  value.property

public theorem zero_lt_iff_ne_zero (value : NNReal) :
    lt zero value ↔ value ≠ zero := by
  constructor
  · intro positive equal
    subst value
    exact lt_irrefl zero positive
  · intro nonzero
    refine ⟨zero_le value, ?_⟩
    intro nonpositive
    exact nonzero (le_antisymm nonpositive (zero_le value))

public theorem eq_zero_or_zero_lt (value : NNReal) :
    value = zero ∨ lt zero value := by
  by_cases equal : value = zero
  · exact Or.inl equal
  · exact Or.inr ((zero_lt_iff_ne_zero value).mpr equal)

public theorem add_comm (left right : NNReal) :
    add left right = add right left := by
  apply ext
  rw [toReal_add, toReal_add]
  exact Construction.Dedekind.add_comm (toReal left) (toReal right)

public theorem add_assoc (left middle right : NNReal) :
    add (add left middle) right = add left (add middle right) := by
  apply ext
  rw [toReal_add, toReal_add, toReal_add, toReal_add]
  exact Construction.Dedekind.add_assoc
    (toReal left) (toReal middle) (toReal right)

public theorem add_zero (value : NNReal) : add value zero = value := by
  apply ext
  rw [toReal_add, toReal_zero]
  exact Construction.Dedekind.add_zero (toReal value)

public theorem zero_add (value : NNReal) : add zero value = value := by
  rw [add_comm, add_zero]

public theorem add_left_cancel {left first second : NNReal}
    (equal : add left first = add left second) : first = second := by
  apply ext
  apply Construction.Dedekind.add_left_cancel
  simpa only [toReal_add] using congrArg toReal equal

public theorem add_right_cancel {right first second : NNReal}
    (equal : add first right = add second right) : first = second := by
  apply ext
  apply Construction.Dedekind.add_right_cancel
  simpa only [toReal_add] using congrArg toReal equal

public theorem mul_comm (left right : NNReal) :
    mul left right = mul right left := by
  apply ext
  rw [toReal_mul, toReal_mul]
  exact Construction.Dedekind.mul_comm (toReal left) (toReal right)

public theorem mul_assoc (left middle right : NNReal) :
    mul (mul left middle) right = mul left (mul middle right) := by
  apply ext
  rw [toReal_mul, toReal_mul, toReal_mul, toReal_mul]
  exact Construction.Dedekind.mul_assoc
    (toReal left) (toReal middle) (toReal right)

public theorem mul_one (value : NNReal) : mul value one = value := by
  apply ext
  rw [toReal_mul, toReal_one]
  exact Construction.Dedekind.mul_one (toReal value)

public theorem one_mul (value : NNReal) : mul one value = value := by
  rw [mul_comm, mul_one]

public theorem mul_add (left middle right : NNReal) :
    mul left (add middle right) =
      add (mul left middle) (mul left right) := by
  apply ext
  rw [toReal_mul, toReal_add, toReal_add, toReal_mul, toReal_mul]
  exact Construction.Dedekind.mul_add
    (toReal left) (toReal middle) (toReal right)

public theorem add_mul (left middle right : NNReal) :
    mul (add left middle) right =
      add (mul left right) (mul middle right) := by
  rw [mul_comm (add left middle), mul_add,
    mul_comm right left, mul_comm right middle]

public theorem mul_zero (value : NNReal) : mul value zero = zero := by
  apply ext
  change Construction.Dedekind.mul
    (toReal value) Construction.Dedekind.zero = Construction.Dedekind.zero
  exact Construction.Dedekind.multiplicativeSelection.ring.mul_zero (toReal value)

public theorem zero_mul (value : NNReal) : mul zero value = zero := by
  rw [mul_comm, mul_zero]

public noncomputable def semiring :
    Problib.Algebra.CommutativeSemiringLaws NNReal where
  additive := {
    zero := zero
    add := add
    add_comm := add_comm
    add_assoc := add_assoc
    add_zero := add_zero
  }
  multiplicative := {
    one := one
    mul := mul
    mul_comm := mul_comm
    mul_assoc := mul_assoc
    mul_one := mul_one
  }
  zero_mul := zero_mul
  mul_add := mul_add

public theorem add_le_add {firstLeft firstRight secondLeft secondRight : NNReal}
    (firstIncluded : le firstLeft firstRight)
    (secondIncluded : le secondLeft secondRight) :
    le (add firstLeft secondLeft) (add firstRight secondRight) := by
  change Construction.Dedekind.le
    (Construction.Dedekind.add (toReal firstLeft) (toReal secondLeft))
    (Construction.Dedekind.add (toReal firstRight) (toReal secondRight))
  exact Construction.Dedekind.le_trans
    ((Construction.Dedekind.add_le_add_right_iff).mpr firstIncluded)
    ((Construction.Dedekind.add_le_add_left_iff).mpr secondIncluded)

public theorem add_le_add_right {left right : NNReal}
    (included : le left right) (shift : NNReal) :
    le (add left shift) (add right shift) := by
  change Construction.Dedekind.le
    (Construction.Dedekind.add (toReal left) (toReal shift))
    (Construction.Dedekind.add (toReal right) (toReal shift))
  exact (Construction.Dedekind.add_le_add_right_iff).mpr included

public theorem add_le_add_left {left right : NNReal}
    (included : le left right) (shift : NNReal) :
    le (add shift left) (add shift right) := by
  change Construction.Dedekind.le
    (Construction.Dedekind.add (toReal shift) (toReal left))
    (Construction.Dedekind.add (toReal shift) (toReal right))
  exact (Construction.Dedekind.add_le_add_left_iff).mpr included

public theorem add_le_add_right_iff {left right shift : NNReal} :
    le (add left shift) (add right shift) ↔ le left right := by
  change Construction.Dedekind.le
      (Construction.Dedekind.add (toReal left) (toReal shift))
      (Construction.Dedekind.add (toReal right) (toReal shift)) ↔
    Construction.Dedekind.le (toReal left) (toReal right)
  exact Construction.Dedekind.add_le_add_right_iff

public theorem add_le_add_left_iff {left right shift : NNReal} :
    le (add shift left) (add shift right) ↔ le left right := by
  change Construction.Dedekind.le
      (Construction.Dedekind.add (toReal shift) (toReal left))
      (Construction.Dedekind.add (toReal shift) (toReal right)) ↔
    Construction.Dedekind.le (toReal left) (toReal right)
  exact Construction.Dedekind.add_le_add_left_iff

public theorem mul_le_mul {firstLeft firstRight secondLeft secondRight : NNReal}
    (firstIncluded : le firstLeft firstRight)
    (secondIncluded : le secondLeft secondRight) :
    le (mul firstLeft secondLeft) (mul firstRight secondRight) := by
  change Construction.Dedekind.le
    (Construction.Dedekind.mul (toReal firstLeft) (toReal secondLeft))
    (Construction.Dedekind.mul (toReal firstRight) (toReal secondRight))
  exact Construction.Dedekind.le_trans
    (Construction.Dedekind.mul_le_mul_nonnegative_right firstIncluded secondLeft.property)
    (Construction.Dedekind.mul_le_mul_nonnegative_left secondIncluded firstRight.property)

public theorem mul_le_mul_right {left right : NNReal}
    (included : le left right) (factor : NNReal) :
    le (mul left factor) (mul right factor) := by
  change Construction.Dedekind.le
    (Construction.Dedekind.mul (toReal left) (toReal factor))
    (Construction.Dedekind.mul (toReal right) (toReal factor))
  exact Construction.Dedekind.mul_le_mul_nonnegative_right included factor.property

public theorem mul_le_mul_left {left right : NNReal}
    (included : le left right) (factor : NNReal) :
    le (mul factor left) (mul factor right) := by
  change Construction.Dedekind.le
    (Construction.Dedekind.mul (toReal factor) (toReal left))
    (Construction.Dedekind.mul (toReal factor) (toReal right))
  exact Construction.Dedekind.mul_le_mul_nonnegative_left included factor.property

public theorem mul_eq_zero_iff {left right : NNReal} :
    mul left right = zero ↔ left = zero ∨ right = zero := by
  constructor
  · intro equal
    have productZero : Construction.Dedekind.mul
        (toReal left) (toReal right) = Construction.Dedekind.zero := by
      simpa only [toReal_mul, toReal_zero] using congrArg toReal equal
    rcases Construction.Dedekind.mul_eq_zero_iff.mp productZero with
      leftZero | rightZero
    · exact Or.inl (ext leftZero)
    · exact Or.inr (ext rightZero)
  · rintro (leftZero | rightZero)
    · rw [leftZero, zero_mul]
    · rw [rightZero, mul_zero]

end NNReal

end Problib.Real
