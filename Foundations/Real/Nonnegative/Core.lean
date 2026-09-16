module

public import Foundations.Real.Inverse

set_option autoImplicit false

namespace Foundations.Real

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
  ⟨Construction.Dedekind.zero, Construction.Dedekind.leRefl Construction.Dedekind.zero⟩

@[expose] public noncomputable def one : NNReal :=
  ⟨Construction.Dedekind.one, Construction.Dedekind.oneNonnegative⟩

@[expose] public def add (left right : NNReal) : NNReal :=
  ⟨Construction.Dedekind.add (toReal left) (toReal right), by
    have rightIncluded :=
      (Construction.Dedekind.addLeAddLeftIff
        (left := Construction.Dedekind.zero)
        (right := toReal right) (shift := toReal left)).mpr right.property
    have leftIncluded : Construction.Dedekind.le (toReal left)
        (Construction.Dedekind.add (toReal left) (toReal right)) := by
      simpa only [Construction.Dedekind.addZero] using rightIncluded
    exact Construction.Dedekind.leTrans left.property leftIncluded⟩

@[expose] public noncomputable def mul (left right : NNReal) : NNReal :=
  ⟨Construction.Dedekind.mul (toReal left) (toReal right),
    Construction.Dedekind.mulNonnegative left.property right.property⟩

@[expose] public noncomputable def sub (left right : NNReal) : NNReal := by
  classical
  exact if included : le right left then
    ⟨Construction.Dedekind.sub (toReal left) (toReal right),
      Construction.Dedekind.additive.orderedGroup.subNonnegativeOfLe included⟩
  else
    zero

@[expose] public noncomputable def ofReal (value : SignedReal) : NNReal := by
  classical
  exact if nonnegative : Construction.Dedekind.le Construction.Dedekind.zero value then
    ⟨value, nonnegative⟩
  else
    zero

public theorem toRealZero : toReal zero = Construction.Dedekind.zero :=
  rfl

public theorem toRealOne : toReal one = Construction.Dedekind.one :=
  rfl

public theorem toRealAdd (left right : NNReal) :
    toReal (add left right) =
      Construction.Dedekind.add (toReal left) (toReal right) :=
  rfl

public theorem toRealMul (left right : NNReal) :
    toReal (mul left right) =
      Construction.Dedekind.mul (toReal left) (toReal right) :=
  rfl

public theorem leRefl (value : NNReal) : le value value :=
  Construction.Dedekind.leRefl (toReal value)

public theorem leTrans {left middle right : NNReal}
    (leftMiddle : le left middle) (middleRight : le middle right) :
    le left right :=
  Construction.Dedekind.leTrans leftMiddle middleRight

public theorem leAntisymm {left right : NNReal}
    (leftRight : le left right) (rightLeft : le right left) :
    left = right :=
  ext (Construction.Dedekind.leAntisymm leftRight rightLeft)

public theorem leTotal (left right : NNReal) :
    le left right ∨ le right left :=
  Construction.Dedekind.leTotal (toReal left) (toReal right)

public def linearOrder : Foundations.Algebra.LinearOrderLaws NNReal where
  le := le
  refl := leRefl
  trans := leTrans
  antisymm := leAntisymm
  total := leTotal

public theorem ltIrrefl (value : NNReal) : ¬lt value value := by
  intro strict
  exact strict.right strict.left

public theorem ltTrans {left middle right : NNReal}
    (leftMiddle : lt left middle) (middleRight : lt middle right) :
    lt left right := by
  constructor
  · exact leTrans leftMiddle.left middleRight.left
  · intro rightLeft
    exact leftMiddle.right (leTrans middleRight.left rightLeft)

public theorem ltOfLeOfLt {left middle right : NNReal}
    (leftMiddle : le left middle) (middleRight : lt middle right) :
    lt left right := by
  constructor
  · exact leTrans leftMiddle middleRight.left
  · intro rightLeft
    exact middleRight.right (leTrans rightLeft leftMiddle)

public theorem ltOfLtOfLe {left middle right : NNReal}
    (leftMiddle : lt left middle) (middleRight : le middle right) :
    lt left right := by
  constructor
  · exact leTrans leftMiddle.left middleRight
  · intro rightLeft
    exact leftMiddle.right (leTrans middleRight rightLeft)

public theorem zeroLe (value : NNReal) : le zero value :=
  value.property

public theorem zeroLtIffNeZero (value : NNReal) :
    lt zero value ↔ value ≠ zero := by
  constructor
  · intro positive equal
    subst value
    exact ltIrrefl zero positive
  · intro nonzero
    refine ⟨zeroLe value, ?_⟩
    intro nonpositive
    exact nonzero (leAntisymm nonpositive (zeroLe value))

public theorem eqZeroOrZeroLt (value : NNReal) :
    value = zero ∨ lt zero value := by
  by_cases equal : value = zero
  · exact Or.inl equal
  · exact Or.inr ((zeroLtIffNeZero value).mpr equal)

public theorem addComm (left right : NNReal) :
    add left right = add right left := by
  apply ext
  rw [toRealAdd, toRealAdd]
  exact Construction.Dedekind.addComm (toReal left) (toReal right)

public theorem addAssoc (left middle right : NNReal) :
    add (add left middle) right = add left (add middle right) := by
  apply ext
  rw [toRealAdd, toRealAdd, toRealAdd, toRealAdd]
  exact Construction.Dedekind.addAssoc
    (toReal left) (toReal middle) (toReal right)

public theorem addZero (value : NNReal) : add value zero = value := by
  apply ext
  rw [toRealAdd, toRealZero]
  exact Construction.Dedekind.addZero (toReal value)

public theorem zeroAdd (value : NNReal) : add zero value = value := by
  rw [addComm, addZero]

public theorem addLeftCancel {left first second : NNReal}
    (equal : add left first = add left second) : first = second := by
  apply ext
  apply Construction.Dedekind.addLeftCancel
  simpa only [toRealAdd] using congrArg toReal equal

public theorem addRightCancel {right first second : NNReal}
    (equal : add first right = add second right) : first = second := by
  apply ext
  apply Construction.Dedekind.addRightCancel
  simpa only [toRealAdd] using congrArg toReal equal

public theorem mulComm (left right : NNReal) :
    mul left right = mul right left := by
  apply ext
  rw [toRealMul, toRealMul]
  exact Construction.Dedekind.mulComm (toReal left) (toReal right)

public theorem mulAssoc (left middle right : NNReal) :
    mul (mul left middle) right = mul left (mul middle right) := by
  apply ext
  rw [toRealMul, toRealMul, toRealMul, toRealMul]
  exact Construction.Dedekind.mulAssoc
    (toReal left) (toReal middle) (toReal right)

public theorem mulOne (value : NNReal) : mul value one = value := by
  apply ext
  rw [toRealMul, toRealOne]
  exact Construction.Dedekind.mulOne (toReal value)

public theorem oneMul (value : NNReal) : mul one value = value := by
  rw [mulComm, mulOne]

public theorem mulAdd (left middle right : NNReal) :
    mul left (add middle right) =
      add (mul left middle) (mul left right) := by
  apply ext
  rw [toRealMul, toRealAdd, toRealAdd, toRealMul, toRealMul]
  exact Construction.Dedekind.mulAdd
    (toReal left) (toReal middle) (toReal right)

public theorem addMul (left middle right : NNReal) :
    mul (add left middle) right =
      add (mul left right) (mul middle right) := by
  rw [mulComm (add left middle), mulAdd,
    mulComm right left, mulComm right middle]

public theorem mulZero (value : NNReal) : mul value zero = zero := by
  apply ext
  change Construction.Dedekind.mul
    (toReal value) Construction.Dedekind.zero = Construction.Dedekind.zero
  exact Construction.Dedekind.multiplicativeSelection.ring.mulZero (toReal value)

public theorem zeroMul (value : NNReal) : mul zero value = zero := by
  rw [mulComm, mulZero]

public noncomputable def semiring :
    Foundations.Algebra.CommutativeSemiringLaws NNReal where
  additive := {
    zero := zero
    add := add
    add_comm := addComm
    add_assoc := addAssoc
    add_zero := addZero
  }
  multiplicative := {
    one := one
    mul := mul
    mul_comm := mulComm
    mul_assoc := mulAssoc
    mul_one := mulOne
  }
  zero_mul := zeroMul
  mul_add := mulAdd

public theorem addLeAdd {firstLeft firstRight secondLeft secondRight : NNReal}
    (firstIncluded : le firstLeft firstRight)
    (secondIncluded : le secondLeft secondRight) :
    le (add firstLeft secondLeft) (add firstRight secondRight) := by
  change Construction.Dedekind.le
    (Construction.Dedekind.add (toReal firstLeft) (toReal secondLeft))
    (Construction.Dedekind.add (toReal firstRight) (toReal secondRight))
  exact Construction.Dedekind.leTrans
    ((Construction.Dedekind.addLeAddRightIff).mpr firstIncluded)
    ((Construction.Dedekind.addLeAddLeftIff).mpr secondIncluded)

public theorem addLeAddRight {left right : NNReal}
    (included : le left right) (shift : NNReal) :
    le (add left shift) (add right shift) := by
  change Construction.Dedekind.le
    (Construction.Dedekind.add (toReal left) (toReal shift))
    (Construction.Dedekind.add (toReal right) (toReal shift))
  exact (Construction.Dedekind.addLeAddRightIff).mpr included

public theorem addLeAddLeft {left right : NNReal}
    (included : le left right) (shift : NNReal) :
    le (add shift left) (add shift right) := by
  change Construction.Dedekind.le
    (Construction.Dedekind.add (toReal shift) (toReal left))
    (Construction.Dedekind.add (toReal shift) (toReal right))
  exact (Construction.Dedekind.addLeAddLeftIff).mpr included

public theorem addLeAddRightIff {left right shift : NNReal} :
    le (add left shift) (add right shift) ↔ le left right := by
  change Construction.Dedekind.le
      (Construction.Dedekind.add (toReal left) (toReal shift))
      (Construction.Dedekind.add (toReal right) (toReal shift)) ↔
    Construction.Dedekind.le (toReal left) (toReal right)
  exact Construction.Dedekind.addLeAddRightIff

public theorem addLeAddLeftIff {left right shift : NNReal} :
    le (add shift left) (add shift right) ↔ le left right := by
  change Construction.Dedekind.le
      (Construction.Dedekind.add (toReal shift) (toReal left))
      (Construction.Dedekind.add (toReal shift) (toReal right)) ↔
    Construction.Dedekind.le (toReal left) (toReal right)
  exact Construction.Dedekind.addLeAddLeftIff

public theorem mulLeMul {firstLeft firstRight secondLeft secondRight : NNReal}
    (firstIncluded : le firstLeft firstRight)
    (secondIncluded : le secondLeft secondRight) :
    le (mul firstLeft secondLeft) (mul firstRight secondRight) := by
  change Construction.Dedekind.le
    (Construction.Dedekind.mul (toReal firstLeft) (toReal secondLeft))
    (Construction.Dedekind.mul (toReal firstRight) (toReal secondRight))
  exact Construction.Dedekind.leTrans
    (Construction.Dedekind.mulLeMulNonnegativeRight firstIncluded secondLeft.property)
    (Construction.Dedekind.mulLeMulNonnegativeLeft secondIncluded firstRight.property)

public theorem mulLeMulRight {left right : NNReal}
    (included : le left right) (factor : NNReal) :
    le (mul left factor) (mul right factor) := by
  change Construction.Dedekind.le
    (Construction.Dedekind.mul (toReal left) (toReal factor))
    (Construction.Dedekind.mul (toReal right) (toReal factor))
  exact Construction.Dedekind.mulLeMulNonnegativeRight included factor.property

public theorem mulLeMulLeft {left right : NNReal}
    (included : le left right) (factor : NNReal) :
    le (mul factor left) (mul factor right) := by
  change Construction.Dedekind.le
    (Construction.Dedekind.mul (toReal factor) (toReal left))
    (Construction.Dedekind.mul (toReal factor) (toReal right))
  exact Construction.Dedekind.mulLeMulNonnegativeLeft included factor.property

public theorem mulEqZeroIff {left right : NNReal} :
    mul left right = zero ↔ left = zero ∨ right = zero := by
  constructor
  · intro equal
    have productZero : Construction.Dedekind.mul
        (toReal left) (toReal right) = Construction.Dedekind.zero := by
      simpa only [toRealMul, toRealZero] using congrArg toReal equal
    rcases Construction.Dedekind.mulEqZeroIff.mp productZero with
      leftZero | rightZero
    · exact Or.inl (ext leftZero)
    · exact Or.inr (ext rightZero)
  · rintro (leftZero | rightZero)
    · rw [leftZero, zeroMul]
    · rw [rightZero, mulZero]

end NNReal

end Foundations.Real
