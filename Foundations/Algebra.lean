module

namespace Foundations.Algebra

public structure AdditiveCommutativeMonoidLaws (α : Type) where
  zero : α
  add : α → α → α
  add_comm : ∀ left right, add left right = add right left
  add_assoc : ∀ left middle right,
    add (add left middle) right = add left (add middle right)
  add_zero : ∀ value, add value zero = value

public structure AdditiveCommutativeGroupLaws (α : Type) extends
    AdditiveCommutativeMonoidLaws α where
  neg : α → α
  add_neg : ∀ value, add value (neg value) = zero

public structure MultiplicativeCommutativeMonoidLaws (α : Type) where
  one : α
  mul : α → α → α
  mul_comm : ∀ left right, mul left right = mul right left
  mul_assoc : ∀ left middle right,
    mul (mul left middle) right = mul left (mul middle right)
  mul_one : ∀ value, mul value one = value

public structure CommutativeSemiringLaws (α : Type) where
  additive : AdditiveCommutativeMonoidLaws α
  multiplicative : MultiplicativeCommutativeMonoidLaws α
  zero_mul : ∀ value,
    multiplicative.mul additive.zero value = additive.zero
  mul_add : ∀ left middle right,
    multiplicative.mul left (additive.add middle right) =
      additive.add
        (multiplicative.mul left middle)
        (multiplicative.mul left right)

namespace AdditiveCommutativeMonoidLaws

public theorem zeroAdd {α : Type}
    (laws : AdditiveCommutativeMonoidLaws α) (value : α) :
    laws.add laws.zero value = value := by
  rw [laws.add_comm, laws.add_zero]

public theorem addLeftComm {α : Type}
    (laws : AdditiveCommutativeMonoidLaws α) (left middle right : α) :
    laws.add left (laws.add middle right) =
      laws.add middle (laws.add left right) := by
  rw [← laws.add_assoc, laws.add_comm left middle, laws.add_assoc]

end AdditiveCommutativeMonoidLaws

namespace AdditiveCommutativeGroupLaws

@[expose] public def sub {α : Type}
    (laws : AdditiveCommutativeGroupLaws α) (left right : α) : α :=
  laws.add left (laws.neg right)

public theorem subEqAddNeg {α : Type}
    (laws : AdditiveCommutativeGroupLaws α) (left right : α) :
    laws.sub left right = laws.add left (laws.neg right) :=
  rfl

public theorem zeroAdd {α : Type}
    (laws : AdditiveCommutativeGroupLaws α) (value : α) :
    laws.add laws.zero value = value :=
  laws.toAdditiveCommutativeMonoidLaws.zeroAdd value

public theorem negAdd {α : Type}
    (laws : AdditiveCommutativeGroupLaws α) (value : α) :
    laws.add (laws.neg value) value = laws.zero := by
  rw [laws.add_comm, laws.add_neg]

public theorem addNegCancelRight {α : Type}
    (laws : AdditiveCommutativeGroupLaws α) (left right : α) :
    laws.add (laws.add left right) (laws.neg right) = left := by
  rw [laws.add_assoc, laws.add_neg, laws.add_zero]

public theorem negAddCancelLeft {α : Type}
    (laws : AdditiveCommutativeGroupLaws α) (left right : α) :
    laws.add (laws.neg left) (laws.add left right) = right := by
  rw [← laws.add_assoc, negAdd laws, zeroAdd laws]

public theorem addLeftCancel {α : Type}
    (laws : AdditiveCommutativeGroupLaws α) {left first second : α}
    (equal : laws.add left first = laws.add left second) :
    first = second := by
  calc
    first = laws.add (laws.neg left) (laws.add left first) :=
      (negAddCancelLeft laws left first).symm
    _ = laws.add (laws.neg left) (laws.add left second) :=
      congrArg (laws.add (laws.neg left)) equal
    _ = second := negAddCancelLeft laws left second

public theorem addRightCancel {α : Type}
    (laws : AdditiveCommutativeGroupLaws α) {right first second : α}
    (equal : laws.add first right = laws.add second right) :
    first = second := by
  apply addLeftCancel laws (left := right)
  rw [laws.add_comm right first, laws.add_comm right second]
  exact equal

public theorem addLeftComm {α : Type}
    (laws : AdditiveCommutativeGroupLaws α) (left middle right : α) :
    laws.add left (laws.add middle right) =
      laws.add middle (laws.add left right) :=
  laws.toAdditiveCommutativeMonoidLaws.addLeftComm left middle right

public theorem negNeg {α : Type}
    (laws : AdditiveCommutativeGroupLaws α) (value : α) :
    laws.neg (laws.neg value) = value := by
  apply addLeftCancel laws (left := laws.neg value)
  rw [laws.add_neg, negAdd laws]

public theorem negZero {α : Type}
    (laws : AdditiveCommutativeGroupLaws α) :
    laws.neg laws.zero = laws.zero := by
  calc
    laws.neg laws.zero = laws.add laws.zero (laws.neg laws.zero) :=
      (zeroAdd laws _).symm
    _ = laws.zero := laws.add_neg laws.zero

public theorem addNegEqOfEqAdd {α : Type}
    (laws : AdditiveCommutativeGroupLaws α) {left result shift : α}
    (equal : result = laws.add left shift) :
    left = laws.add result (laws.neg shift) := by
  rw [equal, addNegCancelRight laws]

public theorem eqAddOfEqNegAdd {α : Type}
    (laws : AdditiveCommutativeGroupLaws α) {left result shift : α}
    (equal : shift = laws.add (laws.neg left) result) :
    result = laws.add left shift := by
  rw [equal, ← laws.add_assoc, laws.add_neg, zeroAdd laws]

public theorem negAddDistrib {α : Type}
    (laws : AdditiveCommutativeGroupLaws α) (left right : α) :
    laws.neg (laws.add left right) =
      laws.add (laws.neg left) (laws.neg right) := by
  apply addLeftCancel laws (left := laws.add left right)
  rw [laws.add_neg]
  have rightZero :
      laws.add (laws.add left right)
        (laws.add (laws.neg left) (laws.neg right)) = laws.zero := by
    calc
      laws.add (laws.add left right)
          (laws.add (laws.neg left) (laws.neg right)) =
        laws.add
          (laws.add (laws.add left right) (laws.neg left))
          (laws.neg right) := by rw [← laws.add_assoc]
      _ = laws.add right (laws.neg right) := by
        rw [laws.add_comm left right, addNegCancelRight laws]
      _ = laws.zero := laws.add_neg right
  exact rightZero.symm

public theorem negAddAddLeft {α : Type}
    (laws : AdditiveCommutativeGroupLaws α) (left right : α) :
    laws.add (laws.neg (laws.add left right)) left =
      laws.neg right := by
  rw [negAddDistrib laws, laws.add_comm (laws.neg left),
    laws.add_assoc, negAdd laws, laws.add_zero]

end AdditiveCommutativeGroupLaws

namespace MultiplicativeCommutativeMonoidLaws

public theorem oneMul {α : Type}
    (laws : MultiplicativeCommutativeMonoidLaws α) (value : α) :
    laws.mul laws.one value = value := by
  rw [laws.mul_comm, laws.mul_one]

public theorem mulLeftComm {α : Type}
    (laws : MultiplicativeCommutativeMonoidLaws α) (left middle right : α) :
    laws.mul left (laws.mul middle right) =
      laws.mul middle (laws.mul left right) := by
  rw [← laws.mul_assoc, laws.mul_comm left middle, laws.mul_assoc]

end MultiplicativeCommutativeMonoidLaws

namespace CommutativeSemiringLaws

public theorem mulZero {α : Type}
    (laws : CommutativeSemiringLaws α) (value : α) :
    laws.multiplicative.mul value laws.additive.zero =
      laws.additive.zero := by
  rw [laws.multiplicative.mul_comm, laws.zero_mul]

public theorem addMul {α : Type}
    (laws : CommutativeSemiringLaws α) (left middle right : α) :
    laws.multiplicative.mul (laws.additive.add left middle) right =
      laws.additive.add
        (laws.multiplicative.mul left right)
        (laws.multiplicative.mul middle right) := by
  rw [laws.multiplicative.mul_comm (laws.additive.add left middle) right,
    laws.mul_add,
    laws.multiplicative.mul_comm right left,
    laws.multiplicative.mul_comm right middle]

end CommutativeSemiringLaws

end Foundations.Algebra
