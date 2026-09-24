module

namespace Problib.Algebra

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

public theorem zero_add {α : Type}
    (laws : AdditiveCommutativeMonoidLaws α) (value : α) :
    laws.add laws.zero value = value := by
  rw [laws.add_comm, laws.add_zero]

public theorem add_left_comm {α : Type}
    (laws : AdditiveCommutativeMonoidLaws α) (left middle right : α) :
    laws.add left (laws.add middle right) =
      laws.add middle (laws.add left right) := by
  rw [← laws.add_assoc, laws.add_comm left middle, laws.add_assoc]

end AdditiveCommutativeMonoidLaws

namespace AdditiveCommutativeGroupLaws

@[expose] public def sub {α : Type}
    (laws : AdditiveCommutativeGroupLaws α) (left right : α) : α :=
  laws.add left (laws.neg right)

public theorem sub_eq_add_neg {α : Type}
    (laws : AdditiveCommutativeGroupLaws α) (left right : α) :
    laws.sub left right = laws.add left (laws.neg right) :=
  rfl

public theorem zero_add {α : Type}
    (laws : AdditiveCommutativeGroupLaws α) (value : α) :
    laws.add laws.zero value = value :=
  laws.toAdditiveCommutativeMonoidLaws.zero_add value

public theorem neg_add {α : Type}
    (laws : AdditiveCommutativeGroupLaws α) (value : α) :
    laws.add (laws.neg value) value = laws.zero := by
  rw [laws.add_comm, laws.add_neg]

public theorem add_neg_cancel_right {α : Type}
    (laws : AdditiveCommutativeGroupLaws α) (left right : α) :
    laws.add (laws.add left right) (laws.neg right) = left := by
  rw [laws.add_assoc, laws.add_neg, laws.add_zero]

public theorem neg_add_cancel_left {α : Type}
    (laws : AdditiveCommutativeGroupLaws α) (left right : α) :
    laws.add (laws.neg left) (laws.add left right) = right := by
  rw [← laws.add_assoc, neg_add laws, zero_add laws]

public theorem add_left_cancel {α : Type}
    (laws : AdditiveCommutativeGroupLaws α) {left first second : α}
    (equal : laws.add left first = laws.add left second) :
    first = second := by
  calc
    first = laws.add (laws.neg left) (laws.add left first) :=
      (neg_add_cancel_left laws left first).symm
    _ = laws.add (laws.neg left) (laws.add left second) :=
      congrArg (laws.add (laws.neg left)) equal
    _ = second := neg_add_cancel_left laws left second

public theorem add_right_cancel {α : Type}
    (laws : AdditiveCommutativeGroupLaws α) {right first second : α}
    (equal : laws.add first right = laws.add second right) :
    first = second := by
  apply add_left_cancel laws (left := right)
  rw [laws.add_comm right first, laws.add_comm right second]
  exact equal

public theorem add_left_comm {α : Type}
    (laws : AdditiveCommutativeGroupLaws α) (left middle right : α) :
    laws.add left (laws.add middle right) =
      laws.add middle (laws.add left right) :=
  laws.toAdditiveCommutativeMonoidLaws.add_left_comm left middle right

public theorem neg_neg {α : Type}
    (laws : AdditiveCommutativeGroupLaws α) (value : α) :
    laws.neg (laws.neg value) = value := by
  apply add_left_cancel laws (left := laws.neg value)
  rw [laws.add_neg, neg_add laws]

public theorem neg_zero {α : Type}
    (laws : AdditiveCommutativeGroupLaws α) :
    laws.neg laws.zero = laws.zero := by
  calc
    laws.neg laws.zero = laws.add laws.zero (laws.neg laws.zero) :=
      (zero_add laws _).symm
    _ = laws.zero := laws.add_neg laws.zero

public theorem add_neg_eq_of_eq_add {α : Type}
    (laws : AdditiveCommutativeGroupLaws α) {left result shift : α}
    (equal : result = laws.add left shift) :
    left = laws.add result (laws.neg shift) := by
  rw [equal, add_neg_cancel_right laws]

public theorem eq_add_of_eq_neg_add {α : Type}
    (laws : AdditiveCommutativeGroupLaws α) {left result shift : α}
    (equal : shift = laws.add (laws.neg left) result) :
    result = laws.add left shift := by
  rw [equal, ← laws.add_assoc, laws.add_neg, zero_add laws]

public theorem neg_add_distrib {α : Type}
    (laws : AdditiveCommutativeGroupLaws α) (left right : α) :
    laws.neg (laws.add left right) =
      laws.add (laws.neg left) (laws.neg right) := by
  apply add_left_cancel laws (left := laws.add left right)
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
        rw [laws.add_comm left right, add_neg_cancel_right laws]
      _ = laws.zero := laws.add_neg right
  exact rightZero.symm

public theorem neg_add_add_left {α : Type}
    (laws : AdditiveCommutativeGroupLaws α) (left right : α) :
    laws.add (laws.neg (laws.add left right)) left =
      laws.neg right := by
  rw [neg_add_distrib laws, laws.add_comm (laws.neg left),
    laws.add_assoc, neg_add laws, laws.add_zero]

end AdditiveCommutativeGroupLaws

namespace MultiplicativeCommutativeMonoidLaws

public theorem one_mul {α : Type}
    (laws : MultiplicativeCommutativeMonoidLaws α) (value : α) :
    laws.mul laws.one value = value := by
  rw [laws.mul_comm, laws.mul_one]

public theorem mul_left_comm {α : Type}
    (laws : MultiplicativeCommutativeMonoidLaws α) (left middle right : α) :
    laws.mul left (laws.mul middle right) =
      laws.mul middle (laws.mul left right) := by
  rw [← laws.mul_assoc, laws.mul_comm left middle, laws.mul_assoc]

end MultiplicativeCommutativeMonoidLaws

namespace CommutativeSemiringLaws

public theorem mul_zero {α : Type}
    (laws : CommutativeSemiringLaws α) (value : α) :
    laws.multiplicative.mul value laws.additive.zero =
      laws.additive.zero := by
  rw [laws.multiplicative.mul_comm, laws.zero_mul]

public theorem add_mul {α : Type}
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

end Problib.Algebra
