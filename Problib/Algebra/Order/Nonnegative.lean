module

public import Problib.Algebra.Order

namespace Problib.Algebra

@[expose] public def NonnegativePart {α : Type}
    (base : OrderedAdditiveCommutativeGroupLaws α) :=
  { value : α // base.order.le base.group.zero value }

namespace NonnegativePart

public theorem ext {α : Type}
    {base : OrderedAdditiveCommutativeGroupLaws α}
    {left right : NonnegativePart base} (equal : left.val = right.val) :
    left = right := by
  cases left
  cases right
  cases equal
  rfl

@[expose] public def zero {α : Type}
    (base : OrderedAdditiveCommutativeGroupLaws α) :
    NonnegativePart base :=
  ⟨base.group.zero, base.order.refl base.group.zero⟩

@[expose] public def add {α : Type}
    {base : OrderedAdditiveCommutativeGroupLaws α}
    (left right : NonnegativePart base) : NonnegativePart base :=
  ⟨base.group.add left.val right.val, by
    have included := base.add_le_add left.property right.property
    simpa only [base.group.add_zero] using included⟩

public theorem add_comm {α : Type}
    {base : OrderedAdditiveCommutativeGroupLaws α}
    (left right : NonnegativePart base) :
    add left right = add right left := by
  apply ext
  exact base.group.add_comm left.val right.val

public theorem add_assoc {α : Type}
    {base : OrderedAdditiveCommutativeGroupLaws α}
    (left middle right : NonnegativePart base) :
    add (add left middle) right = add left (add middle right) := by
  apply ext
  exact base.group.add_assoc left.val middle.val right.val

public theorem add_zero {α : Type}
    {base : OrderedAdditiveCommutativeGroupLaws α}
    (value : NonnegativePart base) : add value (zero base) = value := by
  apply ext
  exact base.group.add_zero value.val

public theorem add_left_cancel {α : Type}
    {base : OrderedAdditiveCommutativeGroupLaws α}
    {left first second : NonnegativePart base}
    (equal : add left first = add left second) : first = second := by
  apply ext
  apply AdditiveCommutativeGroupLaws.add_left_cancel base.group
  exact congrArg Subtype.val equal

public def additiveLaws {α : Type}
    (base : OrderedAdditiveCommutativeGroupLaws α) :
    AdditiveCommutativeMonoidLaws (NonnegativePart base) where
  zero := zero base
  add := add
  add_comm := add_comm
  add_assoc := add_assoc
  add_zero := add_zero

end NonnegativePart

public structure NonnegativeMultiplicationKernel {α : Type}
    (base : OrderedAdditiveCommutativeGroupLaws α) where
  one : NonnegativePart base
  mul : NonnegativePart base → NonnegativePart base → NonnegativePart base
  mul_comm : ∀ left right, mul left right = mul right left
  mul_assoc : ∀ left middle right,
    mul (mul left middle) right = mul left (mul middle right)
  mul_one : ∀ value, mul value one = value
  mul_add : ∀ left middle right,
    mul left (NonnegativePart.add middle right) =
      NonnegativePart.add (mul left middle) (mul left right)

namespace NonnegativeMultiplicationKernel

public theorem mul_zero {α : Type}
    {base : OrderedAdditiveCommutativeGroupLaws α}
    (kernel : NonnegativeMultiplicationKernel base)
    (value : NonnegativePart base) :
    kernel.mul value (NonnegativePart.zero base) =
      NonnegativePart.zero base := by
  apply NonnegativePart.add_left_cancel
    (left := kernel.mul value (NonnegativePart.zero base))
  calc
    NonnegativePart.add
        (kernel.mul value (NonnegativePart.zero base))
        (kernel.mul value (NonnegativePart.zero base)) =
      kernel.mul value
        (NonnegativePart.add
          (NonnegativePart.zero base) (NonnegativePart.zero base)) :=
      (kernel.mul_add value _ _).symm
    _ = kernel.mul value (NonnegativePart.zero base) := by
      rw [NonnegativePart.add_zero]
    _ = NonnegativePart.add
        (kernel.mul value (NonnegativePart.zero base))
        (NonnegativePart.zero base) :=
      (NonnegativePart.add_zero _).symm

public theorem zero_mul {α : Type}
    {base : OrderedAdditiveCommutativeGroupLaws α}
    (kernel : NonnegativeMultiplicationKernel base)
    (value : NonnegativePart base) :
    kernel.mul (NonnegativePart.zero base) value =
      NonnegativePart.zero base := by
  rw [kernel.mul_comm, kernel.mul_zero]

public def semiring {α : Type}
    {base : OrderedAdditiveCommutativeGroupLaws α}
    (kernel : NonnegativeMultiplicationKernel base) :
    CommutativeSemiringLaws (NonnegativePart base) where
  additive := NonnegativePart.additiveLaws base
  multiplicative := {
    one := kernel.one
    mul := kernel.mul
    mul_comm := kernel.mul_comm
    mul_assoc := kernel.mul_assoc
    mul_one := kernel.mul_one
  }
  zero_mul := kernel.zero_mul
  mul_add := kernel.mul_add

end NonnegativeMultiplicationKernel

end Problib.Algebra
