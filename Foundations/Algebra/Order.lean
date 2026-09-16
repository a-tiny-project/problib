module

public import Foundations.Algebra

namespace Foundations.Algebra

public structure PreorderLaws (α : Type) where
  le : α → α → Prop
  refl : ∀ value, le value value
  trans : ∀ {left middle right},
    le left middle → le middle right → le left right

public structure LinearOrderLaws (α : Type) extends PreorderLaws α where
  antisymm : ∀ {left right}, le left right → le right left → left = right
  total : ∀ left right, le left right ∨ le right left

public structure TranslationMonotone (α : Type)
    (le : α → α → Prop) (add : α → α → α) where
  add_le_add_right : ∀ {left right}, le left right →
    ∀ shift, le (add left shift) (add right shift)

public structure OrderedAdditiveCommutativeGroupLaws (α : Type) where
  order : PreorderLaws α
  group : AdditiveCommutativeGroupLaws α
  translation : TranslationMonotone α order.le group.add

public structure LinearlyOrderedAdditiveCommutativeGroupLaws
    (α : Type) extends OrderedAdditiveCommutativeGroupLaws α where
  antisymm : ∀ {left right},
    order.le left right → order.le right left → left = right
  total : ∀ left right, order.le left right ∨ order.le right left

namespace OrderedAdditiveCommutativeGroupLaws

public theorem addLeAddRight {α : Type}
    (laws : OrderedAdditiveCommutativeGroupLaws α)
    {left right : α} (included : laws.order.le left right) (shift : α) :
    laws.order.le (laws.group.add left shift)
      (laws.group.add right shift) :=
  laws.translation.add_le_add_right included shift

public theorem leOfAddLeAddRight {α : Type}
    (laws : OrderedAdditiveCommutativeGroupLaws α)
    {left right shift : α}
    (included : laws.order.le
      (laws.group.add left shift) (laws.group.add right shift)) :
    laws.order.le left right := by
  have restored := laws.translation.add_le_add_right included
    (laws.group.neg shift)
  simpa only [laws.group.add_assoc, laws.group.add_neg,
    laws.group.add_zero] using restored

public theorem addLeAddRightIff {α : Type}
    (laws : OrderedAdditiveCommutativeGroupLaws α)
    {left right shift : α} :
    laws.order.le (laws.group.add left shift)
      (laws.group.add right shift) ↔ laws.order.le left right :=
  ⟨leOfAddLeAddRight laws, fun included =>
    addLeAddRight laws included shift⟩

public theorem addLeAddLeft {α : Type}
    (laws : OrderedAdditiveCommutativeGroupLaws α)
    {left right : α} (included : laws.order.le left right) (shift : α) :
    laws.order.le (laws.group.add shift left)
      (laws.group.add shift right) := by
  rw [laws.group.add_comm shift left, laws.group.add_comm shift right]
  exact addLeAddRight laws included shift

public theorem leOfAddLeAddLeft {α : Type}
    (laws : OrderedAdditiveCommutativeGroupLaws α)
    {left right shift : α}
    (included : laws.order.le
      (laws.group.add shift left) (laws.group.add shift right)) :
    laws.order.le left right := by
  apply leOfAddLeAddRight laws (shift := shift)
  rw [laws.group.add_comm left shift, laws.group.add_comm right shift]
  exact included

public theorem addLeAddLeftIff {α : Type}
    (laws : OrderedAdditiveCommutativeGroupLaws α)
    {left right shift : α} :
    laws.order.le (laws.group.add shift left)
      (laws.group.add shift right) ↔ laws.order.le left right :=
  ⟨leOfAddLeAddLeft laws, fun included =>
    addLeAddLeft laws included shift⟩

public theorem addLeAdd {α : Type}
    (laws : OrderedAdditiveCommutativeGroupLaws α)
    {firstLeft firstRight secondLeft secondRight : α}
    (firstIncluded : laws.order.le firstLeft firstRight)
    (secondIncluded : laws.order.le secondLeft secondRight) :
    laws.order.le
      (laws.group.add firstLeft secondLeft)
      (laws.group.add firstRight secondRight) :=
  laws.order.trans
    (addLeAddRight laws firstIncluded secondLeft)
    (addLeAddLeft laws secondIncluded firstRight)

public theorem negAntitone {α : Type}
    (laws : OrderedAdditiveCommutativeGroupLaws α)
    {left right : α} (included : laws.order.le left right) :
    laws.order.le (laws.group.neg right) (laws.group.neg left) := by
  apply leOfAddLeAddRight laws (shift := right)
  have shifted := addLeAddRight laws included (laws.group.neg left)
  rw [laws.group.add_neg] at shifted
  rw [AdditiveCommutativeGroupLaws.negAdd laws.group,
    laws.group.add_comm (laws.group.neg left) right]
  exact shifted

public theorem negLeNegIff {α : Type}
    (laws : OrderedAdditiveCommutativeGroupLaws α)
    {left right : α} :
    laws.order.le (laws.group.neg right) (laws.group.neg left) ↔
      laws.order.le left right := by
  constructor
  · intro included
    have restored := negAntitone laws included
    rw [AdditiveCommutativeGroupLaws.negNeg laws.group,
      AdditiveCommutativeGroupLaws.negNeg laws.group] at restored
    exact restored
  · exact negAntitone laws

public theorem subNonnegativeOfLe {α : Type}
    (laws : OrderedAdditiveCommutativeGroupLaws α)
    {left right : α} (included : laws.order.le left right) :
    laws.order.le laws.group.zero (laws.group.sub right left) := by
  have shifted := addLeAddRight laws included (laws.group.neg left)
  simpa only [AdditiveCommutativeGroupLaws.sub,
    laws.group.add_neg] using shifted

public theorem leOfSubNonnegative {α : Type}
    (laws : OrderedAdditiveCommutativeGroupLaws α)
    {left right : α}
    (nonnegative : laws.order.le laws.group.zero
      (laws.group.sub right left)) :
    laws.order.le left right := by
  have shifted := addLeAddRight laws nonnegative left
  simpa only [AdditiveCommutativeGroupLaws.sub,
    AdditiveCommutativeGroupLaws.zeroAdd,
    laws.group.add_assoc,
    laws.group.add_comm (laws.group.neg left) left,
    laws.group.add_neg, laws.group.add_zero] using shifted

end OrderedAdditiveCommutativeGroupLaws

namespace LinearlyOrderedAdditiveCommutativeGroupLaws

public theorem nonpositiveOfNotNonnegative {α : Type}
    (laws : LinearlyOrderedAdditiveCommutativeGroupLaws α) {value : α}
    (notNonnegative : ¬laws.order.le laws.group.zero value) :
    laws.order.le value laws.group.zero := by
  rcases laws.total value laws.group.zero with
    valueNonpositive | valueNonnegative
  · exact valueNonpositive
  · exact False.elim (notNonnegative valueNonnegative)

public theorem negNonnegativeOfNonpositive {α : Type}
    (laws : LinearlyOrderedAdditiveCommutativeGroupLaws α) {value : α}
    (nonpositive : laws.order.le value laws.group.zero) :
    laws.order.le laws.group.zero (laws.group.neg value) := by
  have reversed := laws.toOrderedAdditiveCommutativeGroupLaws.negAntitone
    nonpositive
  rw [AdditiveCommutativeGroupLaws.negZero laws.group] at reversed
  exact reversed

public theorem negNonpositiveOfNonnegative {α : Type}
    (laws : LinearlyOrderedAdditiveCommutativeGroupLaws α) {value : α}
    (nonnegative : laws.order.le laws.group.zero value) :
    laws.order.le (laws.group.neg value) laws.group.zero := by
  have reversed := laws.toOrderedAdditiveCommutativeGroupLaws.negAntitone
    nonnegative
  rw [AdditiveCommutativeGroupLaws.negZero laws.group] at reversed
  exact reversed

public theorem negNonnegativeOfNotNonnegative {α : Type}
    (laws : LinearlyOrderedAdditiveCommutativeGroupLaws α) {value : α}
    (notNonnegative : ¬laws.order.le laws.group.zero value) :
    laws.order.le laws.group.zero (laws.group.neg value) :=
  negNonnegativeOfNonpositive laws
    (nonpositiveOfNotNonnegative laws notNonnegative)

public theorem nonpositiveOfNegNonnegative {α : Type}
    (laws : LinearlyOrderedAdditiveCommutativeGroupLaws α) {value : α}
    (negNonnegative : laws.order.le laws.group.zero
      (laws.group.neg value)) :
    laws.order.le value laws.group.zero := by
  have reversed := laws.toOrderedAdditiveCommutativeGroupLaws.negAntitone
    negNonnegative
  rw [AdditiveCommutativeGroupLaws.negNeg laws.group,
    AdditiveCommutativeGroupLaws.negZero laws.group] at reversed
  exact reversed

public theorem eqZeroOfNonnegativeOfNegNonnegative {α : Type}
    (laws : LinearlyOrderedAdditiveCommutativeGroupLaws α) {value : α}
    (nonnegative : laws.order.le laws.group.zero value)
    (negNonnegative : laws.order.le laws.group.zero
      (laws.group.neg value)) :
    value = laws.group.zero :=
  laws.antisymm
    (nonpositiveOfNegNonnegative laws negNonnegative)
    nonnegative

end LinearlyOrderedAdditiveCommutativeGroupLaws

end Foundations.Algebra
