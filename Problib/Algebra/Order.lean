module

public import Problib.Algebra

namespace Problib.Algebra

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

public theorem add_le_add_right {α : Type}
    (laws : OrderedAdditiveCommutativeGroupLaws α)
    {left right : α} (included : laws.order.le left right) (shift : α) :
    laws.order.le (laws.group.add left shift)
      (laws.group.add right shift) :=
  laws.translation.add_le_add_right included shift

public theorem le_of_add_le_add_right {α : Type}
    (laws : OrderedAdditiveCommutativeGroupLaws α)
    {left right shift : α}
    (included : laws.order.le
      (laws.group.add left shift) (laws.group.add right shift)) :
    laws.order.le left right := by
  have restored := laws.translation.add_le_add_right included
    (laws.group.neg shift)
  simpa only [laws.group.add_assoc, laws.group.add_neg,
    laws.group.add_zero] using restored

public theorem add_le_add_right_iff {α : Type}
    (laws : OrderedAdditiveCommutativeGroupLaws α)
    {left right shift : α} :
    laws.order.le (laws.group.add left shift)
      (laws.group.add right shift) ↔ laws.order.le left right :=
  ⟨le_of_add_le_add_right laws, fun included =>
    add_le_add_right laws included shift⟩

public theorem add_le_add_left {α : Type}
    (laws : OrderedAdditiveCommutativeGroupLaws α)
    {left right : α} (included : laws.order.le left right) (shift : α) :
    laws.order.le (laws.group.add shift left)
      (laws.group.add shift right) := by
  rw [laws.group.add_comm shift left, laws.group.add_comm shift right]
  exact add_le_add_right laws included shift

public theorem le_of_add_le_add_left {α : Type}
    (laws : OrderedAdditiveCommutativeGroupLaws α)
    {left right shift : α}
    (included : laws.order.le
      (laws.group.add shift left) (laws.group.add shift right)) :
    laws.order.le left right := by
  apply le_of_add_le_add_right laws (shift := shift)
  rw [laws.group.add_comm left shift, laws.group.add_comm right shift]
  exact included

public theorem add_le_add_left_iff {α : Type}
    (laws : OrderedAdditiveCommutativeGroupLaws α)
    {left right shift : α} :
    laws.order.le (laws.group.add shift left)
      (laws.group.add shift right) ↔ laws.order.le left right :=
  ⟨le_of_add_le_add_left laws, fun included =>
    add_le_add_left laws included shift⟩

public theorem add_le_add {α : Type}
    (laws : OrderedAdditiveCommutativeGroupLaws α)
    {firstLeft firstRight secondLeft secondRight : α}
    (firstIncluded : laws.order.le firstLeft firstRight)
    (secondIncluded : laws.order.le secondLeft secondRight) :
    laws.order.le
      (laws.group.add firstLeft secondLeft)
      (laws.group.add firstRight secondRight) :=
  laws.order.trans
    (add_le_add_right laws firstIncluded secondLeft)
    (add_le_add_left laws secondIncluded firstRight)

public theorem neg_antitone {α : Type}
    (laws : OrderedAdditiveCommutativeGroupLaws α)
    {left right : α} (included : laws.order.le left right) :
    laws.order.le (laws.group.neg right) (laws.group.neg left) := by
  apply le_of_add_le_add_right laws (shift := right)
  have shifted := add_le_add_right laws included (laws.group.neg left)
  rw [laws.group.add_neg] at shifted
  rw [AdditiveCommutativeGroupLaws.neg_add laws.group,
    laws.group.add_comm (laws.group.neg left) right]
  exact shifted

public theorem neg_le_neg_iff {α : Type}
    (laws : OrderedAdditiveCommutativeGroupLaws α)
    {left right : α} :
    laws.order.le (laws.group.neg right) (laws.group.neg left) ↔
      laws.order.le left right := by
  constructor
  · intro included
    have restored := neg_antitone laws included
    rw [AdditiveCommutativeGroupLaws.neg_neg laws.group,
      AdditiveCommutativeGroupLaws.neg_neg laws.group] at restored
    exact restored
  · exact neg_antitone laws

public theorem sub_nonnegative_of_le {α : Type}
    (laws : OrderedAdditiveCommutativeGroupLaws α)
    {left right : α} (included : laws.order.le left right) :
    laws.order.le laws.group.zero (laws.group.sub right left) := by
  have shifted := add_le_add_right laws included (laws.group.neg left)
  simpa only [AdditiveCommutativeGroupLaws.sub,
    laws.group.add_neg] using shifted

public theorem le_of_sub_nonnegative {α : Type}
    (laws : OrderedAdditiveCommutativeGroupLaws α)
    {left right : α}
    (nonnegative : laws.order.le laws.group.zero
      (laws.group.sub right left)) :
    laws.order.le left right := by
  have shifted := add_le_add_right laws nonnegative left
  simpa only [AdditiveCommutativeGroupLaws.sub,
    AdditiveCommutativeGroupLaws.zero_add,
    laws.group.add_assoc,
    laws.group.add_comm (laws.group.neg left) left,
    laws.group.add_neg, laws.group.add_zero] using shifted

end OrderedAdditiveCommutativeGroupLaws

namespace LinearlyOrderedAdditiveCommutativeGroupLaws

public theorem nonpositive_of_not_nonnegative {α : Type}
    (laws : LinearlyOrderedAdditiveCommutativeGroupLaws α) {value : α}
    (notNonnegative : ¬laws.order.le laws.group.zero value) :
    laws.order.le value laws.group.zero := by
  rcases laws.total value laws.group.zero with
    valueNonpositive | valueNonnegative
  · exact valueNonpositive
  · exact False.elim (notNonnegative valueNonnegative)

public theorem neg_nonnegative_of_nonpositive {α : Type}
    (laws : LinearlyOrderedAdditiveCommutativeGroupLaws α) {value : α}
    (nonpositive : laws.order.le value laws.group.zero) :
    laws.order.le laws.group.zero (laws.group.neg value) := by
  have reversed := laws.toOrderedAdditiveCommutativeGroupLaws.neg_antitone
    nonpositive
  rw [AdditiveCommutativeGroupLaws.neg_zero laws.group] at reversed
  exact reversed

public theorem neg_nonpositive_of_nonnegative {α : Type}
    (laws : LinearlyOrderedAdditiveCommutativeGroupLaws α) {value : α}
    (nonnegative : laws.order.le laws.group.zero value) :
    laws.order.le (laws.group.neg value) laws.group.zero := by
  have reversed := laws.toOrderedAdditiveCommutativeGroupLaws.neg_antitone
    nonnegative
  rw [AdditiveCommutativeGroupLaws.neg_zero laws.group] at reversed
  exact reversed

public theorem neg_nonnegative_of_not_nonnegative {α : Type}
    (laws : LinearlyOrderedAdditiveCommutativeGroupLaws α) {value : α}
    (notNonnegative : ¬laws.order.le laws.group.zero value) :
    laws.order.le laws.group.zero (laws.group.neg value) :=
  neg_nonnegative_of_nonpositive laws
    (nonpositive_of_not_nonnegative laws notNonnegative)

public theorem nonpositive_of_neg_nonnegative {α : Type}
    (laws : LinearlyOrderedAdditiveCommutativeGroupLaws α) {value : α}
    (negNonnegative : laws.order.le laws.group.zero
      (laws.group.neg value)) :
    laws.order.le value laws.group.zero := by
  have reversed := laws.toOrderedAdditiveCommutativeGroupLaws.neg_antitone
    negNonnegative
  rw [AdditiveCommutativeGroupLaws.neg_neg laws.group,
    AdditiveCommutativeGroupLaws.neg_zero laws.group] at reversed
  exact reversed

public theorem eq_zero_of_nonnegative_of_neg_nonnegative {α : Type}
    (laws : LinearlyOrderedAdditiveCommutativeGroupLaws α) {value : α}
    (nonnegative : laws.order.le laws.group.zero value)
    (negNonnegative : laws.order.le laws.group.zero
      (laws.group.neg value)) :
    value = laws.group.zero :=
  laws.antisymm
    (nonpositive_of_neg_nonnegative laws negNonnegative)
    nonnegative

end LinearlyOrderedAdditiveCommutativeGroupLaws

end Problib.Algebra
