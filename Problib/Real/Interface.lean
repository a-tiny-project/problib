module

public import Problib.Algebra.Order
public import Init.Data.Rat.Lemmas

/-
Copyright (c) 2026 Si-Qi Liu.
Licensed under the MIT License.

Adapted from Tautology/Foundation/OrderField.lean at commit
261012c7540673d59a4015371b7618b7573d43da.

Tiny separates order, additive algebra, translation monotonicity, and rational
embedding capabilities. Names and namespaces change.
-/

namespace Problib.Real

@[expose] public def IsUpperBound {α : Type} (le : α → α → Prop)
    (set : α → Prop) (upper : α) : Prop :=
  ∀ value, set value → le value upper

@[expose] public def IsLeastUpperBound {α : Type} (le : α → α → Prop)
    (set : α → Prop) (least : α) : Prop :=
  IsUpperBound le set least ∧
    ∀ upper, IsUpperBound le set upper → le least upper

@[expose] public def IsLowerBound {α : Type} (le : α → α → Prop)
    (set : α → Prop) (lower : α) : Prop :=
  ∀ value, set value → le lower value

@[expose] public def IsGreatestLowerBound {α : Type} (le : α → α → Prop)
    (set : α → Prop) (greatest : α) : Prop :=
  IsLowerBound le set greatest ∧
    ∀ lower, IsLowerBound le set lower → le lower greatest

public structure DedekindComplete (α : Type)
    (le : α → α → Prop) where
  exists_lub : ∀ set : α → Prop,
    (∃ value, set value) →
    (∃ upper, IsUpperBound le set upper) →
    ∃ least, IsLeastUpperBound le set least

/-- Derives greatest lower bounds from least-upper-bound completeness by
reflecting into the set of lower bounds. Requires no order-law hypotheses on the
relation, enabling generic instantiation across arbitrary relations without
additional axioms. -/
public theorem DedekindComplete.exists_glb {α : Type} {le : α → α → Prop}
    (complete : DedekindComplete α le) (set : α → Prop)
    (nonempty : ∃ point, set point)
    (bounded : ∃ lower, IsLowerBound le set lower) :
    ∃ greatest, IsGreatestLowerBound le set greatest := by
  let lowerBounds := fun lower => ∀ point, set point → le lower point
  rcases nonempty with ⟨member, memberIn⟩
  rcases complete.exists_lub lowerBounds bounded
      ⟨member, fun lower lowerBound => lowerBound member memberIn⟩ with
    ⟨greatest, aboveLower, least⟩
  refine ⟨greatest, ?_, aboveLower⟩
  intro point pointIn
  exact least point (fun lower lowerBound => lowerBound point pointIn)

public structure CompleteLinearOrder (α : Type) where
  order : Problib.Algebra.LinearOrderLaws α
  complete : DedekindComplete α order.le

public structure OrderedSelection where
  name : String
  Carrier : Type
  completeOrder : CompleteLinearOrder Carrier
  ofRat : Rat → Carrier
  ofRat_le_iff : ∀ left right,
    completeOrder.order.le (ofRat left) (ofRat right) ↔ left ≤ right

public structure RationalAdditiveHomomorphism (α : Type)
    (add : α → α → α) (ofRat : Rat → α) where
  map_add : ∀ left right,
    ofRat (left + right) = add (ofRat left) (ofRat right)

public structure AdditiveOrderExtension (base : OrderedSelection) where
  group : Problib.Algebra.AdditiveCommutativeGroupLaws base.Carrier
  translation : Problib.Algebra.TranslationMonotone base.Carrier
    base.completeOrder.order.le group.add
  rational : RationalAdditiveHomomorphism base.Carrier
    group.add base.ofRat

public structure AdditiveSelection where
  ordered : OrderedSelection
  additive : AdditiveOrderExtension ordered

namespace AdditiveOrderExtension

@[expose] public def orderedGroup {base : OrderedSelection}
    (extension : AdditiveOrderExtension base) :
    Problib.Algebra.OrderedAdditiveCommutativeGroupLaws
      base.Carrier where
  order := base.completeOrder.order.toPreorderLaws
  group := extension.group
  translation := extension.translation

@[expose] public def linearlyOrderedGroup {base : OrderedSelection}
    (extension : AdditiveOrderExtension base) :
    Problib.Algebra.LinearlyOrderedAdditiveCommutativeGroupLaws
      base.Carrier where
  order := base.completeOrder.order.toPreorderLaws
  group := extension.group
  translation := extension.translation
  antisymm := base.completeOrder.order.antisymm
  total := base.completeOrder.order.total

end AdditiveOrderExtension

namespace AdditiveSelection

@[expose] public def orderedGroup (base : AdditiveSelection) :
    Problib.Algebra.OrderedAdditiveCommutativeGroupLaws
      base.ordered.Carrier :=
  base.additive.orderedGroup

@[expose] public def linearlyOrderedGroup (base : AdditiveSelection) :
    Problib.Algebra.LinearlyOrderedAdditiveCommutativeGroupLaws
      base.ordered.Carrier :=
  base.additive.linearlyOrderedGroup

end AdditiveSelection

end Problib.Real
