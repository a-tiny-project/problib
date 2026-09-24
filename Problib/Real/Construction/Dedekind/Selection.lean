module

public import Problib.Real.Additive
import all Problib.Real.Construction.Dedekind.Order
import all Problib.Real.Construction.Dedekind.Additive
import all Problib.Real.Construction.Dedekind.Embedding
import all Problib.Real.Construction.Dedekind.Approximation

/-
Copyright (c) 2026 Si-Qi Liu.
Licensed under the MIT License.

Adapted from Tautology/RealBasic/ModuleBackend/Dedekind/Selection.lean at
commit 261012c7540673d59a4015371b7618b7573d43da.

Tiny packages the proved order, completeness, additive algebra, translation
order, and rational additive homomorphism.
-/

namespace Problib.Real.Construction.Dedekind

public def certificate : AdditiveSelection where
  ordered := {
    name := "sealed rational Dedekind additive order"
    Carrier := Cut
    completeOrder := {
      order := {
        le := fun left right => left ≤ right
        refl := Cut.le_refl
        trans := Cut.le_trans
        antisymm := Cut.le_antisymm
        total := Cut.le_total
      }
      complete := {
        exists_lub := Cut.exists_lub
      }
    }
    ofRat := Cut.ofRat
    ofRat_le_iff := Cut.ofRat_le_iff
  }
  additive := {
    group := {
      zero := 0
      add := fun left right => left + right
      neg := fun value => -value
      add_comm := Cut.add_comm
      add_assoc := Cut.add_assoc
      add_zero := Cut.add_zero
      add_neg := Cut.add_neg
    }
    translation := {
      add_le_add_right := fun included shift => Cut.add_le_add_right included shift
    }
    rational := {
      map_add := Cut.ofRat_add
    }
  }

@[expose] public def selection : OrderedSelection :=
  certificate.ordered

public def additive : AdditiveOrderExtension selection :=
  certificate.additive

@[expose] public def le (left right : selection.Carrier) : Prop :=
  selection.completeOrder.order.le left right

@[expose] public def lt (left right : selection.Carrier) : Prop :=
  le left right ∧ ¬le right left

public theorem le_refl (value : selection.Carrier) : le value value :=
  selection.completeOrder.order.refl value

public theorem le_trans {left middle right : selection.Carrier}
    (leftMiddle : le left middle) (middleRight : le middle right) :
    le left right :=
  selection.completeOrder.order.trans leftMiddle middleRight

public theorem le_antisymm {left right : selection.Carrier}
    (leftRight : le left right) (rightLeft : le right left) :
    left = right :=
  selection.completeOrder.order.antisymm leftRight rightLeft

public theorem le_total (left right : selection.Carrier) :
    le left right ∨ le right left :=
  selection.completeOrder.order.total left right

public theorem ofRat_le_iff (left right : Rat) :
    le (selection.ofRat left) (selection.ofRat right) ↔ left ≤ right :=
  selection.ofRat_le_iff left right

public theorem ofRat_lt_iff (left right : Rat) :
    lt (selection.ofRat left) (selection.ofRat right) ↔ left < right := by
  change (le (selection.ofRat left) (selection.ofRat right) ∧
    ¬le (selection.ofRat right) (selection.ofRat left)) ↔ left < right
  rw [ofRat_le_iff, ofRat_le_iff]
  exact Rat.lt_iff_le_and_not_ge.symm

public theorem ofRat_injective : Function.Injective selection.ofRat := by
  intro left right equal
  apply Rat.le_antisymm
  · apply (ofRat_le_iff left right).mp
    rw [equal]
    exact le_refl _
  · apply (ofRat_le_iff right left).mp
    rw [equal]
    exact le_refl _

public theorem exists_lub (set : selection.Carrier → Prop)
    (setNonempty : ∃ value, set value)
    (setBounded : ∃ upper, IsUpperBound le set upper) :
    ∃ least, IsLeastUpperBound le set least :=
  selection.completeOrder.complete.exists_lub set setNonempty setBounded

public theorem exists_rational_between {left right : selection.Carrier}
    (less : lt left right) :
    ∃ rational : Rat,
      lt left (selection.ofRat rational) ∧
        lt (selection.ofRat rational) right := by
  rcases Cut.exists_rational_between less with
    ⟨rational, leftLe, notLeLeft, leRight, notRightLe⟩
  exact ⟨rational, ⟨leftLe, notLeLeft⟩, ⟨leRight, notRightLe⟩⟩

public theorem exists_nat_upper (value : selection.Carrier) :
    ∃ index : Nat, le value (selection.ofRat (index : Rat)) :=
  Cut.exists_nat_upper value

public theorem exists_nat_strict_upper (value : selection.Carrier) :
    ∃ index : Nat, lt value (selection.ofRat (index : Rat)) :=
  Cut.exists_nat_strict_upper value

end Problib.Real.Construction.Dedekind
