module

public import Foundations.Real.Additive
import all Foundations.Real.Construction.Dedekind.Order
import all Foundations.Real.Construction.Dedekind.Additive
import all Foundations.Real.Construction.Dedekind.Embedding
import all Foundations.Real.Construction.Dedekind.Approximation

/-
Copyright (c) 2026 Si-Qi Liu.
Licensed under the MIT License.

Adapted from Tautology/RealBasic/ModuleBackend/Dedekind/Selection.lean at
commit 261012c7540673d59a4015371b7618b7573d43da.

Tiny packages the proved order, completeness, additive algebra, translation
order, and rational additive homomorphism.
-/

namespace Foundations.Real.Construction.Dedekind

public def certificate : AdditiveSelection where
  ordered := {
    name := "sealed rational Dedekind additive order"
    Carrier := Cut
    completeOrder := {
      order := {
        le := fun left right => left ≤ right
        refl := Cut.leRefl
        trans := Cut.leTrans
        antisymm := Cut.leAntisymm
        total := Cut.leTotal
      }
      complete := {
        exists_lub := Cut.existsLub
      }
    }
    ofRat := Cut.ofRat
    ofRat_le_iff := Cut.ofRatLeIff
  }
  additive := {
    group := {
      zero := 0
      add := fun left right => left + right
      neg := fun value => -value
      add_comm := Cut.addComm
      add_assoc := Cut.addAssoc
      add_zero := Cut.addZero
      add_neg := Cut.addNeg
    }
    translation := {
      add_le_add_right := fun included shift => Cut.addLeAddRight included shift
    }
    rational := {
      map_add := Cut.ofRatAdd
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

public theorem leRefl (value : selection.Carrier) : le value value :=
  selection.completeOrder.order.refl value

public theorem leTrans {left middle right : selection.Carrier}
    (leftMiddle : le left middle) (middleRight : le middle right) :
    le left right :=
  selection.completeOrder.order.trans leftMiddle middleRight

public theorem leAntisymm {left right : selection.Carrier}
    (leftRight : le left right) (rightLeft : le right left) :
    left = right :=
  selection.completeOrder.order.antisymm leftRight rightLeft

public theorem leTotal (left right : selection.Carrier) :
    le left right ∨ le right left :=
  selection.completeOrder.order.total left right

public theorem ofRatLeIff (left right : Rat) :
    le (selection.ofRat left) (selection.ofRat right) ↔ left ≤ right :=
  selection.ofRat_le_iff left right

public theorem ofRatLtIff (left right : Rat) :
    lt (selection.ofRat left) (selection.ofRat right) ↔ left < right := by
  change (le (selection.ofRat left) (selection.ofRat right) ∧
    ¬le (selection.ofRat right) (selection.ofRat left)) ↔ left < right
  rw [ofRatLeIff, ofRatLeIff]
  exact Rat.lt_iff_le_and_not_ge.symm

public theorem ofRatInjective : Function.Injective selection.ofRat := by
  intro left right equal
  apply Rat.le_antisymm
  · apply (ofRatLeIff left right).mp
    rw [equal]
    exact leRefl _
  · apply (ofRatLeIff right left).mp
    rw [equal]
    exact leRefl _

public theorem existsLub (set : selection.Carrier → Prop)
    (setNonempty : ∃ value, set value)
    (setBounded : ∃ upper, IsUpperBound le set upper) :
    ∃ least, IsLeastUpperBound le set least :=
  selection.completeOrder.complete.exists_lub set setNonempty setBounded

public theorem existsRationalBetween {left right : selection.Carrier}
    (less : lt left right) :
    ∃ rational : Rat,
      lt left (selection.ofRat rational) ∧
        lt (selection.ofRat rational) right := by
  rcases Cut.existsRationalBetween less with
    ⟨rational, leftLe, notLeLeft, leRight, notRightLe⟩
  exact ⟨rational, ⟨leftLe, notLeLeft⟩, ⟨leRight, notRightLe⟩⟩

public theorem existsNatUpper (value : selection.Carrier) :
    ∃ index : Nat, le value (selection.ofRat (index : Rat)) :=
  Cut.existsNatUpper value

public theorem existsNatStrictUpper (value : selection.Carrier) :
    ∃ index : Nat, lt value (selection.ofRat (index : Rat)) :=
  Cut.existsNatStrictUpper value

end Foundations.Real.Construction.Dedekind
