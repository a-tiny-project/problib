module

import all Problib.Real.Construction.Rational

/-
Copyright (c) 2026 Si-Qi Liu.
Licensed under the MIT License.

Adapted from Tautology/RealBasic/ModuleBackend/Dedekind/Basic.lean at commit
261012c7540673d59a4015371b7618b7573d43da.

Tiny changes namespaces and proof names. The module seal hides the carrier.
-/

namespace Problib.Real.Construction.Dedekind

structure Cut where
  mem : Rat → Prop
  nonempty : ∃ value, mem value
  proper : ∃ value, ¬mem value
  downward : ∀ {left right}, left < right → mem right → mem left
  no_greatest : ∀ {value}, mem value →
    ∃ greater, mem greater ∧ value < greater

namespace Cut

theorem ext {left right : Cut}
    (equal : ∀ value, left.mem value ↔ right.mem value) :
    left = right := by
  cases left with
  | mk leftMem leftNonempty leftProper leftDownward leftNoGreatest =>
      cases right with
      | mk rightMem rightNonempty rightProper rightDownward rightNoGreatest =>
          dsimp at equal
          have memEqual : leftMem = rightMem :=
            funext fun value => propext (equal value)
          subst memEqual
          rfl

def ofRat (boundary : Rat) : Cut where
  mem value := value < boundary
  nonempty := ⟨boundary - 1, Rational.sub_one_lt boundary⟩
  proper := ⟨boundary, Rat.lt_irrefl⟩
  downward := fun leftRight rightBoundary =>
    Rational.lt_trans leftRight rightBoundary
  no_greatest := by
    intro value valueBoundary
    rcases Rational.exists_between valueBoundary with ⟨greater, bounds⟩
    exact ⟨greater, bounds.right, bounds.left⟩

instance : Zero Cut where
  zero := ofRat 0

instance : One Cut where
  one := ofRat 1

theorem mem_ofRat {boundary value : Rat} :
    (ofRat boundary).mem value ↔ value < boundary :=
  Iff.rfl

theorem le_of_mem_of_not_mem {cut : Cut} {inside outside : Rat}
    (insideMember : cut.mem inside) (outsideAbsent : ¬cut.mem outside) :
    inside ≤ outside := by
  have notLess : ¬outside < inside := by
    intro less
    exact outsideAbsent (cut.downward less insideMember)
  exact Rat.not_lt.mp notLess

theorem exists_member_above_both {cut : Cut} {left right : Rat}
    (leftMember : cut.mem left) (rightMember : cut.mem right) :
    ∃ greater, cut.mem greater ∧ left < greater ∧ right < greater := by
  rcases Rat.le_total (a := left) (b := right) with
      leftRight | rightLeft
  · rcases cut.no_greatest rightMember with
      ⟨greater, greaterMember, rightGreater⟩
    exact ⟨greater, greaterMember,
      Rational.lt_of_le_of_lt leftRight rightGreater, rightGreater⟩
  · rcases cut.no_greatest leftMember with
      ⟨greater, greaterMember, leftGreater⟩
    exact ⟨greater, greaterMember, leftGreater,
      Rational.lt_of_le_of_lt rightLeft leftGreater⟩

end Cut

end Problib.Real.Construction.Dedekind
