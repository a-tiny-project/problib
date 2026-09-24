module

import Problib.Real.Interface
import all Problib.Real.Construction.Dedekind.Basic

/-
Copyright (c) 2026 Si-Qi Liu.
Licensed under the MIT License.

Adapted from Tautology/RealBasic/ModuleBackend/Dedekind/Order.lean at commit
261012c7540673d59a4015371b7618b7573d43da.

Tiny removes unused strict-order lemmas. Suprema use the public generic
completeness vocabulary.
-/

namespace Problib.Real.Construction.Dedekind

namespace Cut

instance : LE Cut where
  le left right := ∀ value, left.mem value → right.mem value

theorem le_refl (value : Cut) : value ≤ value := by
  intro rational member
  exact member

theorem le_trans {left middle right : Cut}
    (leftMiddle : left ≤ middle) (middleRight : middle ≤ right) :
    left ≤ right := by
  intro rational member
  exact middleRight rational (leftMiddle rational member)

theorem le_antisymm {left right : Cut}
    (leftRight : left ≤ right) (rightLeft : right ≤ left) :
    left = right := by
  apply Cut.ext
  intro rational
  exact ⟨leftRight rational, rightLeft rational⟩

theorem le_total (left right : Cut) : left ≤ right ∨ right ≤ left := by
  by_cases leftRight : left ≤ right
  · exact Or.inl leftRight
  · apply Or.inr
    have notAll : ¬∀ value, left.mem value → right.mem value := leftRight
    rcases Classical.not_forall.mp notAll with ⟨boundary, notImplication⟩
    have separated : left.mem boundary ∧ ¬right.mem boundary :=
      Classical.not_imp.mp notImplication
    intro value rightMember
    cases Rat.le_total (a := value) (b := boundary) with
    | inl valueBoundary =>
        cases Rat.le_iff_lt_or_eq.mp valueBoundary with
        | inl less => exact left.downward less separated.left
        | inr equal =>
            rw [equal]
            exact separated.left
    | inr boundaryValue =>
        have boundaryMember : right.mem boundary := by
          cases Rat.le_iff_lt_or_eq.mp boundaryValue with
          | inl less => exact right.downward less rightMember
          | inr equal =>
              rw [equal]
              exact rightMember
        exact False.elim (separated.right boundaryMember)

theorem ofRat_le_iff (left right : Rat) :
    ofRat left ≤ ofRat right ↔ left ≤ right := by
  constructor
  · intro included
    apply Classical.byContradiction
    intro notLe
    have rightLeft : right < left := Rat.not_le.mp notLe
    rcases Rational.exists_between rightLeft with
      ⟨middle, rightMiddle, middleLeft⟩
    have middleRight : middle < right := included middle middleLeft
    exact Rat.lt_irrefl (Rational.lt_trans rightMiddle middleRight)
  · intro leftRight value valueLeft
    exact Rational.lt_of_lt_of_le valueLeft leftRight

private def sup (set : Cut → Prop) (setNonempty : ∃ value, set value)
    (setBounded : ∃ upper,
      Problib.Real.IsUpperBound (fun left right : Cut => left ≤ right)
        set upper) : Cut where
  mem rational := ∃ value, set value ∧ value.mem rational
  nonempty := by
    rcases setNonempty with ⟨value, valueInSet⟩
    rcases value.nonempty with ⟨rational, member⟩
    exact ⟨rational, value, valueInSet, member⟩
  proper := by
    rcases setBounded with ⟨upper, upperBound⟩
    unfold Problib.Real.IsUpperBound at upperBound
    rcases upper.proper with ⟨rational, absent⟩
    refine ⟨rational, ?_⟩
    rintro ⟨value, valueInSet, member⟩
    exact absent (upperBound value valueInSet rational member)
  downward := by
    intro left right leftRight
    rintro ⟨value, valueInSet, rightMember⟩
    exact ⟨value, valueInSet, value.downward leftRight rightMember⟩
  no_greatest := by
    intro rational
    rintro ⟨value, valueInSet, member⟩
    rcases value.no_greatest member with ⟨greater, greaterMember, less⟩
    exact ⟨greater, ⟨value, valueInSet, greaterMember⟩, less⟩

private theorem sup_upper_bound {set : Cut → Prop}
    {setNonempty : ∃ value, set value}
    {setBounded : ∃ upper,
      Problib.Real.IsUpperBound (fun left right : Cut => left ≤ right)
        set upper} :
    Problib.Real.IsUpperBound (fun left right : Cut => left ≤ right)
      set (sup set setNonempty setBounded) := by
  unfold Problib.Real.IsUpperBound
  intro value valueInSet rational member
  exact ⟨value, valueInSet, member⟩

private theorem sup_least {set : Cut → Prop}
    {setNonempty : ∃ value, set value}
    {setBounded : ∃ upper,
      Problib.Real.IsUpperBound (fun left right : Cut => left ≤ right)
        set upper}
    {upper : Cut}
    (upperBound : Problib.Real.IsUpperBound
      (fun left right : Cut => left ≤ right) set upper) :
    sup set setNonempty setBounded ≤ upper := by
  unfold Problib.Real.IsUpperBound at upperBound
  intro rational
  rintro ⟨value, valueInSet, member⟩
  exact upperBound value valueInSet rational member

theorem exists_lub (set : Cut → Prop) (setNonempty : ∃ value, set value)
    (setBounded : ∃ upper,
      Problib.Real.IsUpperBound (fun left right : Cut => left ≤ right)
        set upper) :
    ∃ least, Problib.Real.IsLeastUpperBound
      (fun left right : Cut => left ≤ right) set least := by
  refine ⟨sup set setNonempty setBounded, ?_⟩
  unfold Problib.Real.IsLeastUpperBound
  constructor
  · exact sup_upper_bound
  · intro upper upperBound
    exact sup_least upperBound

end Cut

end Problib.Real.Construction.Dedekind
