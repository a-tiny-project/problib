module

import Foundations.Real.Interface
import all Foundations.Real.Construction.Dedekind.Basic

/-
Copyright (c) 2026 Si-Qi Liu.
Licensed under the MIT License.

Adapted from Tautology/RealBasic/ModuleBackend/Dedekind/Order.lean at commit
261012c7540673d59a4015371b7618b7573d43da.

Tiny removes unused strict-order lemmas. Suprema use the public generic
completeness vocabulary.
-/

namespace Foundations.Real.Construction.Dedekind

namespace Cut

instance : LE Cut where
  le left right := ∀ value, left.mem value → right.mem value

theorem leRefl (value : Cut) : value ≤ value := by
  intro rational member
  exact member

theorem leTrans {left middle right : Cut}
    (leftMiddle : left ≤ middle) (middleRight : middle ≤ right) :
    left ≤ right := by
  intro rational member
  exact middleRight rational (leftMiddle rational member)

theorem leAntisymm {left right : Cut}
    (leftRight : left ≤ right) (rightLeft : right ≤ left) :
    left = right := by
  apply Cut.ext
  intro rational
  exact ⟨leftRight rational, rightLeft rational⟩

theorem leTotal (left right : Cut) : left ≤ right ∨ right ≤ left := by
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

theorem ofRatLeIff (left right : Rat) :
    ofRat left ≤ ofRat right ↔ left ≤ right := by
  constructor
  · intro included
    apply Classical.byContradiction
    intro notLe
    have rightLeft : right < left := Rat.not_le.mp notLe
    rcases Rational.existsBetween rightLeft with
      ⟨middle, rightMiddle, middleLeft⟩
    have middleRight : middle < right := included middle middleLeft
    exact Rat.lt_irrefl (Rational.ltTrans rightMiddle middleRight)
  · intro leftRight value valueLeft
    exact Rational.ltOfLtOfLe valueLeft leftRight

private def sup (set : Cut → Prop) (setNonempty : ∃ value, set value)
    (setBounded : ∃ upper,
      Foundations.Real.IsUpperBound (fun left right : Cut => left ≤ right)
        set upper) : Cut where
  mem rational := ∃ value, set value ∧ value.mem rational
  nonempty := by
    rcases setNonempty with ⟨value, valueInSet⟩
    rcases value.nonempty with ⟨rational, member⟩
    exact ⟨rational, value, valueInSet, member⟩
  proper := by
    rcases setBounded with ⟨upper, upperBound⟩
    unfold Foundations.Real.IsUpperBound at upperBound
    rcases upper.proper with ⟨rational, absent⟩
    refine ⟨rational, ?_⟩
    rintro ⟨value, valueInSet, member⟩
    exact absent (upperBound value valueInSet rational member)
  downward := by
    intro left right leftRight
    rintro ⟨value, valueInSet, rightMember⟩
    exact ⟨value, valueInSet, value.downward leftRight rightMember⟩
  noGreatest := by
    intro rational
    rintro ⟨value, valueInSet, member⟩
    rcases value.noGreatest member with ⟨greater, greaterMember, less⟩
    exact ⟨greater, ⟨value, valueInSet, greaterMember⟩, less⟩

private theorem supUpperBound {set : Cut → Prop}
    {setNonempty : ∃ value, set value}
    {setBounded : ∃ upper,
      Foundations.Real.IsUpperBound (fun left right : Cut => left ≤ right)
        set upper} :
    Foundations.Real.IsUpperBound (fun left right : Cut => left ≤ right)
      set (sup set setNonempty setBounded) := by
  unfold Foundations.Real.IsUpperBound
  intro value valueInSet rational member
  exact ⟨value, valueInSet, member⟩

private theorem supLeast {set : Cut → Prop}
    {setNonempty : ∃ value, set value}
    {setBounded : ∃ upper,
      Foundations.Real.IsUpperBound (fun left right : Cut => left ≤ right)
        set upper}
    {upper : Cut}
    (upperBound : Foundations.Real.IsUpperBound
      (fun left right : Cut => left ≤ right) set upper) :
    sup set setNonempty setBounded ≤ upper := by
  unfold Foundations.Real.IsUpperBound at upperBound
  intro rational
  rintro ⟨value, valueInSet, member⟩
  exact upperBound value valueInSet rational member

theorem existsLub (set : Cut → Prop) (setNonempty : ∃ value, set value)
    (setBounded : ∃ upper,
      Foundations.Real.IsUpperBound (fun left right : Cut => left ≤ right)
        set upper) :
    ∃ least, Foundations.Real.IsLeastUpperBound
      (fun left right : Cut => left ≤ right) set least := by
  refine ⟨sup set setNonempty setBounded, ?_⟩
  unfold Foundations.Real.IsLeastUpperBound
  constructor
  · exact supUpperBound
  · intro upper upperBound
    exact supLeast upperBound

end Cut

end Foundations.Real.Construction.Dedekind
