module

import all Foundations.Real.Construction.Dedekind.Add

/-
Copyright (c) 2026 Si-Qi Liu.
Licensed under the MIT License.

This Tiny-local proof extends the adapted Tautology Dedekind construction at
commit 261012c7540673d59a4015371b7618b7573d43da. Upstream has no matching
rational-addition theorem.
-/

namespace Foundations.Real.Construction.Dedekind

namespace Cut

theorem ofRatAdd (left right : Rat) :
    ofRat (left + right) = ofRat left + ofRat right := by
  apply Cut.ext
  intro value
  constructor
  · intro valueBoundary
    have lowerLess : value - right < left :=
      (Rat.sub_lt_iff (a := value) (b := left) (c := right)).mpr
        valueBoundary
    rcases Rational.existsBetween lowerLess with
      ⟨leftValue, lowerLeftValue, leftValueBoundary⟩
    have valueSum : value < leftValue + right :=
      (Rat.sub_lt_iff
        (a := value) (b := leftValue) (c := right)).mp lowerLeftValue
    have reordered : value < right + leftValue := by
      rw [Rat.add_comm]
      exact valueSum
    have rightValueBoundary : value - leftValue < right :=
      (Rat.sub_lt_iff
        (a := value) (b := right) (c := leftValue)).mpr reordered
    have equal : value = leftValue + (value - leftValue) := by
      rw [Rat.sub_eq_add_neg, Rat.add_comm value (-leftValue),
        ← Rat.add_assoc, Rat.add_neg_cancel, Rat.zero_add]
    exact ⟨leftValue, leftValueBoundary, value - leftValue,
      rightValueBoundary, equal⟩
  · rintro ⟨leftValue, leftValueBoundary,
        rightValue, rightValueBoundary, equal⟩
    have firstLess : leftValue + rightValue < left + rightValue :=
      (Rat.add_lt_add_right
        (a := leftValue) (b := left) (c := rightValue)).mpr
        leftValueBoundary
    have secondLess : left + rightValue < left + right :=
      (Rat.add_lt_add_left
        (a := rightValue) (b := right) (c := left)).mpr
        rightValueBoundary
    rw [equal]
    exact Rational.ltTrans firstLess secondLess

end Cut

end Foundations.Real.Construction.Dedekind
