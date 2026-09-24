module

import all Problib.Real.Construction.Dedekind.Basic

/-
Copyright (c) 2026 Si-Qi Liu.
Licensed under the MIT License.

Adapted from Tautology/RealBasic/ModuleBackend/Dedekind/Add.lean at commit
261012c7540673d59a4015371b7618b7573d43da.

Tiny changes namespaces, names, and proof syntax. The module seal hides all
cut closure witnesses.
-/

namespace Problib.Real.Construction.Dedekind

namespace Cut

def add (left right : Cut) : Cut where
  mem value := ∃ leftValue : Rat, left.mem leftValue ∧
    ∃ rightValue : Rat, right.mem rightValue ∧
      value = leftValue + rightValue
  nonempty := by
    rcases left.nonempty with ⟨leftValue, leftMember⟩
    rcases right.nonempty with ⟨rightValue, rightMember⟩
    exact ⟨leftValue + rightValue, leftValue, leftMember,
      rightValue, rightMember, rfl⟩
  proper := by
    rcases left.proper with ⟨leftUpper, leftAbsent⟩
    rcases right.proper with ⟨rightUpper, rightAbsent⟩
    refine ⟨leftUpper + rightUpper, ?_⟩
    rintro ⟨leftValue, leftMember, rightValue, rightMember, equal⟩
    have leftBound := left.le_of_mem_of_not_mem leftMember leftAbsent
    have rightBound := right.le_of_mem_of_not_mem rightMember rightAbsent
    have leftLess : leftValue < leftUpper := by
      apply Rat.lt_of_le_of_ne leftBound
      intro boundaryEqual
      apply leftAbsent
      rw [← boundaryEqual]
      exact leftMember
    have rightLess : rightValue < rightUpper := by
      apply Rat.lt_of_le_of_ne rightBound
      intro boundaryEqual
      apply rightAbsent
      rw [← boundaryEqual]
      exact rightMember
    have firstLess : leftValue + rightValue < leftUpper + rightValue :=
      (Rat.add_lt_add_right
        (a := leftValue) (b := leftUpper) (c := rightValue)).mpr leftLess
    have secondLess : leftUpper + rightValue < leftUpper + rightUpper :=
      (Rat.add_lt_add_left
        (a := rightValue) (b := rightUpper) (c := leftUpper)).mpr rightLess
    have impossible := Rational.lt_trans firstLess secondLess
    rw [← equal] at impossible
    exact Rat.lt_irrefl impossible
  downward := by
    intro smaller value smallerValue
    rintro ⟨leftValue, leftMember, rightValue, rightMember, equal⟩
    have smallerSum : smaller < leftValue + rightValue := by
      rw [← equal]
      exact smallerValue
    have adjustedLess : smaller - rightValue < leftValue :=
      (Rat.sub_lt_iff
        (a := smaller) (b := leftValue) (c := rightValue)).mpr smallerSum
    have adjustedEqual : (smaller - rightValue) + rightValue = smaller := by
      rw [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.neg_add_cancel,
        Rat.add_zero]
    exact ⟨smaller - rightValue, left.downward adjustedLess leftMember,
      rightValue, rightMember, adjustedEqual.symm⟩
  no_greatest := by
    intro value
    rintro ⟨leftValue, leftMember, rightValue, rightMember, equal⟩
    rcases left.no_greatest leftMember with
      ⟨greaterLeft, greaterMember, leftLess⟩
    refine ⟨greaterLeft + rightValue, ?_, ?_⟩
    · exact ⟨greaterLeft, greaterMember, rightValue, rightMember, rfl⟩
    · rw [equal]
      exact (Rat.add_lt_add_right
        (a := leftValue) (b := greaterLeft) (c := rightValue)).mpr leftLess

instance : Add Cut where
  add := add

theorem add_comm (left right : Cut) : left + right = right + left := by
  apply Cut.ext
  intro value
  constructor
  · rintro ⟨leftValue, leftMember, rightValue, rightMember, equal⟩
    exact ⟨rightValue, rightMember, leftValue, leftMember,
      by rw [Rat.add_comm]; exact equal⟩
  · rintro ⟨rightValue, rightMember, leftValue, leftMember, equal⟩
    exact ⟨leftValue, leftMember, rightValue, rightMember,
      by rw [Rat.add_comm]; exact equal⟩

theorem add_assoc (left middle right : Cut) :
    (left + middle) + right = left + (middle + right) := by
  apply Cut.ext
  intro value
  constructor
  · rintro ⟨leftMiddle, ⟨leftValue, leftMember, middleValue,
        middleMember, leftMiddleEqual⟩, rightValue, rightMember, equal⟩
    exact ⟨leftValue, leftMember, middleValue + rightValue,
      ⟨middleValue, middleMember, rightValue, rightMember, rfl⟩,
      by calc
        value = leftMiddle + rightValue := equal
        _ = (leftValue + middleValue) + rightValue := by
          rw [leftMiddleEqual]
        _ = leftValue + (middleValue + rightValue) := by
          rw [Rat.add_assoc]⟩
  · rintro ⟨leftValue, leftMember, middleRight,
        ⟨middleValue, middleMember, rightValue, rightMember,
          middleRightEqual⟩, equal⟩
    exact ⟨leftValue + middleValue,
      ⟨leftValue, leftMember, middleValue, middleMember, rfl⟩,
      rightValue, rightMember,
      by calc
        value = leftValue + middleRight := equal
        _ = leftValue + (middleValue + rightValue) := by
          rw [middleRightEqual]
        _ = (leftValue + middleValue) + rightValue := by
          rw [← Rat.add_assoc]⟩

theorem add_zero (value : Cut) : value + 0 = value := by
  apply Cut.ext
  intro rational
  constructor
  · rintro ⟨leftValue, leftMember, rightValue, rightMember, equal⟩
    have rightNegative : rightValue < 0 := rightMember
    have sumLess : leftValue + rightValue < leftValue + 0 :=
      (Rat.add_lt_add_left
        (a := rightValue) (b := 0) (c := leftValue)).mpr rightNegative
    have rationalLess : rational < leftValue := by
      rw [equal]
      rw [Rat.add_zero] at sumLess
      exact sumLess
    exact value.downward rationalLess leftMember
  · intro member
    rcases value.no_greatest member with ⟨greater, greaterMember, less⟩
    have differenceNegative : rational - greater < 0 := by
      apply (Rat.sub_lt_iff
        (a := rational) (b := 0) (c := greater)).mpr
      rw [Rat.zero_add]
      exact less
    have equal : greater + (rational - greater) = rational := by
      rw [Rat.sub_eq_add_neg, Rat.add_comm rational (-greater),
        ← Rat.add_assoc, Rat.add_neg_cancel, Rat.zero_add]
    exact ⟨greater, greaterMember, rational - greater,
      differenceNegative, equal.symm⟩

end Cut

end Problib.Real.Construction.Dedekind
