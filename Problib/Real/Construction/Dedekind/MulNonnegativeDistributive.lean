module

import all Problib.Real.Construction.Dedekind.Additive
import all Problib.Real.Construction.Dedekind.MulNonnegative

/-
Copyright (c) 2026 Si-Qi Liu.
Licensed under the MIT License.

Adapted from
Tautology/RealBasic/ModuleBackend/Dedekind/MulNonnegDistrib.lean at commit
261012c7540673d59a4015371b7618b7573d43da.

Tiny retains only the left-distributive nonnegative result and its proof
closure. Names, namespaces, and proof syntax change; the right-distributive
law is derived abstractly from commutativity.
-/

namespace Problib.Real.Construction.Dedekind

namespace Cut

private theorem add_nonnegative {left right : Cut}
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right) :
    0 ≤ left + right := by
  have shifted := Cut.add_le_add_right leftNonnegative right
  rw [Cut.add_comm 0 right, Cut.add_zero] at shifted
  exact Cut.le_trans rightNonnegative shifted

private theorem exists_greater_member_of_lt_mul
    {left right : Cut}
    {leftNonnegative : 0 ≤ left} {rightNonnegative : 0 ≤ right}
    {leftValue rightValue target : Rat}
    (leftMember : left.mem leftValue) (leftPositive : 0 < leftValue)
    (rightMember : right.mem rightValue)
    (targetBound : target < leftValue * rightValue) :
    ∃ greater,
      (mulNonnegative left right
        leftNonnegative rightNonnegative).mem greater ∧ target < greater := by
  by_cases rightPositive : 0 < rightValue
  · rcases Rational.exists_between targetBound with
      ⟨greater, targetGreater, greaterBound⟩
    exact ⟨greater,
      Or.inr ⟨leftValue, leftMember, leftPositive,
        rightValue, rightMember, rightPositive, greaterBound⟩,
      targetGreater⟩
  · have rightNonpositive : rightValue ≤ 0 := Rat.not_lt.mp rightPositive
    have productNonpositive : leftValue * rightValue ≤ 0 := by
      have included := Rat.mul_le_mul_of_nonneg_left
        (a := rightValue) (b := 0) (c := leftValue)
        rightNonpositive (Rat.le_of_lt leftPositive)
      rw [Rat.mul_zero] at included
      exact included
    have targetNegative :=
      Rational.lt_of_lt_of_le targetBound productNonpositive
    rcases Rational.exists_between targetNegative with
      ⟨greater, targetGreater, greaterNegative⟩
    exact ⟨greater, Or.inl greaterNegative, targetGreater⟩

private theorem member_add_of_lt_sum {left right : Cut}
    {leftValue rightValue target : Rat}
    (leftMember : left.mem leftValue) (rightMember : right.mem rightValue)
    (targetBound : target < leftValue + rightValue) :
    (left + right).mem target := by
  have adjustedLess : target - rightValue < leftValue :=
    (Rat.sub_lt_iff
      (a := target) (b := leftValue) (c := rightValue)).mpr targetBound
  have equal : (target - rightValue) + rightValue = target := by
    rw [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.neg_add_cancel,
      Rat.add_zero]
  exact ⟨target - rightValue,
    left.downward adjustedLess leftMember,
    rightValue, rightMember, equal.symm⟩

private theorem member_add_of_left_slack {left right : Cut}
    (rightNonnegative : 0 ≤ right) {leftValue target : Rat}
    (leftMember : left.mem leftValue) (targetLess : target < leftValue) :
    (left + right).mem target := by
  have differenceNegative : target - leftValue < 0 := by
    apply (Rat.sub_lt_iff
      (a := target) (b := 0) (c := leftValue)).mpr
    rw [Rat.zero_add]
    exact targetLess
  have rightMember : right.mem (target - leftValue) :=
    rightNonnegative (target - leftValue) differenceNegative
  have equal : leftValue + (target - leftValue) = target := by
    rw [Rat.sub_eq_add_neg, Rat.add_comm target (-leftValue),
      ← Rat.add_assoc, Rat.add_neg_cancel, Rat.zero_add]
  exact ⟨leftValue, leftMember, target - leftValue,
    rightMember, equal.symm⟩

private theorem member_add_of_right_slack {left right : Cut}
    (leftNonnegative : 0 ≤ left) {rightValue target : Rat}
    (rightMember : right.mem rightValue)
    (targetLess : target < rightValue) :
    (left + right).mem target := by
  have differenceNegative : target - rightValue < 0 := by
    apply (Rat.sub_lt_iff
      (a := target) (b := 0) (c := rightValue)).mpr
    rw [Rat.zero_add]
    exact targetLess
  have leftMember : left.mem (target - rightValue) :=
    leftNonnegative (target - rightValue) differenceNegative
  have equal : (target - rightValue) + rightValue = target := by
    rw [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.neg_add_cancel,
      Rat.add_zero]
  exact ⟨target - rightValue, leftMember,
    rightValue, rightMember, equal.symm⟩

theorem mulNonnegative_add_left (factor left right : Cut)
    (factorNonnegative : 0 ≤ factor)
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right) :
    mulNonnegative factor (left + right)
        factorNonnegative (Cut.add_nonnegative leftNonnegative rightNonnegative) =
      mulNonnegative factor left factorNonnegative leftNonnegative +
        mulNonnegative factor right factorNonnegative rightNonnegative := by
  apply Cut.ext
  intro target
  constructor
  · intro targetMember
    have leftProductNonnegative :=
      mulNonnegative_nonnegative factor left
        factorNonnegative leftNonnegative
    have rightProductNonnegative :=
      mulNonnegative_nonnegative factor right
        factorNonnegative rightNonnegative
    have sumNonnegative := Cut.add_nonnegative
      leftProductNonnegative rightProductNonnegative
    rcases targetMember with targetNegative | positiveProduct
    · exact sumNonnegative target targetNegative
    · rcases positiveProduct with
        ⟨factorValue, factorMember, factorPositive,
          sumValue, sumMember, sumPositive, targetProduct⟩
      rcases sumMember with
        ⟨leftValue, leftMember, rightValue, rightMember, sumEqual⟩
      have targetSum :
          target < factorValue * leftValue + factorValue * rightValue := by
        have targetRaw :
            target < factorValue * (leftValue + rightValue) := by
          rw [← sumEqual]
          exact targetProduct
        rw [Rat.mul_add] at targetRaw
        exact targetRaw
      have leftTarget : target - factorValue * rightValue <
          factorValue * leftValue :=
        (Rat.sub_lt_iff
          (a := target) (b := factorValue * leftValue)
          (c := factorValue * rightValue)).mpr targetSum
      rcases exists_greater_member_of_lt_mul
          (left := factor) (right := left)
          factorMember factorPositive leftMember leftTarget with
        ⟨leftProductValue, leftProductMember, leftProductBound⟩
      have targetLeftRight :
          target < leftProductValue + factorValue * rightValue :=
        (Rat.sub_lt_iff
          (a := target) (b := leftProductValue)
          (c := factorValue * rightValue)).mp leftProductBound
      have rightTarget : target - leftProductValue <
          factorValue * rightValue := by
        apply (Rat.sub_lt_iff
          (a := target) (b := factorValue * rightValue)
          (c := leftProductValue)).mpr
        rw [Rat.add_comm]
        exact targetLeftRight
      rcases exists_greater_member_of_lt_mul
          (left := factor) (right := right)
          factorMember factorPositive rightMember rightTarget with
        ⟨rightProductValue, rightProductMember, rightProductBound⟩
      have exactRightMember :
          (mulNonnegative factor right
            factorNonnegative rightNonnegative).mem
              (target - leftProductValue) :=
        (mulNonnegative factor right
          factorNonnegative rightNonnegative).downward
            rightProductBound rightProductMember
      have equal :
          leftProductValue + (target - leftProductValue) = target := by
        rw [Rat.sub_eq_add_neg, Rat.add_comm target (-leftProductValue),
          ← Rat.add_assoc, Rat.add_neg_cancel, Rat.zero_add]
      exact ⟨leftProductValue, leftProductMember,
        target - leftProductValue, exactRightMember, equal.symm⟩
  · rintro ⟨leftProductValue, leftProductMember,
      rightProductValue, rightProductMember, targetEqual⟩
    by_cases targetNegative : target < 0
    · exact Or.inl targetNegative
    · have targetNonnegative : 0 ≤ target := Rat.not_lt.mp targetNegative
      rcases leftProductMember with
          leftProductNegative | leftPositiveProduct
      · rcases rightProductMember with
          rightProductNegative | rightPositiveProduct
        · have sumLessRight :
              leftProductValue + rightProductValue < rightProductValue := by
            have less := (Rat.add_lt_add_right
              (a := leftProductValue) (b := 0)
              (c := rightProductValue)).mpr leftProductNegative
            rw [Rat.zero_add] at less
            exact less
          have sumNegative := Rational.lt_trans
            sumLessRight rightProductNegative
          have targetNegative : target < 0 := by
            rw [targetEqual]
            exact sumNegative
          exact False.elim ((Rat.not_lt.mpr targetNonnegative) targetNegative)
        · rcases rightPositiveProduct with
            ⟨factorValue, factorMember, factorPositive,
              rightValue, rightMember, rightPositive, rightBound⟩
          have sumLessRight :
              leftProductValue + rightProductValue < rightProductValue := by
            have less := (Rat.add_lt_add_right
              (a := leftProductValue) (b := 0)
              (c := rightProductValue)).mpr leftProductNegative
            rw [Rat.zero_add] at less
            exact less
          have targetBound : target < factorValue * rightValue :=
            Rational.lt_trans (by rw [targetEqual]; exact sumLessRight)
              rightBound
          rcases Rational.exists_pos_lt_of_lt_mul_left
              targetNonnegative factorPositive targetBound with
            ⟨sumValue, sumPositive, productBound, sumRightBound⟩
          exact Or.inr ⟨factorValue, factorMember, factorPositive,
            sumValue,
            member_add_of_right_slack leftNonnegative
              rightMember sumRightBound,
            sumPositive, productBound⟩
      · rcases leftPositiveProduct with
          ⟨firstFactorValue, firstFactorMember, firstFactorPositive,
            leftValue, leftMember, leftPositive, leftBound⟩
        rcases rightProductMember with
          rightProductNegative | rightPositiveProduct
        · have sumLessLeft :
              leftProductValue + rightProductValue < leftProductValue := by
            have less := (Rat.add_lt_add_left
              (a := rightProductValue) (b := 0)
              (c := leftProductValue)).mpr rightProductNegative
            rw [Rat.add_zero] at less
            exact less
          have targetBound : target < firstFactorValue * leftValue :=
            Rational.lt_trans (by rw [targetEqual]; exact sumLessLeft)
              leftBound
          rcases Rational.exists_pos_lt_of_lt_mul_left
              targetNonnegative firstFactorPositive targetBound with
            ⟨sumValue, sumPositive, productBound, sumLeftBound⟩
          exact Or.inr ⟨firstFactorValue, firstFactorMember,
            firstFactorPositive, sumValue,
            member_add_of_left_slack rightNonnegative
              leftMember sumLeftBound,
            sumPositive, productBound⟩
        · rcases rightPositiveProduct with
            ⟨secondFactorValue, secondFactorMember,
              secondFactorPositive, rightValue, rightMember,
              rightPositive, rightBound⟩
          rcases factor.exists_member_above_both
              firstFactorMember secondFactorMember with
            ⟨factorValue, factorMember,
              firstFactorBound, secondFactorBound⟩
          have factorPositive :=
            Rational.lt_trans firstFactorPositive firstFactorBound
          have leftProductBound :
              leftProductValue < factorValue * leftValue := by
            have factorBound :
                firstFactorValue * leftValue < factorValue * leftValue :=
              Rat.mul_lt_mul_of_pos_right firstFactorBound leftPositive
            exact Rational.lt_trans leftBound factorBound
          have rightProductBound :
              rightProductValue < factorValue * rightValue := by
            have factorBound :
                secondFactorValue * rightValue < factorValue * rightValue :=
              Rat.mul_lt_mul_of_pos_right secondFactorBound rightPositive
            exact Rational.lt_trans rightBound factorBound
          have sumBound :
              leftProductValue + rightProductValue <
                factorValue * leftValue + factorValue * rightValue :=
            Rational.add_lt_add leftProductBound rightProductBound
          have targetBound : target <
              factorValue * (leftValue + rightValue) := by
            have distributed : target <
                factorValue * leftValue + factorValue * rightValue := by
              rw [targetEqual]
              exact sumBound
            rw [Rat.mul_add]
            exact distributed
          rcases Rational.exists_pos_lt_of_lt_mul_left
              targetNonnegative factorPositive targetBound with
            ⟨sumValue, sumPositive, productBound, sumBound⟩
          exact Or.inr ⟨factorValue, factorMember, factorPositive,
            sumValue,
            member_add_of_lt_sum leftMember rightMember sumBound,
            sumPositive, productBound⟩

end Cut

end Problib.Real.Construction.Dedekind
