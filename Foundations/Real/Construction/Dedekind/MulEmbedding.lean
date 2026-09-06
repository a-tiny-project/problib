module

import all Foundations.Real.Construction.Dedekind.Multiplication

/-
Copyright (c) 2026 Si-Qi Liu.
Licensed under the MIT License.

This Tiny-local proof extends the adapted Tautology Dedekind multiplication
at commit 261012c7540673d59a4015371b7618b7573d43da. Upstream has no matching
rational-multiplication theorem.
-/

namespace Foundations.Real.Construction.Dedekind

theorem ringOfRatOne :
    selection.ofRat 1 = ringLaws.multiplicative.one :=
  rfl

namespace Cut

private theorem ofRatNonnegative {value : Rat} (nonnegative : 0 ≤ value) :
    (0 : Cut) ≤ ofRat value := by
  intro rational negative
  exact Rational.ltOfLtOfLe negative nonnegative

theorem ofRatMulNonnegative (left right : Rat)
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right) :
    mulNonnegative (ofRat left) (ofRat right)
        (ofRatNonnegative leftNonnegative)
        (ofRatNonnegative rightNonnegative) =
      ofRat (left * right) := by
  apply Cut.ext
  intro value
  constructor
  · rintro (valueNegative | positiveProduct)
    · exact Rational.ltOfLtOfLe valueNegative
        (Rat.mul_nonneg leftNonnegative rightNonnegative)
    · rcases positiveProduct with
        ⟨leftValue, leftBound, leftPositive,
          rightValue, rightBound, rightPositive, valueBound⟩
      have leftPositiveBoundary : 0 < left :=
        Rational.ltTrans leftPositive leftBound
      have firstProductBound :
          leftValue * rightValue < left * rightValue :=
        Rat.mul_lt_mul_of_pos_right leftBound rightPositive
      have secondProductBound : left * rightValue < left * right :=
        Rat.mul_lt_mul_of_pos_left rightBound leftPositiveBoundary
      exact Rational.ltTrans valueBound
        (Rational.ltTrans firstProductBound secondProductBound)
  · intro valueBound
    by_cases valueNegative : value < 0
    · exact Or.inl valueNegative
    · have valueNonnegative : 0 ≤ value := Rat.not_lt.mp valueNegative
      have productPositive : 0 < left * right :=
        Rational.ltOfLeOfLt valueNonnegative valueBound
      have leftPositive : 0 < left := by
        rcases Rat.le_iff_lt_or_eq.mp leftNonnegative with
            positive | zero
        · exact positive
        · have productZero : left * right = 0 := by
            rw [← zero, Rat.zero_mul]
          rw [productZero] at productPositive
          exact False.elim (Rat.lt_irrefl productPositive)
      have rightPositive : 0 < right :=
        (Rat.mul_pos_iff_of_pos_left leftPositive).mp productPositive
      rcases Rational.existsPosLtOfLtMulRight
          valueNonnegative rightPositive valueBound with
        ⟨leftValue, leftValuePositive,
          leftProductBound, leftValueBound⟩
      rcases Rational.existsPosLtOfLtMulLeft
          valueNonnegative leftValuePositive leftProductBound with
        ⟨rightValue, rightValuePositive,
          productBound, rightValueBound⟩
      exact Or.inr ⟨leftValue, leftValueBound, leftValuePositive,
        rightValue, rightValueBound, rightValuePositive, productBound⟩

end Cut

private theorem selectedOfRatNonnegative {value : Rat}
    (nonnegative : 0 ≤ value) :
    additive.linearlyOrderedGroup.order.le
      additive.linearlyOrderedGroup.group.zero
      (selection.ofRat value) := by
  exact Cut.ofRatNonnegative nonnegative

theorem ringOfRatMulNonnegative (left right : Rat)
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right) :
  ringLaws.multiplicative.mul
        (selection.ofRat left) (selection.ofRat right) =
      selection.ofRat (left * right) := by
  rw [ringMul]
  rw [Foundations.Algebra.NonnegativeMultiplicationKernel.signedMulOfNonnegativeOfNonnegative
    additive.linearlyOrderedGroup multiplicationKernel
    (selectedOfRatNonnegative leftNonnegative)
    (selectedOfRatNonnegative rightNonnegative)]
  change Cut.mulNonnegative (Cut.ofRat left) (Cut.ofRat right)
      (Cut.ofRatNonnegative leftNonnegative)
      (Cut.ofRatNonnegative rightNonnegative) = Cut.ofRat (left * right)
  exact Cut.ofRatMulNonnegative left right leftNonnegative rightNonnegative

private theorem selectedOfRatNotNonnegative {value : Rat}
    (notNonnegative : ¬0 ≤ value) :
    ¬additive.linearlyOrderedGroup.order.le
      additive.linearlyOrderedGroup.group.zero
      (selection.ofRat value) := by
  intro included
  apply notNonnegative
  apply (selection.ofRat_le_iff 0 value).mp
  have zeroMap := RationalAdditiveHomomorphism.mapZero
    additive.group selection.ofRat additive.rational
  rw [zeroMap]
  exact included

private theorem selectedOfRatNeg (value : Rat) :
    additive.group.neg (selection.ofRat value) =
      selection.ofRat (-value) :=
  (RationalAdditiveHomomorphism.mapNeg
    additive.group selection.ofRat additive.rational value).symm

private theorem negNonnegativeOfNotNonnegative {value : Rat}
    (notNonnegative : ¬0 ≤ value) : 0 ≤ -value := by
  have valueNonpositive : value ≤ 0 :=
    Rat.le_of_lt (Rat.not_le.mp notNonnegative)
  have reversed := Rat.neg_le_neg valueNonpositive
  simpa [Rat.neg_zero] using reversed

theorem ringOfRatMul (left right : Rat) :
    ringLaws.multiplicative.mul
        (selection.ofRat left) (selection.ofRat right) =
      selection.ofRat (left * right) := by
  by_cases leftNonnegative : 0 ≤ left
  · by_cases rightNonnegative : 0 ≤ right
    · exact ringOfRatMulNonnegative left right
        leftNonnegative rightNonnegative
    · have negRightNonnegative :=
        negNonnegativeOfNotNonnegative rightNonnegative
      have rightRestored :
          selection.ofRat right =
            additive.group.neg (selection.ofRat (-right)) := by
        have mapped := selectedOfRatNeg (-right)
        rw [Rat.neg_neg] at mapped
        exact mapped.symm
      calc
        ringLaws.multiplicative.mul
            (selection.ofRat left) (selection.ofRat right) =
          ringLaws.multiplicative.mul
            (selection.ofRat left)
            (additive.group.neg (selection.ofRat (-right))) := by
              rw [rightRestored]
        _ = additive.group.neg
            (ringLaws.multiplicative.mul
              (selection.ofRat left) (selection.ofRat (-right))) :=
          ringLaws.mulNeg _ _
        _ = additive.group.neg
            (selection.ofRat (left * (-right))) := by
          rw [ringOfRatMulNonnegative left (-right)
            leftNonnegative negRightNonnegative]
        _ = selection.ofRat (-(left * (-right))) :=
          selectedOfRatNeg (left * (-right))
        _ = selection.ofRat (left * right) := by
          rw [Rat.mul_neg, Rat.neg_neg]
  · have negLeftNonnegative :=
      negNonnegativeOfNotNonnegative leftNonnegative
    by_cases rightNonnegative : 0 ≤ right
    · have leftRestored :
          selection.ofRat left =
            additive.group.neg (selection.ofRat (-left)) := by
        have mapped := selectedOfRatNeg (-left)
        rw [Rat.neg_neg] at mapped
        exact mapped.symm
      calc
        ringLaws.multiplicative.mul
            (selection.ofRat left) (selection.ofRat right) =
          ringLaws.multiplicative.mul
            (additive.group.neg (selection.ofRat (-left)))
            (selection.ofRat right) := by
              rw [leftRestored]
        _ = additive.group.neg
            (ringLaws.multiplicative.mul
              (selection.ofRat (-left)) (selection.ofRat right)) :=
          ringLaws.negMul _ _
        _ = additive.group.neg
            (selection.ofRat ((-left) * right)) := by
          rw [ringOfRatMulNonnegative (-left) right
            negLeftNonnegative rightNonnegative]
        _ = selection.ofRat (-((-left) * right)) :=
          selectedOfRatNeg ((-left) * right)
        _ = selection.ofRat (left * right) := by
          rw [Rat.neg_mul, Rat.neg_neg]
    · have negRightNonnegative :=
        negNonnegativeOfNotNonnegative rightNonnegative
      have leftRestored :
          selection.ofRat left =
            additive.group.neg (selection.ofRat (-left)) := by
        have mapped := selectedOfRatNeg (-left)
        rw [Rat.neg_neg] at mapped
        exact mapped.symm
      have rightRestored :
          selection.ofRat right =
            additive.group.neg (selection.ofRat (-right)) := by
        have mapped := selectedOfRatNeg (-right)
        rw [Rat.neg_neg] at mapped
        exact mapped.symm
      calc
        ringLaws.multiplicative.mul
            (selection.ofRat left) (selection.ofRat right) =
          ringLaws.multiplicative.mul
            (additive.group.neg (selection.ofRat (-left)))
            (additive.group.neg (selection.ofRat (-right))) := by
              rw [leftRestored, rightRestored]
        _ = ringLaws.multiplicative.mul
            (selection.ofRat (-left)) (selection.ofRat (-right)) :=
          ringLaws.negMulNeg _ _
        _ = selection.ofRat ((-left) * (-right)) :=
          ringOfRatMulNonnegative (-left) (-right)
            negLeftNonnegative negRightNonnegative
        _ = selection.ofRat (left * right) := by
          rw [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]

end Foundations.Real.Construction.Dedekind
