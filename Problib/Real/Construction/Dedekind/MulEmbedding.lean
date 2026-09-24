module

import all Problib.Real.Construction.Dedekind.Multiplication

/-
Copyright (c) 2026 Si-Qi Liu.
Licensed under the MIT License.

This Tiny-local proof extends the adapted Tautology Dedekind multiplication
at commit 261012c7540673d59a4015371b7618b7573d43da. Upstream has no matching
rational-multiplication theorem.
-/

namespace Problib.Real.Construction.Dedekind

theorem ring_ofRat_one :
    selection.ofRat 1 = ringLaws.multiplicative.one :=
  rfl

namespace Cut

private theorem ofRat_nonnegative {value : Rat} (nonnegative : 0 ≤ value) :
    (0 : Cut) ≤ ofRat value := by
  intro rational negative
  exact Rational.lt_of_lt_of_le negative nonnegative

theorem ofRat_mulNonnegative (left right : Rat)
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right) :
    mulNonnegative (ofRat left) (ofRat right)
        (ofRat_nonnegative leftNonnegative)
        (ofRat_nonnegative rightNonnegative) =
      ofRat (left * right) := by
  apply Cut.ext
  intro value
  constructor
  · rintro (valueNegative | positiveProduct)
    · exact Rational.lt_of_lt_of_le valueNegative
        (Rat.mul_nonneg leftNonnegative rightNonnegative)
    · rcases positiveProduct with
        ⟨leftValue, leftBound, leftPositive,
          rightValue, rightBound, rightPositive, valueBound⟩
      have leftPositiveBoundary : 0 < left :=
        Rational.lt_trans leftPositive leftBound
      have firstProductBound :
          leftValue * rightValue < left * rightValue :=
        Rat.mul_lt_mul_of_pos_right leftBound rightPositive
      have secondProductBound : left * rightValue < left * right :=
        Rat.mul_lt_mul_of_pos_left rightBound leftPositiveBoundary
      exact Rational.lt_trans valueBound
        (Rational.lt_trans firstProductBound secondProductBound)
  · intro valueBound
    by_cases valueNegative : value < 0
    · exact Or.inl valueNegative
    · have valueNonnegative : 0 ≤ value := Rat.not_lt.mp valueNegative
      have productPositive : 0 < left * right :=
        Rational.lt_of_le_of_lt valueNonnegative valueBound
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
      rcases Rational.exists_pos_lt_of_lt_mul_right
          valueNonnegative rightPositive valueBound with
        ⟨leftValue, leftValuePositive,
          leftProductBound, leftValueBound⟩
      rcases Rational.exists_pos_lt_of_lt_mul_left
          valueNonnegative leftValuePositive leftProductBound with
        ⟨rightValue, rightValuePositive,
          productBound, rightValueBound⟩
      exact Or.inr ⟨leftValue, leftValueBound, leftValuePositive,
        rightValue, rightValueBound, rightValuePositive, productBound⟩

end Cut

private theorem selected_ofRat_nonnegative {value : Rat}
    (nonnegative : 0 ≤ value) :
    additive.linearlyOrderedGroup.order.le
      additive.linearlyOrderedGroup.group.zero
      (selection.ofRat value) := by
  exact Cut.ofRat_nonnegative nonnegative

theorem ring_ofRat_mul_nonnegative (left right : Rat)
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right) :
  ringLaws.multiplicative.mul
        (selection.ofRat left) (selection.ofRat right) =
      selection.ofRat (left * right) := by
  rw [ring_mul]
  rw [Problib.Algebra.NonnegativeMultiplicationKernel.signedMul_of_nonnegative_of_nonnegative
    additive.linearlyOrderedGroup multiplicationKernel
    (selected_ofRat_nonnegative leftNonnegative)
    (selected_ofRat_nonnegative rightNonnegative)]
  change Cut.mulNonnegative (Cut.ofRat left) (Cut.ofRat right)
      (Cut.ofRat_nonnegative leftNonnegative)
      (Cut.ofRat_nonnegative rightNonnegative) = Cut.ofRat (left * right)
  exact Cut.ofRat_mulNonnegative left right leftNonnegative rightNonnegative

private theorem selected_ofRat_not_nonnegative {value : Rat}
    (notNonnegative : ¬0 ≤ value) :
    ¬additive.linearlyOrderedGroup.order.le
      additive.linearlyOrderedGroup.group.zero
      (selection.ofRat value) := by
  intro included
  apply notNonnegative
  apply (selection.ofRat_le_iff 0 value).mp
  have zeroMap := RationalAdditiveHomomorphism.map_zero
    additive.group selection.ofRat additive.rational
  rw [zeroMap]
  exact included

private theorem selected_ofRat_neg (value : Rat) :
    additive.group.neg (selection.ofRat value) =
      selection.ofRat (-value) :=
  (RationalAdditiveHomomorphism.map_neg
    additive.group selection.ofRat additive.rational value).symm

private theorem neg_nonnegative_of_not_nonnegative {value : Rat}
    (notNonnegative : ¬0 ≤ value) : 0 ≤ -value := by
  have valueNonpositive : value ≤ 0 :=
    Rat.le_of_lt (Rat.not_le.mp notNonnegative)
  have reversed := Rat.neg_le_neg valueNonpositive
  simpa [Rat.neg_zero] using reversed

theorem ring_ofRat_mul (left right : Rat) :
    ringLaws.multiplicative.mul
        (selection.ofRat left) (selection.ofRat right) =
      selection.ofRat (left * right) := by
  by_cases leftNonnegative : 0 ≤ left
  · by_cases rightNonnegative : 0 ≤ right
    · exact ring_ofRat_mul_nonnegative left right
        leftNonnegative rightNonnegative
    · have negRightNonnegative :=
        neg_nonnegative_of_not_nonnegative rightNonnegative
      have rightRestored :
          selection.ofRat right =
            additive.group.neg (selection.ofRat (-right)) := by
        have mapped := selected_ofRat_neg (-right)
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
          ringLaws.mul_neg _ _
        _ = additive.group.neg
            (selection.ofRat (left * (-right))) := by
          rw [ring_ofRat_mul_nonnegative left (-right)
            leftNonnegative negRightNonnegative]
        _ = selection.ofRat (-(left * (-right))) :=
          selected_ofRat_neg (left * (-right))
        _ = selection.ofRat (left * right) := by
          rw [Rat.mul_neg, Rat.neg_neg]
  · have negLeftNonnegative :=
      neg_nonnegative_of_not_nonnegative leftNonnegative
    by_cases rightNonnegative : 0 ≤ right
    · have leftRestored :
          selection.ofRat left =
            additive.group.neg (selection.ofRat (-left)) := by
        have mapped := selected_ofRat_neg (-left)
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
          ringLaws.neg_mul _ _
        _ = additive.group.neg
            (selection.ofRat ((-left) * right)) := by
          rw [ring_ofRat_mul_nonnegative (-left) right
            negLeftNonnegative rightNonnegative]
        _ = selection.ofRat (-((-left) * right)) :=
          selected_ofRat_neg ((-left) * right)
        _ = selection.ofRat (left * right) := by
          rw [Rat.neg_mul, Rat.neg_neg]
    · have negRightNonnegative :=
        neg_nonnegative_of_not_nonnegative rightNonnegative
      have leftRestored :
          selection.ofRat left =
            additive.group.neg (selection.ofRat (-left)) := by
        have mapped := selected_ofRat_neg (-left)
        rw [Rat.neg_neg] at mapped
        exact mapped.symm
      have rightRestored :
          selection.ofRat right =
            additive.group.neg (selection.ofRat (-right)) := by
        have mapped := selected_ofRat_neg (-right)
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
          ringLaws.neg_mul_neg _ _
        _ = selection.ofRat ((-left) * (-right)) :=
          ring_ofRat_mul_nonnegative (-left) (-right)
            negLeftNonnegative negRightNonnegative
        _ = selection.ofRat (left * right) := by
          rw [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]

end Problib.Real.Construction.Dedekind
