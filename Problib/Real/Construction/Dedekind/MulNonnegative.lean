module

import all Problib.Real.Construction.Dedekind.Sign
import all Problib.Real.Construction.Rational

/-
Copyright (c) 2026 Si-Qi Liu.
Licensed under the MIT License.

Adapted from Tautology/RealBasic/ModuleBackend/Dedekind/MulNonneg.lean at
commit 261012c7540673d59a4015371b7618b7573d43da.

Tiny retains the closure, commutativity, identity, and associativity slice
needed to construct the abstract nonnegative multiplication kernel. Names,
namespaces, and proof syntax change; zero absorption is derived generically.
-/

namespace Problib.Real.Construction.Dedekind

namespace Cut

def positiveProductMember (left right : Cut) (value : Rat) : Prop :=
  ∃ leftValue, left.mem leftValue ∧ 0 < leftValue ∧
    ∃ rightValue, right.mem rightValue ∧ 0 < rightValue ∧
      value < leftValue * rightValue

def mulNonnegative (left right : Cut)
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right) : Cut where
  mem value := value < 0 ∨ positiveProductMember left right value
  nonempty := ⟨0 - 1, Or.inl (Rational.sub_one_lt 0)⟩
  proper := by
    rcases left.proper with ⟨leftUpper, leftAbsent⟩
    rcases right.proper with ⟨rightUpper, rightAbsent⟩
    refine ⟨leftUpper * rightUpper, ?_⟩
    intro member
    rcases member with productNegative | positiveProduct
    · have leftUpperNonnegative :=
        left.nonnegative_of_nonnegative_cut_not_mem
          leftNonnegative leftAbsent
      have rightUpperNonnegative :=
        right.nonnegative_of_nonnegative_cut_not_mem
          rightNonnegative rightAbsent
      have productNonnegative : 0 ≤ leftUpper * rightUpper :=
        Rat.mul_nonneg leftUpperNonnegative rightUpperNonnegative
      exact Rat.lt_irrefl
        (Rational.lt_of_lt_of_le productNegative productNonnegative)
    · rcases positiveProduct with
        ⟨leftValue, leftMember, leftPositive,
          rightValue, rightMember, rightPositive, valueBound⟩
      have leftBound := left.le_of_mem_of_not_mem leftMember leftAbsent
      have rightBound := right.le_of_mem_of_not_mem rightMember rightAbsent
      have leftUpperPositive := left.positive_of_positive_mem_of_not_mem
        leftMember leftPositive leftAbsent
      have productBound :
          leftValue * rightValue ≤ leftUpper * rightUpper :=
        Rational.mul_le_mul_of_le_of_le_of_pos_of_pos
          leftBound rightBound rightPositive leftUpperPositive
      exact Rat.lt_irrefl
        (Rational.lt_of_lt_of_le valueBound productBound)
  downward := by
    intro smaller value smallerValue member
    rcases member with valueNegative | positiveProduct
    · exact Or.inl (Rational.lt_trans smallerValue valueNegative)
    · rcases positiveProduct with
        ⟨leftValue, leftMember, leftPositive,
          rightValue, rightMember, rightPositive, valueBound⟩
      exact Or.inr ⟨leftValue, leftMember, leftPositive,
        rightValue, rightMember, rightPositive,
        Rational.lt_trans smallerValue valueBound⟩
  no_greatest := by
    intro value member
    rcases member with valueNegative | positiveProduct
    · rcases Rational.exists_between valueNegative with
        ⟨greater, valueGreater, greaterNegative⟩
      exact ⟨greater, Or.inl greaterNegative, valueGreater⟩
    · rcases positiveProduct with
        ⟨leftValue, leftMember, leftPositive,
          rightValue, rightMember, rightPositive, valueBound⟩
      rcases Rational.exists_between valueBound with
        ⟨greater, valueGreater, greaterBound⟩
      exact ⟨greater,
        Or.inr ⟨leftValue, leftMember, leftPositive,
          rightValue, rightMember, rightPositive, greaterBound⟩,
        valueGreater⟩

theorem mulNonnegative_proof_irrelevant (left right : Cut)
    (leftNonnegative firstLeftNonnegative : 0 ≤ left)
    (rightNonnegative firstRightNonnegative : 0 ≤ right) :
    mulNonnegative left right leftNonnegative rightNonnegative =
      mulNonnegative left right firstLeftNonnegative
        firstRightNonnegative := by
  apply Cut.ext
  intro value
  exact Iff.rfl

theorem positiveProductMember_comm {left right : Cut} {value : Rat} :
    positiveProductMember left right value →
      positiveProductMember right left value := by
  rintro ⟨leftValue, leftMember, leftPositive,
    rightValue, rightMember, rightPositive, valueBound⟩
  refine ⟨rightValue, rightMember, rightPositive,
    leftValue, leftMember, leftPositive, ?_⟩
  rw [Rat.mul_comm]
  exact valueBound

theorem mulNonnegative_comm (left right : Cut)
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right) :
    mulNonnegative left right leftNonnegative rightNonnegative =
      mulNonnegative right left rightNonnegative leftNonnegative := by
  apply Cut.ext
  intro value
  constructor
  · rintro (negative | positive)
    · exact Or.inl negative
    · exact Or.inr (positiveProductMember_comm positive)
  · rintro (negative | positive)
    · exact Or.inl negative
    · exact Or.inr (positiveProductMember_comm positive)

theorem mulNonnegative_nonnegative (left right : Cut)
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right) :
    0 ≤ mulNonnegative left right leftNonnegative rightNonnegative := by
  intro value negative
  exact Or.inl negative

private theorem zero_le_one : (0 : Cut) ≤ 1 := by
  intro value negative
  exact Rational.lt_of_lt_of_le negative (by decide)

theorem mulNonnegative_one_left (value : Cut) (nonnegative : 0 ≤ value) :
    mulNonnegative 1 value zero_le_one nonnegative = value := by
  apply Cut.ext
  intro rational
  constructor
  · rintro (rationalNegative | positiveProduct)
    · exact nonnegative rational rationalNegative
    · rcases positiveProduct with
        ⟨factor, factorMember, factorPositive,
          member, valueMember, memberPositive, rationalBound⟩
      have factorLessOne : factor < 1 := factorMember
      have productLessMember : factor * member < member :=
        Rational.mul_lt_of_lt_one_of_pos factorLessOne memberPositive
      exact value.downward
        (Rational.lt_trans rationalBound productLessMember) valueMember
  · intro member
    by_cases rationalNegative : rational < 0
    · exact Or.inl rationalNegative
    · have rationalNonnegative : 0 ≤ rational :=
        Rat.not_lt.mp rationalNegative
      rcases value.no_greatest member with
        ⟨greater, greaterMember, rationalGreater⟩
      have greaterPositive : 0 < greater :=
        Rational.lt_of_le_of_lt rationalNonnegative rationalGreater
      rcases Rational.exists_pos_lt_one_mul_gt
          rationalNonnegative rationalGreater with
        ⟨factor, factorPositive, factorLessOne, productGreater⟩
      exact Or.inr ⟨factor, factorLessOne, factorPositive,
        greater, greaterMember, greaterPositive, productGreater⟩

theorem mulNonnegative_one_right (value : Cut) (nonnegative : 0 ≤ value) :
    mulNonnegative value 1 nonnegative zero_le_one = value := by
  rw [mulNonnegative_comm value 1 nonnegative zero_le_one]
  exact mulNonnegative_one_left value nonnegative

theorem mulNonnegative_assoc (left middle right : Cut)
    (leftNonnegative : 0 ≤ left) (middleNonnegative : 0 ≤ middle)
    (rightNonnegative : 0 ≤ right) :
    mulNonnegative
        (mulNonnegative left middle leftNonnegative middleNonnegative)
        right
        (mulNonnegative_nonnegative left middle
          leftNonnegative middleNonnegative)
        rightNonnegative =
      mulNonnegative left
        (mulNonnegative middle right middleNonnegative rightNonnegative)
        leftNonnegative
        (mulNonnegative_nonnegative middle right
          middleNonnegative rightNonnegative) := by
  apply Cut.ext
  intro rational
  constructor
  · rintro (rationalNegative | positiveProduct)
    · exact Or.inl rationalNegative
    · by_cases rationalNegative : rational < 0
      · exact Or.inl rationalNegative
      · have rationalNonnegative : 0 ≤ rational :=
          Rat.not_lt.mp rationalNegative
        rcases positiveProduct with
          ⟨pairValue, pairMember, pairPositive,
            rightValue, rightMember, rightPositive, rationalPairRight⟩
        have pairPositiveProduct :
            positiveProductMember left middle pairValue := by
          rcases pairMember with pairNegative | pairProduct
          · exact False.elim
              (Rat.lt_irrefl
                (Rational.lt_trans pairPositive pairNegative))
          · exact pairProduct
        rcases pairPositiveProduct with
          ⟨leftValue, leftMember, leftPositive,
            middleValue, middleMember, middlePositive, pairBound⟩
        have pairProductBound :
            pairValue * rightValue <
              (leftValue * middleValue) * rightValue :=
          Rat.mul_lt_mul_of_pos_right pairBound rightPositive
        have reassociatedBound :
            rational < leftValue * (middleValue * rightValue) := by
          have bound := Rational.lt_trans
            rationalPairRight pairProductBound
          rw [Rat.mul_assoc] at bound
          exact bound
        rcases Rational.exists_pos_lt_of_lt_mul_left
            rationalNonnegative leftPositive reassociatedBound with
          ⟨middleRightValue, middleRightPositive,
            rationalBound, middleRightBound⟩
        have middleRightMember :
            (mulNonnegative middle right
              middleNonnegative rightNonnegative).mem middleRightValue :=
          Or.inr ⟨middleValue, middleMember, middlePositive,
            rightValue, rightMember, rightPositive, middleRightBound⟩
        exact Or.inr ⟨leftValue, leftMember, leftPositive,
          middleRightValue, middleRightMember, middleRightPositive,
          rationalBound⟩
  · rintro (rationalNegative | positiveProduct)
    · exact Or.inl rationalNegative
    · by_cases rationalNegative : rational < 0
      · exact Or.inl rationalNegative
      · have rationalNonnegative : 0 ≤ rational :=
          Rat.not_lt.mp rationalNegative
        rcases positiveProduct with
          ⟨leftValue, leftMember, leftPositive,
            pairValue, pairMember, pairPositive, rationalLeftPair⟩
        have pairPositiveProduct :
            positiveProductMember middle right pairValue := by
          rcases pairMember with pairNegative | pairProduct
          · exact False.elim
              (Rat.lt_irrefl
                (Rational.lt_trans pairPositive pairNegative))
          · exact pairProduct
        rcases pairPositiveProduct with
          ⟨middleValue, middleMember, middlePositive,
            rightValue, rightMember, rightPositive, pairBound⟩
        have leftPairBound :
            leftValue * pairValue <
              leftValue * (middleValue * rightValue) :=
          Rat.mul_lt_mul_of_pos_left pairBound leftPositive
        have reassociatedBound :
            rational < (leftValue * middleValue) * rightValue := by
          have bound := Rational.lt_trans rationalLeftPair leftPairBound
          rw [← Rat.mul_assoc] at bound
          exact bound
        rcases Rational.exists_pos_lt_of_lt_mul_right
            rationalNonnegative rightPositive reassociatedBound with
          ⟨leftMiddleValue, leftMiddlePositive,
            rationalBound, leftMiddleBound⟩
        have leftMiddleMember :
            (mulNonnegative left middle
              leftNonnegative middleNonnegative).mem leftMiddleValue :=
          Or.inr ⟨leftValue, leftMember, leftPositive,
            middleValue, middleMember, middlePositive, leftMiddleBound⟩
        exact Or.inr ⟨leftMiddleValue, leftMiddleMember,
          leftMiddlePositive, rightValue, rightMember, rightPositive,
          rationalBound⟩

end Cut

end Problib.Real.Construction.Dedekind
