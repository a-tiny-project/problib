module

import all Foundations.Real.Construction.Dedekind.Sign
import all Foundations.Real.Construction.Rational

/-
Copyright (c) 2026 Si-Qi Liu.
Licensed under the MIT License.

Adapted from Tautology/RealBasic/ModuleBackend/Dedekind/MulNonneg.lean at
commit 261012c7540673d59a4015371b7618b7573d43da.

Tiny retains the closure, commutativity, identity, and associativity slice
needed to construct the abstract nonnegative multiplication kernel. Names,
namespaces, and proof syntax change; zero absorption is derived generically.
-/

namespace Foundations.Real.Construction.Dedekind

namespace Cut

def positiveProductMember (left right : Cut) (value : Rat) : Prop :=
  ∃ leftValue, left.mem leftValue ∧ 0 < leftValue ∧
    ∃ rightValue, right.mem rightValue ∧ 0 < rightValue ∧
      value < leftValue * rightValue

def mulNonnegative (left right : Cut)
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right) : Cut where
  mem value := value < 0 ∨ positiveProductMember left right value
  nonempty := ⟨0 - 1, Or.inl (Rational.subOneLt 0)⟩
  proper := by
    rcases left.proper with ⟨leftUpper, leftAbsent⟩
    rcases right.proper with ⟨rightUpper, rightAbsent⟩
    refine ⟨leftUpper * rightUpper, ?_⟩
    intro member
    rcases member with productNegative | positiveProduct
    · have leftUpperNonnegative :=
        left.nonnegativeOfNonnegativeCutNotMem
          leftNonnegative leftAbsent
      have rightUpperNonnegative :=
        right.nonnegativeOfNonnegativeCutNotMem
          rightNonnegative rightAbsent
      have productNonnegative : 0 ≤ leftUpper * rightUpper :=
        Rat.mul_nonneg leftUpperNonnegative rightUpperNonnegative
      exact Rat.lt_irrefl
        (Rational.ltOfLtOfLe productNegative productNonnegative)
    · rcases positiveProduct with
        ⟨leftValue, leftMember, leftPositive,
          rightValue, rightMember, rightPositive, valueBound⟩
      have leftBound := left.leOfMemOfNotMem leftMember leftAbsent
      have rightBound := right.leOfMemOfNotMem rightMember rightAbsent
      have leftUpperPositive := left.positiveOfPositiveMemOfNotMem
        leftMember leftPositive leftAbsent
      have productBound :
          leftValue * rightValue ≤ leftUpper * rightUpper :=
        Rational.mulLeMulOfLeOfLeOfPosOfPos
          leftBound rightBound rightPositive leftUpperPositive
      exact Rat.lt_irrefl
        (Rational.ltOfLtOfLe valueBound productBound)
  downward := by
    intro smaller value smallerValue member
    rcases member with valueNegative | positiveProduct
    · exact Or.inl (Rational.ltTrans smallerValue valueNegative)
    · rcases positiveProduct with
        ⟨leftValue, leftMember, leftPositive,
          rightValue, rightMember, rightPositive, valueBound⟩
      exact Or.inr ⟨leftValue, leftMember, leftPositive,
        rightValue, rightMember, rightPositive,
        Rational.ltTrans smallerValue valueBound⟩
  noGreatest := by
    intro value member
    rcases member with valueNegative | positiveProduct
    · rcases Rational.existsBetween valueNegative with
        ⟨greater, valueGreater, greaterNegative⟩
      exact ⟨greater, Or.inl greaterNegative, valueGreater⟩
    · rcases positiveProduct with
        ⟨leftValue, leftMember, leftPositive,
          rightValue, rightMember, rightPositive, valueBound⟩
      rcases Rational.existsBetween valueBound with
        ⟨greater, valueGreater, greaterBound⟩
      exact ⟨greater,
        Or.inr ⟨leftValue, leftMember, leftPositive,
          rightValue, rightMember, rightPositive, greaterBound⟩,
        valueGreater⟩

theorem mulNonnegativeProofIrrelevant (left right : Cut)
    (leftNonnegative firstLeftNonnegative : 0 ≤ left)
    (rightNonnegative firstRightNonnegative : 0 ≤ right) :
    mulNonnegative left right leftNonnegative rightNonnegative =
      mulNonnegative left right firstLeftNonnegative
        firstRightNonnegative := by
  apply Cut.ext
  intro value
  exact Iff.rfl

theorem positiveProductMemberComm {left right : Cut} {value : Rat} :
    positiveProductMember left right value →
      positiveProductMember right left value := by
  rintro ⟨leftValue, leftMember, leftPositive,
    rightValue, rightMember, rightPositive, valueBound⟩
  refine ⟨rightValue, rightMember, rightPositive,
    leftValue, leftMember, leftPositive, ?_⟩
  rw [Rat.mul_comm]
  exact valueBound

theorem mulNonnegativeComm (left right : Cut)
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right) :
    mulNonnegative left right leftNonnegative rightNonnegative =
      mulNonnegative right left rightNonnegative leftNonnegative := by
  apply Cut.ext
  intro value
  constructor
  · rintro (negative | positive)
    · exact Or.inl negative
    · exact Or.inr (positiveProductMemberComm positive)
  · rintro (negative | positive)
    · exact Or.inl negative
    · exact Or.inr (positiveProductMemberComm positive)

theorem mulNonnegativeNonnegative (left right : Cut)
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right) :
    0 ≤ mulNonnegative left right leftNonnegative rightNonnegative := by
  intro value negative
  exact Or.inl negative

private theorem zeroLeOne : (0 : Cut) ≤ 1 := by
  intro value negative
  exact Rational.ltOfLtOfLe negative (by decide)

theorem mulNonnegativeOneLeft (value : Cut) (nonnegative : 0 ≤ value) :
    mulNonnegative 1 value zeroLeOne nonnegative = value := by
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
        Rational.mulLtOfLtOneOfPos factorLessOne memberPositive
      exact value.downward
        (Rational.ltTrans rationalBound productLessMember) valueMember
  · intro member
    by_cases rationalNegative : rational < 0
    · exact Or.inl rationalNegative
    · have rationalNonnegative : 0 ≤ rational :=
        Rat.not_lt.mp rationalNegative
      rcases value.noGreatest member with
        ⟨greater, greaterMember, rationalGreater⟩
      have greaterPositive : 0 < greater :=
        Rational.ltOfLeOfLt rationalNonnegative rationalGreater
      rcases Rational.existsPosLtOneMulGt
          rationalNonnegative rationalGreater with
        ⟨factor, factorPositive, factorLessOne, productGreater⟩
      exact Or.inr ⟨factor, factorLessOne, factorPositive,
        greater, greaterMember, greaterPositive, productGreater⟩

theorem mulNonnegativeOneRight (value : Cut) (nonnegative : 0 ≤ value) :
    mulNonnegative value 1 nonnegative zeroLeOne = value := by
  rw [mulNonnegativeComm value 1 nonnegative zeroLeOne]
  exact mulNonnegativeOneLeft value nonnegative

theorem mulNonnegativeAssoc (left middle right : Cut)
    (leftNonnegative : 0 ≤ left) (middleNonnegative : 0 ≤ middle)
    (rightNonnegative : 0 ≤ right) :
    mulNonnegative
        (mulNonnegative left middle leftNonnegative middleNonnegative)
        right
        (mulNonnegativeNonnegative left middle
          leftNonnegative middleNonnegative)
        rightNonnegative =
      mulNonnegative left
        (mulNonnegative middle right middleNonnegative rightNonnegative)
        leftNonnegative
        (mulNonnegativeNonnegative middle right
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
                (Rational.ltTrans pairPositive pairNegative))
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
          have bound := Rational.ltTrans
            rationalPairRight pairProductBound
          rw [Rat.mul_assoc] at bound
          exact bound
        rcases Rational.existsPosLtOfLtMulLeft
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
                (Rational.ltTrans pairPositive pairNegative))
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
          have bound := Rational.ltTrans rationalLeftPair leftPairBound
          rw [← Rat.mul_assoc] at bound
          exact bound
        rcases Rational.existsPosLtOfLtMulRight
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

end Foundations.Real.Construction.Dedekind
