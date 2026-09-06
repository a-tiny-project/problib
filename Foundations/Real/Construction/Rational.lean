module

import Init.Data.Rat.Lemmas

/-
Copyright (c) 2026 Si-Qi Liu.
Licensed under the MIT License.

Adapted from Tautology/RealBasic/ModuleBackend/Rat.lean at commit
261012c7540673d59a4015371b7618b7573d43da.

Tiny retains only the strict-order, density, Archimedean, and positive-product
helpers used by the cut construction. Names change for Lean 4.31.
-/

namespace Foundations.Real.Construction.Rational

theorem ltTrans {left middle right : Rat}
    (leftMiddle : left < middle) (middleRight : middle < right) :
    left < right := by
  have leftRight : left ≤ right :=
    Rat.le_trans (Rat.le_of_lt leftMiddle) (Rat.le_of_lt middleRight)
  apply Rat.lt_of_le_of_ne leftRight
  intro equal
  subst equal
  have middleLeft : middle = left :=
    Rat.le_antisymm (Rat.le_of_lt middleRight) (Rat.le_of_lt leftMiddle)
  rw [middleLeft] at middleRight
  exact Rat.lt_irrefl middleRight

theorem ltOfLeOfLt {left middle right : Rat}
    (leftMiddle : left ≤ middle) (middleRight : middle < right) :
    left < right := by
  have leftRight : left ≤ right :=
    Rat.le_trans leftMiddle (Rat.le_of_lt middleRight)
  apply Rat.lt_of_le_of_ne leftRight
  intro equal
  subst equal
  have middleLeft : middle = left :=
    Rat.le_antisymm (Rat.le_of_lt middleRight) leftMiddle
  rw [middleLeft] at middleRight
  exact Rat.lt_irrefl middleRight

theorem ltOfLtOfLe {left middle right : Rat}
    (leftMiddle : left < middle) (middleRight : middle ≤ right) :
    left < right := by
  have leftRight : left ≤ right :=
    Rat.le_trans (Rat.le_of_lt leftMiddle) middleRight
  apply Rat.lt_of_le_of_ne leftRight
  intro equal
  subst equal
  have leftMiddleEqual : left = middle :=
    Rat.le_antisymm (Rat.le_of_lt leftMiddle) middleRight
  rw [leftMiddleEqual] at leftMiddle
  exact Rat.lt_irrefl leftMiddle

theorem addLtAdd {firstLeft firstRight secondLeft secondRight : Rat}
    (firstLess : firstLeft < firstRight)
    (secondLess : secondLeft < secondRight) :
    firstLeft + secondLeft < firstRight + secondRight := by
  have firstStep : firstLeft + secondLeft < firstRight + secondLeft :=
    (Rat.add_lt_add_right
      (a := firstLeft) (b := firstRight) (c := secondLeft)).mpr firstLess
  have secondStep : firstRight + secondLeft < firstRight + secondRight :=
    (Rat.add_lt_add_left
      (a := secondLeft) (b := secondRight) (c := firstRight)).mpr secondLess
  exact ltTrans firstStep secondStep

theorem subOneLt (value : Rat) : value - 1 < value := by
  apply (Rat.sub_lt_iff (a := value) (b := value) (c := 1)).mpr
  have zeroOne : (0 : Rat) < 1 := by decide
  have result : value + 0 < value + 1 :=
    (Rat.add_lt_add_left (a := 0) (b := 1) (c := value)).mpr zeroOne
  rw [Rat.add_zero] at result
  exact result

private theorem twoEqOneAddOne : (2 : Rat) = 1 + 1 := by
  simp [Rat.add_def']
  rfl

private theorem mulTwo (value : Rat) : value * 2 = value + value := by
  rw [twoEqOneAddOne, Rat.mul_add]
  simp

theorem existsBetween {left right : Rat} (less : left < right) :
    ∃ middle, left < middle ∧ middle < right := by
  let middle := (left + right) / 2
  have twoPositive : (0 : Rat) < 2 := by decide
  have leftBound : left * 2 < left + right := by
    have result : left + left < left + right :=
      (Rat.add_lt_add_left (a := left) (b := right) (c := left)).mpr less
    rw [mulTwo]
    exact result
  have rightBound : left + right < right * 2 := by
    have result : left + right < right + right :=
      (Rat.add_lt_add_right (a := left) (b := right) (c := right)).mpr less
    rw [mulTwo]
    exact result
  refine ⟨middle, ?_, ?_⟩
  · exact (Rat.lt_div_iff twoPositive).mpr leftBound
  · exact (Rat.div_lt_iff twoPositive).mpr rightBound

def step (start stride : Rat) : Nat → Rat
  | 0 => start
  | index + 1 => step start stride index + stride

private theorem stepEq (start stride : Rat) (index : Nat) :
    step start stride index = start + (index : Rat) * stride := by
  induction index with
  | zero =>
      simp [step, Rat.add_zero, Rat.zero_mul]
  | succ index inductionHypothesis =>
      rw [step, inductionHypothesis, Rat.natCast_add, Rat.add_mul]
      change start + ↑index * stride + stride =
        start + (↑index * stride + 1 * stride)
      rw [Rat.one_mul, Rat.add_assoc]

private theorem existsNatGt (value : Rat) :
    ∃ index : Nat, value < (index : Rat) := by
  let integer : Int := value.floor + 1
  have valueInteger : value < (integer : Rat) := by
    simpa [integer] using Rat.lt_floor_add_one value
  by_cases integerNonpositive : integer ≤ 0
  · have castNonpositive : (integer : Rat) ≤ 0 :=
      Rat.intCast_le_intCast.mpr integerNonpositive
    exact ⟨0, ltOfLtOfLe valueInteger castNonpositive⟩
  · have integerNonnegative : 0 ≤ integer :=
      Int.le_of_lt (Int.not_le.mp integerNonpositive)
    let index : Nat := integer.toNat
    have indexInteger : (index : Int) = integer :=
      Int.toNat_of_nonneg integerNonnegative
    have castEqual : (index : Rat) = (integer : Rat) := by
      rw [← Rat.intCast_natCast, indexInteger]
    exact ⟨index, by rw [castEqual]; exact valueInteger⟩

theorem existsStepGt (start boundary stride : Rat)
    (stridePositive : 0 < stride) :
    ∃ index : Nat, boundary < step start stride index := by
  rcases existsNatGt ((boundary - start) / stride) with
    ⟨index, quotientBound⟩
  have differenceBound : boundary - start < (index : Rat) * stride :=
    (Rat.div_lt_iff stridePositive).mp quotientBound
  have reordered : boundary < (index : Rat) * stride + start :=
    (Rat.sub_lt_iff
      (a := boundary) (b := (index : Rat) * stride) (c := start)).mp
      differenceBound
  refine ⟨index, ?_⟩
  rw [stepEq, Rat.add_comm]
  exact reordered

theorem halfPos {value : Rat} (positive : 0 < value) :
    0 < value / 2 := by
  have twoPositive : (0 : Rat) < 2 := by decide
  apply (Rat.lt_div_iff twoPositive).mpr
  rw [Rat.zero_mul]
  exact positive

theorem halfLt {value : Rat} (positive : 0 < value) :
    value / 2 < value := by
  have twoPositive : (0 : Rat) < 2 := by decide
  apply (Rat.div_lt_iff twoPositive).mpr
  rw [mulTwo]
  have result : value + 0 < value + value :=
    (Rat.add_lt_add_left (a := 0) (b := value) (c := value)).mpr positive
  rw [Rat.add_zero] at result
  exact result

theorem mulLeMulOfLeOfLeOfPosOfPos {firstLeft firstRight secondLeft secondRight : Rat}
    (firstIncluded : firstLeft ≤ firstRight)
    (secondIncluded : secondLeft ≤ secondRight)
    (secondLeftPositive : 0 < secondLeft)
    (firstRightPositive : 0 < firstRight) :
    firstLeft * secondLeft ≤ firstRight * secondRight := by
  have firstStep : firstLeft * secondLeft ≤ firstRight * secondLeft := by
    rcases Rat.le_iff_lt_or_eq.mp firstIncluded with firstLess | firstEqual
    · exact Rat.le_of_lt
        (Rat.mul_lt_mul_of_pos_right firstLess secondLeftPositive)
    · rw [firstEqual]
      exact Rat.le_refl
  have secondStep : firstRight * secondLeft ≤ firstRight * secondRight := by
    rcases Rat.le_iff_lt_or_eq.mp secondIncluded with secondLess | secondEqual
    · exact Rat.le_of_lt
        (Rat.mul_lt_mul_of_pos_left secondLess firstRightPositive)
    · rw [secondEqual]
      exact Rat.le_refl
  exact Rat.le_trans firstStep secondStep

theorem mulLtOfLtOneOfPos {left right : Rat}
    (leftLessOne : left < 1) (rightPositive : 0 < right) :
    left * right < right := by
  have result : left * right < 1 * right :=
    Rat.mul_lt_mul_of_pos_right leftLessOne rightPositive
  rw [Rat.one_mul] at result
  exact result

theorem existsPosLtOneMulGt {lower upper : Rat}
    (lowerNonnegative : 0 ≤ lower) (lowerUpper : lower < upper) :
    ∃ factor, 0 < factor ∧ factor < 1 ∧ lower < factor * upper := by
  have upperPositive : 0 < upper := ltOfLeOfLt lowerNonnegative lowerUpper
  have quotientLessOne : lower / upper < 1 := by
    apply (Rat.div_lt_iff upperPositive).mpr
    rw [Rat.one_mul]
    exact lowerUpper
  rcases existsBetween quotientLessOne with ⟨factor, lowerFactor, factorOne⟩
  have quotientNonnegative : 0 ≤ lower / upper := by
    apply Rat.not_lt.mp
    intro quotientNegative
    have lowerNegative : lower < 0 := by
      have result : lower < 0 * upper :=
        (Rat.div_lt_iff upperPositive).mp quotientNegative
      rw [Rat.zero_mul] at result
      exact result
    exact (Rat.not_lt.mpr lowerNonnegative) lowerNegative
  have factorPositive : 0 < factor :=
    ltOfLeOfLt quotientNonnegative lowerFactor
  have productBound : lower < factor * upper :=
    (Rat.div_lt_iff upperPositive).mp lowerFactor
  exact ⟨factor, factorPositive, factorOne, productBound⟩

theorem existsPosLtOfLtMulLeft {lower factor upper : Rat}
    (lowerNonnegative : 0 ≤ lower) (factorPositive : 0 < factor)
    (productBound : lower < factor * upper) :
    ∃ smaller, 0 < smaller ∧ lower < factor * smaller ∧ smaller < upper := by
  have quotientBound : lower / factor < upper := by
    apply (Rat.div_lt_iff factorPositive).mpr
    rw [Rat.mul_comm]
    exact productBound
  rcases existsBetween quotientBound with
    ⟨smaller, quotientSmaller, smallerUpper⟩
  have quotientNonnegative : 0 ≤ lower / factor := by
    apply Rat.not_lt.mp
    intro quotientNegative
    have lowerNegative : lower < 0 := by
      have result : lower < 0 * factor :=
        (Rat.div_lt_iff factorPositive).mp quotientNegative
      rw [Rat.zero_mul] at result
      exact result
    exact (Rat.not_lt.mpr lowerNonnegative) lowerNegative
  have smallerPositive : 0 < smaller :=
    ltOfLeOfLt quotientNonnegative quotientSmaller
  have lowerProduct : lower < factor * smaller := by
    have reordered : lower < smaller * factor :=
      (Rat.div_lt_iff factorPositive).mp quotientSmaller
    rw [Rat.mul_comm] at reordered
    exact reordered
  exact ⟨smaller, smallerPositive, lowerProduct, smallerUpper⟩

theorem existsPosLtOfLtMulRight {lower upper factor : Rat}
    (lowerNonnegative : 0 ≤ lower) (factorPositive : 0 < factor)
    (productBound : lower < upper * factor) :
    ∃ smaller, 0 < smaller ∧ lower < smaller * factor ∧ smaller < upper := by
  have reordered : lower < factor * upper := by
    rw [Rat.mul_comm]
    exact productBound
  rcases existsPosLtOfLtMulLeft lowerNonnegative factorPositive reordered with
    ⟨smaller, smallerPositive, lowerProduct, smallerUpper⟩
  have restored : lower < smaller * factor := by
    rw [Rat.mul_comm]
    exact lowerProduct
  exact ⟨smaller, smallerPositive, restored, smallerUpper⟩

end Foundations.Real.Construction.Rational
