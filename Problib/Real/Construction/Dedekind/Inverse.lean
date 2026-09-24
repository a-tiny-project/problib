module

public import Problib.Real.Construction.Dedekind.MultiplicativeSelection
import all Problib.Real.Construction.Dedekind.MultiplicativeSelection
import all Problib.Real.Construction.Dedekind.Archimedean
import all Problib.Real.Construction.Dedekind.Multiplication

set_option autoImplicit false

/-
Copyright (c) 2026 Si-Qi Liu.
Licensed under the MIT License.

Adapted from Tautology/RealBasic/ModuleBackend/Dedekind/InvPos.lean and
Inv.lean at commit 261012c7540673d59a4015371b7618b7573d43da.

Tiny uses explicit selected-carrier operations and the existing generic signed
multiplication extension. Names and proof packaging change.
-/

namespace Problib.Real.Construction.Dedekind

namespace Rational

theorem inverse_positive {value : Rat} (positive : 0 < value) :
    0 < value⁻¹ :=
  Rat.inv_pos.mpr positive

theorem inverse_lt_inverse_of_positive_lt {left right : Rat}
    (leftPositive : 0 < left) (rightPositive : 0 < right)
    (leftRight : left < right) : right⁻¹ < left⁻¹ := by
  rw [← Rat.one_mul left⁻¹, ← Rat.div_def 1 left]
  apply (Rat.lt_div_iff leftPositive).mpr
  have quotientLess : left / right < 1 := by
    apply (Rat.div_lt_iff rightPositive).mpr
    rw [Rat.one_mul]
    exact leftRight
  rw [Rat.div_def, Rat.mul_comm] at quotientLess
  exact quotientLess

theorem lt_of_inverse_lt_inverse_of_positive {left right : Rat}
    (leftPositive : 0 < left) (rightPositive : 0 < right)
    (inverseLess : left⁻¹ < right⁻¹) : right < left := by
  have reversed := inverse_lt_inverse_of_positive_lt
    (inverse_positive leftPositive) (inverse_positive rightPositive)
    inverseLess
  simpa only [Rat.inv_inv] using reversed

theorem mul_lt_one_of_le_of_positive_of_lt_inverse {left factor upper : Rat}
    (leftUpper : left ≤ upper) (factorPositive : 0 < factor)
    (upperPositive : 0 < upper) (factorInverse : factor < upper⁻¹) :
    left * factor < 1 := by
  have first : left * factor ≤ upper * factor :=
    Rat.mul_le_mul_of_nonneg_right leftUpper (Rat.le_of_lt factorPositive)
  have second : upper * factor < upper * upper⁻¹ :=
    Rat.mul_lt_mul_of_pos_left factorInverse upperPositive
  rw [Rat.mul_inv_cancel upper (Rat.ne_of_gt upperPositive)] at second
  exact Problib.Real.Construction.Rational.lt_of_le_of_lt first second

private theorem sub_sub_self (boundary inside : Rat) :
    boundary - (boundary - inside) = inside := by
  rw [Rat.sub_eq_add_neg, Rat.sub_eq_add_neg, Rat.neg_add,
    ← Rat.add_assoc, Rat.add_neg_cancel, Rat.zero_add, Rat.neg_neg]

private theorem mul_complement (value boundary : Rat) :
    value * boundary + (1 - value) * boundary = boundary := by
  rw [← Rat.add_mul]
  have sumOne : value + (1 - value) = 1 := by
    rw [Rat.sub_eq_add_neg, ← Rat.add_assoc, Rat.add_comm value 1,
      Rat.add_assoc, Rat.add_neg_cancel, Rat.add_zero]
  rw [sumOne, Rat.one_mul]

theorem mul_lt_of_gap {value inside outside lower : Rat}
    (valueOne : value < 1) (lowerOutside : lower < outside)
    (gap : outside - inside < (1 - value) * lower) :
    value * outside < inside := by
  have complementPositive : 0 < 1 - value :=
    (Rat.lt_iff_sub_pos value 1).mp valueOne
  have scaledLower :
      (1 - value) * lower < (1 - value) * outside :=
    Rat.mul_lt_mul_of_pos_left lowerOutside complementPositive
  have scaledGap : outside - inside < (1 - value) * outside :=
    Problib.Real.Construction.Rational.lt_trans gap scaledLower
  have sumLess :
      value * outside + (outside - inside) <
        value * outside + (1 - value) * outside :=
    (Rat.add_lt_add_left (c := value * outside)).mpr scaledGap
  rw [mul_complement value outside] at sumLess
  have result : value * outside < outside - (outside - inside) :=
    (Rat.lt_sub_right_iff_add_lt).mpr sumLess
  rw [sub_sub_self] at result
  exact result

theorem sub_lt_sub_left_of_lt {left right boundary : Rat}
    (leftRight : left < right) : boundary - right < boundary - left := by
  apply (Rat.sub_lt_iff).mpr
  have shifted : boundary - left + left < boundary - left + right :=
    (Rat.add_lt_add_left (c := boundary - left)).mpr leftRight
  rw [Rat.sub_add_cancel] at shifted
  exact shifted

end Rational

namespace Cut

theorem exists_positive_member (cut : Cut)
    (positive : (0 : Cut) ≤ cut ∧ ¬cut ≤ 0) :
    ∃ value, cut.mem value ∧ 0 < value := by
  have notAll : ¬∀ value, cut.mem value → (0 : Cut).mem value :=
    positive.right
  rcases Classical.not_forall.mp notAll with ⟨value, notImplication⟩
  have separated : cut.mem value ∧ ¬(0 : Cut).mem value :=
    Classical.not_imp.mp notImplication
  have valueNonnegative : 0 ≤ value := Rat.not_lt.mp separated.right
  rcases cut.no_greatest separated.left with
    ⟨greater, greaterMember, valueGreater⟩
  exact ⟨greater, greaterMember,
    Problib.Real.Construction.Rational.lt_of_le_of_lt
      valueNonnegative valueGreater⟩

def inversePositive (cut : Cut)
    (positive : (0 : Cut) ≤ cut ∧ ¬cut ≤ 0) : Cut where
  mem value := value < 0 ∨
    ∃ upper, ¬cut.mem upper ∧ 0 < upper ∧ value < upper⁻¹
  nonempty := ⟨0 - 1,
    Or.inl (Problib.Real.Construction.Rational.sub_one_lt 0)⟩
  proper := by
    rcases exists_positive_member cut positive with
      ⟨inside, insideMember, insidePositive⟩
    refine ⟨inside⁻¹, ?_⟩
    intro member
    rcases member with inverseNegative | witness
    · have inversePositive := Rational.inverse_positive insidePositive
      exact Rat.lt_irrefl
        (Problib.Real.Construction.Rational.lt_trans
          inversePositive inverseNegative)
    · rcases witness with
        ⟨outside, outsideAbsent, outsidePositive, inverseLess⟩
      have outsideInside := Rational.lt_of_inverse_lt_inverse_of_positive
        insidePositive outsidePositive inverseLess
      exact outsideAbsent (cut.downward outsideInside insideMember)
  downward := by
    intro smaller value smallerValue member
    rcases member with valueNegative | witness
    · exact Or.inl (Problib.Real.Construction.Rational.lt_trans
        smallerValue valueNegative)
    · rcases witness with
        ⟨upper, upperAbsent, upperPositive, valueUpper⟩
      exact Or.inr ⟨upper, upperAbsent, upperPositive,
        Problib.Real.Construction.Rational.lt_trans
          smallerValue valueUpper⟩
  no_greatest := by
    intro value member
    rcases member with valueNegative | witness
    · rcases Problib.Real.Construction.Rational.exists_between
        valueNegative with ⟨greater, valueGreater, greaterNegative⟩
      exact ⟨greater, Or.inl greaterNegative, valueGreater⟩
    · rcases witness with
        ⟨upper, upperAbsent, upperPositive, valueUpper⟩
      rcases Problib.Real.Construction.Rational.exists_between valueUpper with
        ⟨greater, valueGreater, greaterUpper⟩
      exact ⟨greater,
        Or.inr ⟨upper, upperAbsent, upperPositive, greaterUpper⟩,
        valueGreater⟩

theorem inversePositive_nonnegative (cut : Cut)
    (positive : (0 : Cut) ≤ cut ∧ ¬cut ≤ 0) :
    0 ≤ inversePositive cut positive := by
  intro value negative
  exact Or.inl negative

theorem mulNonnegative_inversePositive_le_one (cut : Cut)
    (positive : (0 : Cut) ≤ cut ∧ ¬cut ≤ 0) :
    mulNonnegative cut (inversePositive cut positive)
      positive.left (inversePositive_nonnegative cut positive) ≤ 1 := by
  intro value member
  rcases member with valueNegative | product
  · exact Problib.Real.Construction.Rational.lt_of_lt_of_le
      valueNegative (by decide)
  · rcases product with
      ⟨left, leftMember, leftPositive,
        right, rightMember, rightPositive, valueProduct⟩
    rcases rightMember with rightNegative | inverseMember
    · exact False.elim (Rat.lt_irrefl
        (Problib.Real.Construction.Rational.lt_trans
          rightPositive rightNegative))
    · rcases inverseMember with
        ⟨upper, upperAbsent, upperPositive, rightInverse⟩
      have leftUpper := cut.le_of_mem_of_not_mem leftMember upperAbsent
      have productOne := Rational.mul_lt_one_of_le_of_positive_of_lt_inverse
        leftUpper rightPositive upperPositive rightInverse
      exact Problib.Real.Construction.Rational.lt_trans
        valueProduct productOne

theorem exists_positive_inner_outer_gap_lt_with_lower
    (cut : Cut) {lower epsilon : Rat}
    (lowerMember : cut.mem lower) (lowerPositive : 0 < lower)
    (epsilonPositive : 0 < epsilon) :
    ∃ inside, cut.mem inside ∧ 0 < inside ∧ lower < inside ∧
      ∃ outside, ¬cut.mem outside ∧ 0 < outside ∧ lower < outside ∧
        outside - inside < epsilon := by
  rcases cut.exists_inner_outer_gap_lt epsilonPositive with
    ⟨initialInside, initialInsideMember,
      initialOutside, initialOutsideAbsent, initialGap⟩
  rcases cut.exists_member_above_both initialInsideMember lowerMember with
    ⟨inside, insideMember, initialInsideLess, lowerInside⟩
  have insideOutside := cut.le_of_mem_of_not_mem
    insideMember initialOutsideAbsent
  have gap : initialOutside - inside < epsilon := by
    rcases Rat.le_iff_lt_or_eq.mp insideOutside with less | equal
    · exact Problib.Real.Construction.Rational.lt_trans
        (Rational.sub_lt_sub_left_of_lt initialInsideLess) initialGap
    · subst initialOutside
      rw [Rat.sub_self]
      exact epsilonPositive
  have outsidePositive :=
    Problib.Real.Construction.Rational.lt_of_lt_of_le
      (Problib.Real.Construction.Rational.lt_trans
        lowerPositive lowerInside) insideOutside
  have lowerOutside :=
    Problib.Real.Construction.Rational.lt_of_lt_of_le
      lowerInside insideOutside
  exact ⟨inside, insideMember,
    Problib.Real.Construction.Rational.lt_trans
      lowerPositive lowerInside,
    lowerInside, initialOutside, initialOutsideAbsent,
    outsidePositive, lowerOutside, gap⟩

theorem one_le_mulNonnegative_inversePositive (cut : Cut)
    (positive : (0 : Cut) ≤ cut ∧ ¬cut ≤ 0) :
    1 ≤ mulNonnegative cut (inversePositive cut positive)
      positive.left (inversePositive_nonnegative cut positive) := by
  intro value valueOne
  by_cases valueNegative : value < 0
  · exact Or.inl valueNegative
  · have valueNonnegative : 0 ≤ value := Rat.not_lt.mp valueNegative
    rcases exists_positive_member cut positive with
      ⟨lower, lowerMember, lowerPositive⟩
    have complementPositive : 0 < 1 - value :=
      (Rat.lt_iff_sub_pos value 1).mp valueOne
    have epsilonPositive : 0 < (1 - value) * lower :=
      Rat.mul_pos complementPositive lowerPositive
    rcases exists_positive_inner_outer_gap_lt_with_lower cut
        lowerMember lowerPositive epsilonPositive with
      ⟨inside, insideMember, insidePositive, _lowerInside,
        outside, outsideAbsent, outsidePositive, lowerOutside, gap⟩
    have valueOutside : value * outside < inside :=
      Rational.mul_lt_of_gap valueOne lowerOutside gap
    have valueProduct : value < inside * outside⁻¹ := by
      have divided := (Rat.lt_div_iff outsidePositive).mpr valueOutside
      rw [Rat.div_def] at divided
      exact divided
    rcases Problib.Real.Construction.Rational.exists_pos_lt_of_lt_mul_left
        valueNonnegative insidePositive valueProduct with
      ⟨factor, factorPositive, valueFactor, factorInverse⟩
    exact Or.inr ⟨inside, insideMember, insidePositive,
      factor,
      Or.inr ⟨outside, outsideAbsent, outsidePositive, factorInverse⟩,
      factorPositive, valueFactor⟩

theorem mulNonnegative_inversePositive (cut : Cut)
    (positive : (0 : Cut) ≤ cut ∧ ¬cut ≤ 0) :
    mulNonnegative cut (inversePositive cut positive)
      positive.left (inversePositive_nonnegative cut positive) = 1 :=
  Cut.le_antisymm
    (mulNonnegative_inversePositive_le_one cut positive)
    (one_le_mulNonnegative_inversePositive cut positive)

public theorem exists_selected_positive_inverse (value : selection.Carrier)
    (positive : lt zero value) :
    ∃ result, le zero result ∧ mul value result = one := by
  refine ⟨inversePositive value positive,
    inversePositive_nonnegative value positive, ?_⟩
  rw [mul_eq_ring_mul, one_eq_ring_one]
  rw [ring_mul]
  rw [Problib.Algebra.NonnegativeMultiplicationKernel.signedMul_of_nonnegative_of_nonnegative
      additive.linearlyOrderedGroup multiplicationKernel
      positive.left (inversePositive_nonnegative value positive)]
  exact mulNonnegative_inversePositive value positive

end Cut

end Problib.Real.Construction.Dedekind
