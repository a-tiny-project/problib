module

import all Problib.Real.Construction.Dedekind.Add
import all Problib.Real.Construction.Dedekind.Neg
import all Problib.Real.Construction.Dedekind.Archimedean
import all Problib.Real.Construction.Dedekind.Order

/-
Copyright (c) 2026 Si-Qi Liu.
Licensed under the MIT License.

Adapted from Tautology/RealBasic/ModuleBackend/Dedekind/AddInv.lean and
AddOrd.lean at commit 261012c7540673d59a4015371b7618b7573d43da.

Tiny retains only additive inversion and right-translation monotonicity.
-/

namespace Problib.Real.Construction.Dedekind

namespace Cut

theorem add_neg (cut : Cut) : cut + (-cut) = 0 := by
  apply Cut.ext
  intro value
  constructor
  · rintro ⟨inside, insideMember, negated,
        ⟨outside, outsideAbsent, negatedOutside⟩, equal⟩
    have insideOutside : inside ≤ outside :=
      cut.le_of_mem_of_not_mem insideMember outsideAbsent
    have sumLess : inside + negated < inside + -outside :=
      (Rat.add_lt_add_left
        (a := negated) (b := -outside) (c := inside)).mpr
        negatedOutside
    have valueLess : value < inside + -outside := by
      rw [equal]
      exact sumLess
    have sumNonpositive : inside + -outside ≤ 0 := by
      have translated : inside + -outside ≤ outside + -outside :=
        (Rat.add_le_add_right
          (a := inside) (b := outside) (c := -outside)).mpr
          insideOutside
      rw [Rat.add_neg_cancel] at translated
      exact translated
    exact Rational.lt_of_lt_of_le valueLess sumNonpositive
  · intro zeroMember
    have valueNegative : value < 0 := zeroMember
    have negValuePositive : 0 < -value := by
      simpa [Rat.neg_zero] using
        (Rat.neg_lt_neg (a := value) (b := 0) valueNegative)
    rcases cut.exists_inner_outer_gap_lt negValuePositive with
      ⟨inside, insideMember, outside, outsideAbsent, gap⟩
    have valueNegDifference : value < -(outside - inside) :=
      (Rat.lt_neg_iff (a := outside - inside) (b := value)).mp gap
    have valueDifference : value < inside - outside := by
      rw [Rat.neg_sub] at valueNegDifference
      exact valueNegDifference
    have valueSum : value < -outside + inside := by
      rw [Rat.sub_eq_add_neg, Rat.add_comm] at valueDifference
      exact valueDifference
    have adjustedLess : value - inside < -outside :=
      (Rat.sub_lt_iff
        (a := value) (b := -outside) (c := inside)).mpr valueSum
    have equal : inside + (value - inside) = value := by
      rw [Rat.sub_eq_add_neg, Rat.add_comm value (-inside),
        ← Rat.add_assoc, Rat.add_neg_cancel, Rat.zero_add]
    exact ⟨inside, insideMember, value - inside,
      ⟨outside, outsideAbsent, adjustedLess⟩, equal.symm⟩

theorem add_le_add_right {left right : Cut} (included : left ≤ right)
    (shift : Cut) : left + shift ≤ right + shift := by
  intro value
  rintro ⟨leftValue, leftMember, shiftValue, shiftMember, equal⟩
  exact ⟨leftValue, included leftValue leftMember,
    shiftValue, shiftMember, equal⟩

end Cut

end Problib.Real.Construction.Dedekind
