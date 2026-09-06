module

import all Foundations.Real.Construction.Dedekind.Basic

/-
Copyright (c) 2026 Si-Qi Liu.
Licensed under the MIT License.

Adapted from Tautology/RealBasic/ModuleBackend/Dedekind/Neg.lean at commit
261012c7540673d59a4015371b7618b7573d43da.

Tiny retains only rounded negation and its cut-closure proof.
-/

namespace Foundations.Real.Construction.Dedekind

namespace Cut

def neg (cut : Cut) : Cut where
  mem value := ∃ outside : Rat, ¬cut.mem outside ∧ value < -outside
  nonempty := by
    rcases cut.proper with ⟨outside, absent⟩
    exact ⟨-outside - 1, outside, absent, Rational.subOneLt (-outside)⟩
  proper := by
    rcases cut.nonempty with ⟨inside, member⟩
    refine ⟨-inside, ?_⟩
    rintro ⟨outside, absent, less⟩
    have outsideInside : outside < inside :=
      (Rat.neg_lt_neg_iff (a := inside) (b := outside)).mp less
    exact absent (cut.downward outsideInside member)
  downward := by
    intro smaller value smallerValue
    rintro ⟨outside, absent, valueOutside⟩
    exact ⟨outside, absent, Rational.ltTrans smallerValue valueOutside⟩
  noGreatest := by
    intro value
    rintro ⟨outside, absent, valueOutside⟩
    rcases Rational.existsBetween valueOutside with
      ⟨greater, valueGreater, greaterOutside⟩
    exact ⟨greater, ⟨outside, absent, greaterOutside⟩, valueGreater⟩

instance : Neg Cut where
  neg := neg

end Cut

end Foundations.Real.Construction.Dedekind
