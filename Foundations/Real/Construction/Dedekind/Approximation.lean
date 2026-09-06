module

import all Foundations.Real.Construction.Dedekind.Order

set_option autoImplicit false

/-
Copyright (c) 2026 Si-Qi Liu.
Licensed under the MIT License.

Adapted from Tautology/RealBasic/ModuleBackend/Dedekind/Order.lean and
Tautology/RealBasic/ModuleBackend/Rat.lean at commit
261012c7540673d59a4015371b7618b7573d43da.

Tiny isolates the rational density and natural cofinality witnesses used by
the sealed selected carrier. Names and proof packaging change.
-/

namespace Foundations.Real.Construction.Dedekind

namespace Rational

private theorem existsNatGt (value : Rat) :
    ∃ index : Nat, value < (index : Rat) := by
  let integer : Int := value.floor + 1
  have valueInteger : value < (integer : Rat) := by
    simpa [integer] using Rat.lt_floor_add_one value
  by_cases integerNonpositive : integer ≤ 0
  · have castNonpositive : (integer : Rat) ≤ 0 :=
      Rat.intCast_le_intCast.mpr integerNonpositive
    exact ⟨0, Foundations.Real.Construction.Rational.ltOfLtOfLe
      valueInteger castNonpositive⟩
  · have integerNonnegative : 0 ≤ integer :=
      Int.le_of_lt (Int.not_le.mp integerNonpositive)
    let index : Nat := integer.toNat
    have indexInteger : (index : Int) = integer :=
      Int.toNat_of_nonneg integerNonnegative
    have castEqual : (index : Rat) = (integer : Rat) := by
      rw [← Rat.intCast_natCast, indexInteger]
    exact ⟨index, by rw [castEqual]; exact valueInteger⟩

end Rational

namespace Cut

theorem existsRationalBetween {left right : Cut}
    (less : left ≤ right ∧ ¬right ≤ left) :
    ∃ rational : Rat,
      left ≤ ofRat rational ∧ ¬ofRat rational ≤ left ∧
        ofRat rational ≤ right ∧ ¬right ≤ ofRat rational := by
  have notAll : ¬∀ value, right.mem value → left.mem value := less.right
  rcases Classical.not_forall.mp notAll with ⟨boundary, notImplication⟩
  have separated : right.mem boundary ∧ ¬left.mem boundary :=
    Classical.not_imp.mp notImplication
  rcases right.noGreatest separated.left with
    ⟨rational, rationalMember, boundaryRational⟩
  have rationalAbsent : ¬left.mem rational := by
    intro rationalLeft
    exact separated.right (left.downward boundaryRational rationalLeft)
  refine ⟨rational, ?_, ?_, ?_, ?_⟩
  · intro value valueMember
    have valueRational := left.leOfMemOfNotMem valueMember rationalAbsent
    rcases Rat.le_iff_lt_or_eq.mp valueRational with strict | equal
    · exact strict
    · subst value
      exact False.elim (rationalAbsent valueMember)
  · intro included
    exact separated.right (included boundary boundaryRational)
  · intro value valueRational
    exact right.downward valueRational rationalMember
  · intro included
    rcases right.noGreatest rationalMember with
      ⟨greater, greaterMember, rationalGreater⟩
    have greaterRational := included greater greaterMember
    exact Rat.lt_irrefl
      (Rational.ltTrans rationalGreater greaterRational)

theorem existsNatStrictUpper (value : Cut) :
    ∃ index : Nat,
      value ≤ ofRat (index : Rat) ∧ ¬ofRat (index : Rat) ≤ value := by
  rcases value.proper with ⟨outside, outsideAbsent⟩
  rcases Rational.existsNatGt outside with ⟨index, outsideIndex⟩
  refine ⟨index, ?_, ?_⟩
  · intro rational member
    have rationalOutside := value.leOfMemOfNotMem member outsideAbsent
    exact Rational.ltOfLeOfLt rationalOutside outsideIndex
  · intro included
    exact outsideAbsent (included outside outsideIndex)

theorem existsNatUpper (value : Cut) :
    ∃ index : Nat, value ≤ ofRat (index : Rat) := by
  rcases existsNatStrictUpper value with ⟨index, included, _strict⟩
  exact ⟨index, included⟩

end Cut

end Foundations.Real.Construction.Dedekind
