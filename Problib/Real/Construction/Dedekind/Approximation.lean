module

import all Problib.Real.Construction.Dedekind.Order

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

namespace Problib.Real.Construction.Dedekind

namespace Cut

theorem exists_rational_between {left right : Cut}
    (less : left ≤ right ∧ ¬right ≤ left) :
    ∃ rational : Rat,
      left ≤ ofRat rational ∧ ¬ofRat rational ≤ left ∧
        ofRat rational ≤ right ∧ ¬right ≤ ofRat rational := by
  have notAll : ¬∀ value, right.mem value → left.mem value := less.right
  rcases Classical.not_forall.mp notAll with ⟨boundary, notImplication⟩
  have separated : right.mem boundary ∧ ¬left.mem boundary :=
    Classical.not_imp.mp notImplication
  rcases right.no_greatest separated.left with
    ⟨rational, rationalMember, boundaryRational⟩
  have rationalAbsent : ¬left.mem rational := by
    intro rationalLeft
    exact separated.right (left.downward boundaryRational rationalLeft)
  refine ⟨rational, ?_, ?_, ?_, ?_⟩
  · intro value valueMember
    have valueRational := left.le_of_mem_of_not_mem valueMember rationalAbsent
    rcases Rat.le_iff_lt_or_eq.mp valueRational with strict | equal
    · exact strict
    · subst value
      exact False.elim (rationalAbsent valueMember)
  · intro included
    exact separated.right (included boundary boundaryRational)
  · intro value valueRational
    exact right.downward valueRational rationalMember
  · intro included
    rcases right.no_greatest rationalMember with
      ⟨greater, greaterMember, rationalGreater⟩
    have greaterRational := included greater greaterMember
    exact Rat.lt_irrefl
      (Rational.lt_trans rationalGreater greaterRational)

theorem exists_nat_strict_upper (value : Cut) :
    ∃ index : Nat,
      value ≤ ofRat (index : Rat) ∧ ¬ofRat (index : Rat) ≤ value := by
  rcases value.proper with ⟨outside, outsideAbsent⟩
  rcases Construction.Rational.exists_nat_gt outside with ⟨index, outsideIndex⟩
  refine ⟨index, ?_, ?_⟩
  · intro rational member
    have rationalOutside := value.le_of_mem_of_not_mem member outsideAbsent
    exact Rational.lt_of_le_of_lt rationalOutside outsideIndex
  · intro included
    exact outsideAbsent (included outside outsideIndex)

theorem exists_nat_upper (value : Cut) :
    ∃ index : Nat, value ≤ ofRat (index : Rat) := by
  rcases Cut.exists_nat_strict_upper value with ⟨index, included, _strict⟩
  exact ⟨index, included⟩

end Cut

end Problib.Real.Construction.Dedekind
