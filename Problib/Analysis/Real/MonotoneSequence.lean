module

public import Problib.Analysis.Real.Sequence

/-! Bounded monotone real sequences converge by Dedekind completeness. -/

set_option autoImplicit false

namespace Problib.Analysis.Real

open Problib.Real.Construction.Dedekind

noncomputable section

/-- The least upper bound of the range is the limit of a monotone sequence. -/
public theorem monotone_converges_to_lub
    (values : Nat → selection.Carrier)
    (monotone : ∀ first second, first ≤ second → le (values first) (values second))
    {limit : selection.Carrier}
    (limitUpper : Problib.Real.IsUpperBound le
      (fun value => ∃ index, values index = value) limit)
    (limitLeast : ∀ upper : selection.Carrier,
      Problib.Real.IsUpperBound le
        (fun value => ∃ index, values index = value) upper → le limit upper) :
    ConvergesTo values limit := by
  classical
  intro epsilon positive
  have gapLess : lt (sub limit epsilon) limit := by
    have shifted := add_lt_add_right (sub limit epsilon) positive
    rwa [zero_add, add_comm epsilon (sub limit epsilon), sub_add_cancel] at shifted
  have notUpper : ¬Problib.Real.IsUpperBound le
      (fun value => ∃ index, values index = value) (sub limit epsilon) := by
    intro candidateUpper
    have included := limitLeast (sub limit epsilon) candidateUpper
    exact lt_irrefl _ (lt_of_le_of_lt included gapLess)
  have near : ∃ stage, ¬le (values stage) (sub limit epsilon) := by
    apply Classical.byContradiction
    intro none
    apply notUpper
    intro value member
    rcases member with ⟨index, equal⟩
    subst value
    by_cases included : le (values index) (sub limit epsilon)
    · exact included
    · exact False.elim (none ⟨index, included⟩)
  rcases near with ⟨stage, notIncluded⟩
  refine ⟨stage, fun index later => ?_⟩
  have lower : lt (sub limit epsilon) (values index) :=
    lt_of_lt_of_le (lt_of_not_le notIncluded) (monotone stage index later)
  have shifted := add_lt_add_right epsilon lower
  rw [sub_add_cancel] at shifted
  have upperAtIndex : le (values index) limit :=
    limitUpper (values index) ⟨index, rfl⟩
  rw [abs_sub_comm, abs_of_nonnegative (sub_nonnegative upperAtIndex)]
  apply (add_lt_add_right_iff (left := sub limit (values index))
    (right := epsilon) (shift := values index)).mp
  simpa only [sub_add_cancel, add_comm epsilon (values index)] using shifted

public theorem monotone_bounded_converges
    (values : Nat → selection.Carrier)
    (monotone : ∀ first second, first ≤ second → le (values first) (values second))
    (bounded : ∃ upper : selection.Carrier, ∀ index, le (values index) upper) :
    ∃ limit : selection.Carrier, ConvergesTo values limit := by
  classical
  let range : selection.Carrier → Prop := fun value => ∃ index, values index = value
  have nonempty : ∃ value, range value := ⟨values 0, 0, rfl⟩
  rcases bounded with ⟨upper, upperBound⟩
  have boundedRange : ∃ bound, Problib.Real.IsUpperBound le range bound :=
    ⟨upper, fun value ⟨index, equal⟩ => equal ▸ upperBound index⟩
  rcases exists_lub range nonempty boundedRange with ⟨limit, limitUpper, limitLeast⟩
  exact ⟨limit, monotone_converges_to_lub values monotone limitUpper limitLeast⟩

end

end Problib.Analysis.Real
