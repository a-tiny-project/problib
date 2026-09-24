module

import all Problib.Real.Construction.Dedekind.Basic

/-
Copyright (c) 2026 Si-Qi Liu.
Licensed under the MIT License.

Adapted from Tautology/RealBasic/ModuleBackend/Dedekind/Archi.lean at commit
261012c7540673d59a4015371b7618b7573d43da.

Tiny retains only the inner-outer rational gap used by additive inversion.
-/

namespace Problib.Real.Construction.Dedekind

namespace Cut

theorem exists_inner_outer_gap_lt (cut : Cut) {epsilon : Rat}
    (epsilonPositive : 0 < epsilon) :
    ∃ inside, cut.mem inside ∧
      ∃ outside, ¬cut.mem outside ∧ outside - inside < epsilon := by
  apply Classical.byContradiction
  intro noGap
  rcases cut.nonempty with ⟨start, startMember⟩
  rcases cut.proper with ⟨boundary, boundaryAbsent⟩
  let stride : Rat := epsilon / 2
  have stridePositive : 0 < stride := Rational.half_pos epsilonPositive
  have strideLess : stride < epsilon := Rational.half_lt epsilonPositive
  have stepMember : ∀ inside, cut.mem inside → cut.mem (inside + stride) := by
    intro inside insideMember
    by_cases nextMember : cut.mem (inside + stride)
    · exact nextMember
    · have gap : (inside + stride) - inside < epsilon := by
        have cancel : (inside + stride) - inside = stride := by
          rw [Rat.add_comm, Rat.add_sub_cancel]
        rw [cancel]
        exact strideLess
      exact False.elim (noGap
        ⟨inside, insideMember, inside + stride, nextMember, gap⟩)
  have allStepsMember :
      ∀ index, cut.mem (Rational.step start stride index) := by
    intro index
    induction index with
    | zero => exact startMember
    | succ index inductionHypothesis =>
        exact stepMember (Rational.step start stride index)
          inductionHypothesis
  rcases Rational.exists_step_gt start boundary stride stridePositive with
    ⟨index, boundaryStep⟩
  exact boundaryAbsent (cut.downward boundaryStep (allStepsMember index))

end Cut

end Problib.Real.Construction.Dedekind
