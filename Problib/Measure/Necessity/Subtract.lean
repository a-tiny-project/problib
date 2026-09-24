module

public import Problib.Measure.Additive.Counting

set_option autoImplicit false

/-!
Necessity witnesses for measure subtraction.

Two finite Dirac measures on `Bool` witness that pointwise difference fails to
define a measure without domination. For `left = counting + counting` and
`right = counting` on `Nat`, the pointwise formula gives singleton mass one and
universal mass zero. Counting measure itself is an additive residual in that
example. The witness refutes the global pointwise subtraction formula under
sigma-finiteness alone, rather than existence of every additive residual.
-/

namespace Problib.Measure.Necessity.Subtract

open Problib.Real

/-- Witness failure of pointwise difference to define a measure for two finite
Dirac measures lacking domination. -/
public theorem finite_unordered_difference_not_measure :
    ∃ left right : Measure (Space.discrete Bool),
      Measure.IsFinite left ∧ Measure.IsFinite right ∧
        ¬∃ remainder : Measure (Space.discrete Bool),
          ∀ set, (Space.discrete Bool).Measurable set →
            remainder set = ENNReal.sub (left set) (right set) := by
  refine ⟨Measure.dirac (Space.discrete Bool) false,
    Measure.dirac (Space.discrete Bool) true,
    Measure.IsFinite.dirac _ _, Measure.IsFinite.dirac _ _, ?_⟩
  rintro ⟨remainder, values⟩
  have total := values Set.univ (Space.discrete Bool).univ
  rw [Measure.dirac_apply_univ, Measure.dirac_apply_univ, ENNReal.sub_self] at total
  have singleton := values (fun value => value = false) True.intro
  rw [Measure.dirac_apply_of_mem (Space.discrete Bool) false
      (set := fun value => value = false) True.intro rfl,
    Measure.dirac_apply_of_not_mem (Space.discrete Bool) true
      (set := fun value => value = false) True.intro (by decide), ENNReal.sub_zero] at singleton
  have included := remainder.mono (Set.subset_univ (fun value => value = false))
  rw [singleton, total] at included
  exact ENNReal.one_ne_zero (ENNReal.eq_zero_of_le_zero included)

/-- Witness failure of the global pointwise subtraction formula under
sigma-finiteness alone for `counting + counting` and `counting`. -/
public theorem infinite_dominated_difference_not_measure :
    ∃ left right : Measure (Space.discrete Nat),
      Nonempty (Measure.SigmaFinite left) ∧ Nonempty (Measure.SigmaFinite right) ∧
        (∀ set, (Space.discrete Nat).Measurable set → ENNReal.le (right set) (left set)) ∧
        ¬∃ remainder : Measure (Space.discrete Nat),
          ∀ set, (Space.discrete Nat).Measurable set →
            remainder set = ENNReal.sub (left set) (right set) := by
  refine ⟨Measure.add Measure.counting Measure.counting, Measure.counting,
    ?_, ⟨Measure.counting_sigmaFinite⟩, ?_, ?_⟩
  · refine ⟨Measure.SigmaFinite.ofCover {
      sets := fun point value => value = point
      measurable := fun _ => True.intro
      finite := ?_
      cover := ?_
    }⟩
    · intro point
      rw [Measure.add_apply_measurable _ _ True.intro, Measure.counting_singleton]
      exact ENNReal.add_finite True.intro True.intro
    · apply Set.ext
      intro value
      exact ⟨fun _ => True.intro, fun _ => ⟨value, rfl⟩⟩
  · intro set measurable
    rw [Measure.add_apply_measurable _ _ measurable]
    have included := ENNReal.add_le_add_right (ENNReal.zero_le (Measure.counting set))
      (Measure.counting set)
    rw [ENNReal.zero_add] at included
    exact included
  · rintro ⟨remainder, values⟩
    have total := values Set.univ (Space.discrete Nat).univ
    rw [Measure.add_apply_measurable _ _ (Space.discrete Nat).univ,
      Measure.counting_univ, ENNReal.top_add, ENNReal.sub_self] at total
    have singleton := values (fun value => value = 0) True.intro
    rw [Measure.add_apply_measurable _ _ True.intro, Measure.counting_singleton,
      ENNReal.add_sub_cancel_right (right := ENNReal.one) True.intro] at singleton
    have included := remainder.mono (Set.subset_univ (fun value => value = 0))
    rw [singleton, total] at included
    exact ENNReal.one_ne_zero (ENNReal.eq_zero_of_le_zero included)

end Problib.Measure.Necessity.Subtract
