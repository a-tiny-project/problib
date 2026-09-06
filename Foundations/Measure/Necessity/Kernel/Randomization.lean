module

public import Foundations.Measure.Kernel.Randomization.Basic

set_option autoImplicit false

namespace Foundations.Measure.Necessity

open Foundations.Real

universe u v

/-- The zero kernel admits no Uniform randomizer when the parameter space is inhabited. -/
public theorem zero_not_randomizable {alpha : Type u} {beta : Type v}
    (source : Space alpha) (target : Space beta) (input : alpha) :
    ¬Nonempty (Kernel.Randomizer (Kernel.zero source target)) := by
  rintro ⟨selection⟩
  have total := (selection.isProbability input).univ_eq_one
  change (Measure.zero target) Set.univ = ENNReal.one at total
  rw [Measure.zero_apply] at total
  exact ENNReal.oneNeZero total.symm

end Foundations.Measure.Necessity
