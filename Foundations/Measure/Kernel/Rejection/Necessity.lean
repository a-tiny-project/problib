module

public import Foundations.Measure.Kernel.Rejection.Basic

set_option autoImplicit false

namespace Foundations.Measure.Kernel.Rejection.Necessity
open Foundations.Real
universe u v
variable {alpha : Type u} {beta : Type v}
  {source : Space alpha} {target : Space beta}

/-- Zero acceptance conserves mass by retrying forever, but its least output is zero. -/
public theorem zero_acceptance (input : alpha) :
    let weight := fun _ : alpha => ENNReal.one
    let measurable := ENNRealMeasurable.constant source ENNReal.one
    let exit := Kernel.zero source target
    ENNReal.add (weight input) (exit input Set.univ) = ENNReal.one ∧
      loop (retry weight measurable) exit = Kernel.zero source target ∧
      ¬Measure.IsProbability (loop (retry weight measurable) exit input) := by
  dsimp only
  refine ⟨?_, loop_zero_exit _, ?_⟩
  · rw [Kernel.zero_apply, Measure.zero_apply, ENNReal.addZero]
  · intro probability
    have mass := probability.univ_eq_one
    rw [loop_zero_exit, Kernel.zero_apply, Measure.zero_apply] at mass
    exact ENNReal.oneNeZero mass.symm

end Foundations.Measure.Kernel.Rejection.Necessity
