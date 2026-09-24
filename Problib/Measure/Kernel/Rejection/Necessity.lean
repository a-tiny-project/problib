module

public import Problib.Measure.Kernel.Rejection.Bounded

set_option autoImplicit false

namespace Problib.Measure.Kernel.Rejection.Necessity
open Problib.Real
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
  · rw [Kernel.zero_apply, Measure.zero_apply, ENNReal.add_zero]
  · intro probability
    have mass := probability.univ_eq_one
    rw [loop_zero_exit, Kernel.zero_apply, Measure.zero_apply] at mass
    exact ENNReal.one_ne_zero mass.symm

/-- The zero-budget success measure is not normalizable, even with positive acceptance. -/
public theorem zero_budget (weight : alpha → ENNReal)
    (measurable : ENNRealMeasurable source weight) (exit : Kernel source target) (input : alpha) :
    ¬Measure.IsNormalizable (prefixApproximant (retry weight measurable) exit 0 input) :=
  Measure.zero_not_normalizable target

/-- Certain rejection returns exhaustion at the initial state for every finite budget. -/
public theorem zero_acceptance_bounded (count : Nat) :
    boundedLoop (retry (fun _ : alpha => ENNReal.one)
        (ENNRealMeasurable.constant source ENNReal.one)) (Kernel.zero source target) count =
      Kernel.deterministic Sum.inl (MeasurableMap.inl source target) := by
  rw [boundedLoop_zero_exit]
  apply Kernel.ext
  intro input
  rw [map_apply, retry_residual, ENNReal.pow_one, Measure.one_smul,
    Measure.map_dirac, deterministic_apply]

end Problib.Measure.Kernel.Rejection.Necessity
