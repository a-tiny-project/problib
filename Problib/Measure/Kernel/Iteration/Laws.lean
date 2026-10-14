module

public import Problib.Measure.Kernel.Iteration.Basic

set_option autoImplicit false

namespace Problib.Measure.Kernel
open Problib.Real
universe u v
variable {alpha : Type u} {beta : Type v}
  {source : Space alpha} {target : Space beta}

/-- A finite execution prefix cannot return an output when every exit is zero. -/
public theorem prefixApproximant_zero_exit (step : Kernel source source) (count : Nat) :
    prefixApproximant step (Kernel.zero source target) count = Kernel.zero source target := by
  induction count with
  | zero => rfl
  | succ count induction =>
    rw [prefixApproximant_step_unfold, induction, comp_zero, add_zero]

public theorem loop_zero_exit (step : Kernel source source) :
    loop step (Kernel.zero source target) = Kernel.zero source target := by
  apply le_antisymm
  · apply loop_least
    rw [comp_zero, zero_add]
    exact le_refl _
  · exact zero_le _

public theorem loop_immediate_exit (exit : Kernel source target) :
    loop (Kernel.zero source source) exit = exit := by
  rw [loop_unfold, zero_comp, add_zero]

public theorem iterate_zero_step_succ (count : Nat) :
    iterate (Kernel.zero source source) (count + 1) = Kernel.zero source source := by
  rw [iterate_succ, zero_comp]

public theorem iterate_identity (count : Nat) :
    iterate (Kernel.deterministic (fun value => value) (MeasurableMap.identity source)) count =
      Kernel.deterministic (fun value => value) (MeasurableMap.identity source) := by
  induction count with
  | zero => rfl
  | succ count induction =>
    rw [iterate_succ, induction]
    apply Kernel.ext
    intro input
    rw [comp_apply, deterministic_apply, Measure.dirac_bind]
    rfl

public theorem pure_continuation_fixed (candidate : Kernel source target) :
    Kernel.add (Kernel.zero source target)
      ((Kernel.deterministic (fun value => value) (MeasurableMap.identity source)).comp candidate) =
      candidate := by
  rw [zero_add]
  apply Kernel.ext
  intro input
  rw [comp_apply, deterministic_apply, Measure.dirac_bind]

end Problib.Measure.Kernel
