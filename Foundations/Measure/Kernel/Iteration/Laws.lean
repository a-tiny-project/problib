module

public import Foundations.Measure.Kernel.Iteration.Basic

set_option autoImplicit false

namespace Foundations.Measure.Kernel
open Foundations.Real
universe u v
variable {alpha : Type u} {beta : Type v}
  {source : Space alpha} {target : Space beta}

public theorem loop_zero_exit (step : Kernel source source) :
    loop step (Kernel.zero source target) = Kernel.zero source target := by
  apply leAntisymm
  · apply loop_least
    rw [comp_zero, zero_add]
    exact leRefl _
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

end Foundations.Measure.Kernel
