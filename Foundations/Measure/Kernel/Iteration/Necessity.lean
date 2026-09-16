module

public import Foundations.Measure.Kernel.Iteration.Laws

set_option autoImplicit false

namespace Foundations.Measure.Kernel
open Foundations.Real
universe u v
variable {alpha : Type u} {beta : Type v}
  {source : Space alpha} {target : Space beta}

namespace Iteration.Necessity

public theorem zero_pair_substochastic (input : alpha) :
    ENNReal.le (ENNReal.add (Kernel.zero source source input Set.univ)
      (Kernel.zero source target input Set.univ)) ENNReal.one := by
  rw [Kernel.zero_apply, Kernel.zero_apply, Measure.zero_apply,
    Measure.zero_apply, ENNReal.zeroAdd]
  exact ENNReal.zeroLe _

public theorem zero_pair_not_conservative (input : alpha) :
    ENNReal.add (Kernel.zero source source input Set.univ)
      (Kernel.zero source target input Set.univ) ≠ ENNReal.one := by
  rw [Kernel.zero_apply, Kernel.zero_apply, Measure.zero_apply,
    Measure.zero_apply, ENNReal.zeroAdd]
  exact fun equal => ENNReal.oneNeZero equal.symm

public theorem vanishing_continuation_without_output (input : alpha) :
    ENNReal.iInf (fun count => iterate (Kernel.zero source source) count input Set.univ) =
        ENNReal.zero ∧
      loop (Kernel.zero source source) (Kernel.zero source target) input Set.univ ≠
        ENNReal.one := by
  constructor
  · apply ENNReal.eqZeroOfLeZero
    have bound := ENNReal.iInfLe
      (fun count => iterate (Kernel.zero source source) count input Set.univ) 1
    rw [iterate_zero_step_succ, Kernel.zero_apply, Measure.zero_apply] at bound
    exact bound
  · rw [loop_zero_exit, Kernel.zero_apply, Measure.zero_apply]
    exact fun equal => ENNReal.oneNeZero equal.symm

public theorem unfolding_does_not_determine_output (input : alpha) (output : beta) :
    let step := Kernel.deterministic (fun value => value) (MeasurableMap.identity source)
    let exit := Kernel.zero source target
    let alternative := Kernel.const source (Measure.dirac target output)
    Kernel.add exit (step.comp alternative) = alternative ∧
      loop step exit ≠ alternative := by
  dsimp
  constructor
  · exact pure_continuation_fixed _
  · rw [loop_zero_exit]
    intro equal
    have mass := congrArg (fun kernel : Kernel source target => kernel input Set.univ) equal
    rw [Kernel.zero_apply, Measure.zero_apply, Kernel.const_apply,
      Measure.dirac_apply_univ] at mass
    exact ENNReal.oneNeZero mass.symm

end Iteration.Necessity
end Foundations.Measure.Kernel
