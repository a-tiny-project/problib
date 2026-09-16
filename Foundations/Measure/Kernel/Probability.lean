module

public import Foundations.Measure.Kernel.Piecewise
public import Foundations.Measure.AlmostEverywhere.Basic

set_option autoImplicit false

namespace Foundations.Measure.Kernel

open Foundations.Real

universe u v

variable {alpha : Type u} {beta : Type v} {source : Space alpha} {target : Space beta}

/-- Repair a kernel into a probability kernel by retaining fibers of mass one and
replacing all other fibers with the Dirac measure at a fallback point. -/
@[expose] public noncomputable def probabilityRepair (kernel : Kernel source target)
    (fallback : beta) : Kernel source target :=
  piecewise (fun input => kernel input Set.univ = ENNReal.one)
    ((kernel.measurable target.univ).eq_set (ENNRealMeasurable.constant source ENNReal.one))
    kernel (Kernel.const source (Measure.dirac target fallback))

/-- Probability repair leaves fibers that are already probability measures
unchanged. -/
public theorem probabilityRepair_eq (kernel : Kernel source target) (fallback : beta)
    (input : alpha) (normalized : Measure.IsProbability (kernel input)) :
    probabilityRepair kernel fallback input = kernel input := by
  unfold probabilityRepair
  exact piecewise_apply_of_mem _ _ _ _ _ normalized.univ_eq_one

/-- Every fiber of a probability-repaired kernel is a probability measure. -/
public theorem probabilityRepair_isProbability (kernel : Kernel source target) (fallback : beta)
    (input : alpha) : Measure.IsProbability (probabilityRepair kernel fallback input) := by
  classical
  by_cases normalized : kernel input Set.univ = ENNReal.one
  · rw [probabilityRepair_eq kernel fallback input ⟨normalized⟩]
    exact ⟨normalized⟩
  · unfold probabilityRepair
    rw [piecewise_apply_of_not_mem (fun point => kernel point Set.univ = ENNReal.one)
      _ _ _ input normalized, Kernel.const_apply]
    exact Measure.IsProbability.dirac target fallback

/-- A probability-repaired kernel is uniformly finite with bound one. -/
public theorem probabilityRepair_isFinite (kernel : Kernel source target) (fallback : beta) :
    IsFinite (probabilityRepair kernel fallback) := by
  refine ⟨⟨ENNReal.one, True.intro, ?_⟩⟩
  intro input
  rw [(probabilityRepair_isProbability kernel fallback input).univ_eq_one]
  exact ENNReal.leRefl _

/-- A probability-repaired kernel agrees almost everywhere with its input kernel
when the input fibers are probability measures almost everywhere. -/
public theorem probabilityRepair_ae_eq (kernel : Kernel source target) (fallback : beta)
    {measure : Measure source}
    (normalized : measure.AE (fun input => Measure.IsProbability (kernel input))) :
    measure.AEEq (fun input => probabilityRepair kernel fallback input) (fun input => kernel input) :=
  normalized.mono (fun input probability => probabilityRepair_eq kernel fallback input probability)

end Foundations.Measure.Kernel
