module

public import Problib.Measure.Kernel.Rejection.Basic
import Problib.Measure.Additive.Partition

set_option autoImplicit false

namespace Problib.Measure.Kernel
open Problib.Real
universe u v
variable {alpha : Type u} {beta : Type v}
  {source : Space alpha} {target : Space beta}

/-- Restricting a probability proposal to a measurable acceptance set accounts for both outcomes. -/
public theorem restriction_retry_conservative (proposal : Measure target)
    (probability : Measure.IsProbability proposal) (region : Set beta)
    (measurable : target.Measurable region) (input : alpha) :
    ENNReal.add (proposal (Set.complement region))
      (Kernel.const source (proposal.restrict region) input Set.univ) = ENNReal.one := by
  rw [Kernel.const_apply, Measure.restrict_apply_univ, ENNReal.add_comm,
    proposal.add_complement measurable, probability.univ_eq_one]

/-- Rejecting outside a measurable set produces the normalized restriction of any probability proposal. -/
public theorem loop_restriction_retry_eq_normalize (proposal : Measure target)
    (probability : Measure.IsProbability proposal) (region : Set beta)
    (measurable : target.Measurable region)
    (positive : ENNReal.lt ENNReal.zero (proposal region)) (input : alpha) :
    loop (retry (fun _ : alpha => proposal (Set.complement region))
        (ENNRealMeasurable.constant source _))
      (Kernel.const source (proposal.restrict region)) input =
      Measure.normalize (proposal.restrict region)
        ⟨probability.to_finite.restrict region, by
          rw [Measure.restrict_apply_univ]
          exact ENNReal.zero_lt_iff_ne_zero.mp positive⟩ := by
  exact loop_retry_eq_normalize _ _ _
    (restriction_retry_conservative proposal probability region measurable) input
    (by rw [Kernel.const_apply, Measure.restrict_apply_univ]; exact positive)

public theorem loop_restriction_retry_isProbability (proposal : Measure target)
    (probability : Measure.IsProbability proposal) (region : Set beta)
    (measurable : target.Measurable region)
    (positive : ENNReal.lt ENNReal.zero (proposal region)) (input : alpha) :
    Measure.IsProbability
      (loop (retry (fun _ : alpha => proposal (Set.complement region))
          (ENNRealMeasurable.constant source _))
        (Kernel.const source (proposal.restrict region)) input) := by
  rw [loop_restriction_retry_eq_normalize proposal probability region measurable positive input]
  exact Measure.normalize_isProbability _ _

end Problib.Measure.Kernel
