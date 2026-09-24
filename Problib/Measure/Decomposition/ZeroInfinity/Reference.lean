module

public import Problib.Measure.Decomposition.ZeroInfinity.Basic
public import Problib.Measure.Additive.FiniteReference

set_option autoImplicit false

namespace Problib.Measure.Measure

open Problib.Real

universe u

variable {alpha : Type u} {space : Space alpha}

/-- A zero-infinity measure equals its finite reference measure scaled by infinity. -/
public theorem IsZeroInfinitySet.eq_smul_top {measure : Measure space}
    (pure : IsZeroInfinitySet measure Set.univ) (reference : FiniteReference measure) :
    measure = Measure.smul ENNReal.top reference.reference := by
  apply Measure.ext
  intro set measurable
  rw [Measure.smul_apply_measurable _ _ measurable]
  classical
  by_cases zero : reference.reference set = ENNReal.zero
  · rw [reference.target_continuous measurable zero, zero, ENNReal.mul_zero]
  · have positive : measure set ≠ ENNReal.zero :=
      fun null => zero (reference.reference_continuous measurable null)
    have infinity := (pure.subsets_zero_or_top measurable (Set.subset_univ _)).resolve_left positive
    rw [infinity, ENNReal.top_mul_of_ne_zero zero]

end Problib.Measure.Measure
