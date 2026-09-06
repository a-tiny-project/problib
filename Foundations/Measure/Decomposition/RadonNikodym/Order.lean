module

public import Foundations.Measure.Decomposition.RadonNikodym.Basic
public import Foundations.Measure.Integral.Density.Algebra

/-!
# Order comparison for Radon-Nikodym derivatives

This module proves order comparison for Radon-Nikodym derivative certificates
under a sigma-finite reference measure.
Pointwise almost-everywhere density comparison is equivalent to whole-measure
domination on all measurable sets.
-/

set_option autoImplicit false

namespace Foundations.Measure.Measure.RadonNikodymDerivative

open Foundations.Real

universe u

variable {alpha : Type u} {space : Space alpha}
  {left right reference : Measure space}

/-- Compare two Radon-Nikodym derivatives under a sigma-finite reference.
Almost-everywhere density comparison is equivalent to whole-measure domination
on all measurable sets. -/
public theorem density_ae_le_iff
    (first : RadonNikodymDerivative left reference)
    (second : RadonNikodymDerivative right reference)
    (finite : SigmaFinite reference) :
    reference.AE (fun value => ENNReal.le (first.density value) (second.density value)) ↔
      ∀ set, space.Measurable set → ENNReal.le (left set) (right set) := by
  have comparison := withDensity_le_iff_ae_le finite first.densityMeasurable second.densityMeasurable
  rw [← first.reconstruct_eq, ← second.reconstruct_eq] at comparison
  exact comparison.symm

/-- Characterize derivatives bounded by one almost everywhere.
Under a sigma-finite reference, this bound is equivalent to domination of the
target measure on all measurable sets. -/
public theorem density_ae_le_one_iff
    (derivative : RadonNikodymDerivative left reference)
    (finite : SigmaFinite reference) :
    reference.AE (fun value => ENNReal.le (derivative.density value) ENNReal.one) ↔
      ∀ set, space.Measurable set → ENNReal.le (left set) (reference set) := by
  have comparison := withDensity_le_iff_ae_le finite derivative.densityMeasurable
    (ENNRealMeasurable.constant space ENNReal.one)
  rw [reference.withDensity_one, ← derivative.reconstruct_eq] at comparison
  exact comparison.symm

end Foundations.Measure.Measure.RadonNikodymDerivative
