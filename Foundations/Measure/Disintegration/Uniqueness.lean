module

public import Foundations.Measure.Disintegration.Density
public import Foundations.Measure.Disintegration.Probability
public import Foundations.Measure.StandardBorel.Uniqueness

set_option autoImplicit false

namespace Foundations.Measure.Measure.Disintegration

universe u v

variable {alpha : Type u} {beta : Type v} {source : Space alpha} {parameter : Space beta}
  {joint : Measure (Space.product source parameter)}

/-- Two conditional kernels reconstructing the same joint measure agree almost
everywhere under the second marginal.
The conditioned space must be standard Borel and the second marginal must be
σ-finite.
The parameter space is arbitrary. -/
public theorem ae_eq (first second : Disintegration joint)
    (presentation : StandardBorel source) (finite : SigmaFinite (secondMarginal joint)) :
    (secondMarginal joint).AEEq
      (fun input => first.conditional input) (fun input => second.conditional input) :=
  presentation.ae_eq_of_apply_ae_eq first.conditional second.conditional
    ((first.isProbability_ae finite).mono (fun _ probability => probability.toFinite))
    ((second.isProbability_ae finite).mono (fun _ probability => probability.toFinite))
    (fun _ measurable => first.conditional_apply_ae_eq second finite measurable)

end Foundations.Measure.Measure.Disintegration
