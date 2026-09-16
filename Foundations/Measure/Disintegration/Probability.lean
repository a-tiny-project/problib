module

public import Foundations.Measure.Disintegration.Version
public import Foundations.Measure.Disintegration.Density
import Foundations.Measure.Integral.Density.Uniqueness
import Foundations.Measure.Integral.Density.Algebra

set_option autoImplicit false

namespace Foundations.Measure.Measure.Disintegration

open Foundations.Real

universe u v

variable {alpha : Type u} {beta : Type v} {source : Space alpha} {parameter : Space beta}
  {joint : Measure (Space.product source parameter)}

/-- Any disintegration of a joint measure with a σ-finite second marginal has
probability fibers almost everywhere under that marginal.
The proof applies the conditional density identity at the universal event. -/
public theorem isProbability_ae (selection : Disintegration joint)
    (finite : SigmaFinite (secondMarginal joint)) :
    (secondMarginal joint).AE (fun input => IsProbability (selection.conditional input)) := by
  have massEquality := (selection.conditional_isDensity source.univ).eq_withDensity.symm
  rw [Set.preimage_univ, joint.restrict_univ] at massEquality
  have normalized := ae_eq_of_withDensity_eq finite
    (selection.conditional.measurable source.univ)
    (ENNRealMeasurable.constant parameter ENNReal.one)
    (massEquality.trans (Measure.withDensity_one (secondMarginal joint)).symm)
  exact normalized.mono (fun _ equal => ⟨equal⟩)


end Foundations.Measure.Measure.Disintegration
