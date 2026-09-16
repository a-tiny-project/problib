module

public import Foundations.Measure.Disintegration.Reconstruction
public import Foundations.Measure.Kernel.Probability
public import Foundations.Measure.Kernel.Product.AlmostEverywhere

set_option autoImplicit false

namespace Foundations.Measure.Measure.Disintegration

open Foundations.Real

universe u v

variable {alpha : Type u} {beta : Type v} {source : Space alpha} {parameter : Space beta}
  {joint : Measure (Space.product source parameter)}

/-- Construct an everywhere-probability disintegration from an existing
disintegration, an almost-everywhere probability certificate under its second
marginal, and an explicit fallback point in the conditioned space. -/
@[expose] public noncomputable def probabilityVersion (selection : Disintegration joint)
    (normalized : (secondMarginal joint).AE (fun input => IsProbability (selection.conditional input)))
    (fallback : alpha) : Disintegration joint where
  conditional := selection.conditional.probabilityRepair fallback
  conditionalSFinite := (selection.conditional.probabilityRepair_isFinite fallback).toSFinite
  reconstruction := by
    apply Eq.trans _ selection.reconstruction
    apply reverseSemiproduct_congr_ae
    exact selection.conditional.probabilityRepair_ae_eq fallback normalized

/-- Every fiber of a probability-version disintegration is a probability measure. -/
public theorem probabilityVersion_isProbability (selection : Disintegration joint)
    (normalized : (secondMarginal joint).AE (fun input => IsProbability (selection.conditional input)))
    (fallback : alpha) (input : beta) :
    IsProbability ((selection.probabilityVersion normalized fallback).conditional input) :=
  selection.conditional.probabilityRepair_isProbability fallback input

/-- The conditional kernel of a probability-version disintegration equals the
input conditional kernel almost everywhere under the second marginal. -/
public theorem probabilityVersion_ae_eq (selection : Disintegration joint)
    (normalized : (secondMarginal joint).AE (fun input => IsProbability (selection.conditional input)))
    (fallback : alpha) :
    (secondMarginal joint).AEEq
      (fun input => (selection.probabilityVersion normalized fallback).conditional input)
      (fun input => selection.conditional input) :=
  selection.conditional.probabilityRepair_ae_eq fallback normalized


end Foundations.Measure.Measure.Disintegration
