module

public import Problib.Measure.Disintegration.Reconstruction
public import Problib.Measure.Kernel.Probability
public import Problib.Measure.Kernel.Product.AlmostEverywhere

set_option autoImplicit false

namespace Problib.Measure.Measure.Disintegration

open Problib.Real

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
    exact selection.conditional.probabilityRepair_aeEq fallback normalized

/-- Every fiber of a probability-version disintegration is a probability measure. -/
public theorem probabilityVersion_isProbability (selection : Disintegration joint)
    (normalized : (secondMarginal joint).AE (fun input => IsProbability (selection.conditional input)))
    (fallback : alpha) (input : beta) :
    IsProbability ((selection.probabilityVersion normalized fallback).conditional input) :=
  selection.conditional.probabilityRepair_isProbability fallback input

/-- The conditional kernel of a probability-version disintegration equals the
input conditional kernel almost everywhere under the second marginal. -/
public theorem probabilityVersion_aeEq (selection : Disintegration joint)
    (normalized : (secondMarginal joint).AE (fun input => IsProbability (selection.conditional input)))
    (fallback : alpha) :
    (secondMarginal joint).AEEq
      (fun input => (selection.probabilityVersion normalized fallback).conditional input)
      (fun input => selection.conditional input) :=
  selection.conditional.probabilityRepair_aeEq fallback normalized


end Problib.Measure.Measure.Disintegration
