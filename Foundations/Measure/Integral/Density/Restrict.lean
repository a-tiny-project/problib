module

public import Foundations.Measure.Integral.Density.Basic

set_option autoImplicit false

namespace Foundations.Measure.Measure

open Foundations.Real

universe u

variable {alpha : Type u} {space : Space alpha}

/-- Weighting a restricted measure by a density commutes with restricting the
weighted measure to that measurable region. -/
public theorem withDensity_restrict (measure : Measure space)
    (density : alpha → ENNReal) {region : Set alpha}
    (regionMeasurable : space.Measurable region) :
    (measure.restrict region).withDensity density =
      (measure.withDensity density).restrict region := by
  apply Measure.ext
  intro set setMeasurable
  rw [(measure.restrict region).withDensity_apply density setMeasurable,
    (measure.withDensity density).restrict_apply region setMeasurable,
    measure.withDensity_apply density (space.inter setMeasurable regionMeasurable),
    measure.restrict_restrict region setMeasurable]

end Foundations.Measure.Measure
