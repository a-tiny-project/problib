module

public import Problib.Measure.Distribution.Quantile
public import Problib.Measure.Real.Generator
public import Problib.Measure.Extended.Conversion
public import Problib.Measure.Extended.Order
public import Problib.Measure.Product

set_option autoImplicit false

namespace Problib.Measure.Real

open Problib.Real

universe u
variable {α : Type u} {source : Space α}

/-- Parameter-indexed quantiles are jointly measurable on `source × unitBorel`
when each fixed-point distribution-function slice is measurable. -/
public theorem DistributionFunction.quantile_jointly_measurable (family : α → DistributionFunction)
    (slices : ∀ point, MeasurableMap source unitBorel
      (fun input => (family input).function point)) :
    MeasurableMap (Space.product source unitBorel) unitBorel
      (fun pair => (family pair.1).quantile pair.2) := by
  have generated : MeasurableMap (Space.product source unitBorel)
      (Space.generated unitInitials) (fun pair => (family pair.1).quantile pair.2) := by
    apply MeasurableMap.into_generated
    rintro set ⟨point, rfl⟩
    have thresholdMeasurable := ofReal_measurable.comp
      (MeasurableMap.comp unitInclusion_measurable (Space.second_measurable source unitBorel))
    have valueMeasurable := (ofReal_measurable.comp
      (MeasurableMap.comp unitInclusion_measurable (slices point))).comp
      (Space.first_measurable source unitBorel)
    have comparison := ENNRealMeasurable.le_set thresholdMeasurable valueMeasurable
    have same : Set.preimage (fun pair => (family pair.1).quantile pair.2) (unitInitial point) =
        (fun pair : α × UnitInterval => ENNReal.le (ENNReal.ofReal pair.2.val)
          (ENNReal.ofReal ((family pair.1).function point).val)) := by
      apply Set.ext
      intro pair
      exact ((family pair.1).quantile_le_iff pair.2 point).trans
        (ENNReal.ofReal_le_ofReal_iff pair.2.property.1 ((family pair.1).function point).property.1).symm
    rw [same]
    exact comparison
  intro set measurable
  apply generated
  rw [← unitBorel_generated_initials]
  exact measurable

end Problib.Measure.Real
