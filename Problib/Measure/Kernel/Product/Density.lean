module
public import Problib.Measure.Kernel.Product
public import Problib.Measure.Integral.Density.Change
public import Problib.Measure.Integral.Lebesgue.Algebra

set_option autoImplicit false

/-!
# Semiproducts of densities

A measure with a density, extended by a kernel whose laws have densities
against one auxiliary reference, has the product density against the product
reference (`Measure.semiproduct_withDensity_prod`).
-/

namespace Problib.Measure
open Problib.Real
public section
universe u v

namespace Measure

variable {α : Type u} {β : Type v} {source : Space α} {target : Space β}

/-- A weighted measure extended by a kernel with densities against an
auxiliary reference has density `kernelDensity (x, u) · weight x` against the
product of the measure and the auxiliary reference. Unlike
`Measure.semiproduct_withDensity`, which reweights a kernel against itself and
lands on the semiproduct, the kernel's densities here are against one fixed
auxiliary and the result lands on the product measure. -/
public theorem semiproduct_withDensity_prod (measure : Measure source)
    {weight : α → ENNReal} (weightMeasurable : ENNRealMeasurable source weight)
    (auxiliary : Measure target) (auxiliaryFinite : Measure.SFinite auxiliary)
    (kernel : Kernel source target) (kernelFinite : Kernel.IsSFinite kernel)
    {kernelDensity : α × β → ENNReal}
    (kernelDensityMeasurable : ENNRealMeasurable (Space.product source target) kernelDensity)
    (represents : ∀ input, kernel input =
      auxiliary.withDensity (fun value => kernelDensity (input, value))) :
    (measure.withDensity weight).semiproduct kernel kernelFinite =
      (Measure.prod measure auxiliary auxiliaryFinite).withDensity
        (fun pair => ENNReal.mul (kernelDensity pair) (weight pair.1)) := by
  have joint : measure.semiproduct kernel kernelFinite =
      (Measure.prod measure auxiliary auxiliaryFinite).withDensity kernelDensity := by
    apply Measure.ext
    intro set setMeasurable
    let indicator : α × β → ENNReal := ennrealIndicator set fun _ => ENNReal.one
    have indicatorMeasurable :
        ENNRealMeasurable (Space.product source target) indicator :=
      ENNRealMeasurable.indicator setMeasurable (ENNRealMeasurable.constant _ _)
    rw [apply_eq_lintegral_indicator _ setMeasurable,
      apply_eq_lintegral_indicator _ setMeasurable,
      lintegral_semiproduct _ _ _ indicatorMeasurable,
      lintegral_withDensity _ kernelDensityMeasurable indicatorMeasurable,
      lintegral_prod _ _ _
        (ENNRealMeasurable.mul kernelDensityMeasurable indicatorMeasurable)]
    apply lintegral_congr
    intro input
    rw [represents input,
      lintegral_withDensity _
        (kernelDensityMeasurable.comp (Kernel.pair_left_measurable input))
        (indicatorMeasurable.comp (Kernel.pair_left_measurable input))]
  rw [Measure.semiproduct_withDensity_left _ weightMeasurable, joint,
    Measure.withDensity_withDensity _ kernelDensityMeasurable
      (weightMeasurable.comp (Space.first_measurable _ _))]

end Measure

end
end Problib.Measure
