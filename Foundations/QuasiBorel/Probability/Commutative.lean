import Foundations.Measure.Giry.Commutative
import Foundations.QuasiBorel.Probability.Closed

set_option autoImplicit false

namespace Foundations.QuasiBorel.Probability

open Foundations.Measure hiding Space
open Foundations.Measure.Real (Carrier borel)

universe u v w

variable {left right target : Space (Source.ofMeasurable borel)}

private theorem bind_context_source (first : Law left) (second : Law right)
    (family : Hom (Space.product left right) (object target))
    {region : Set target.Carrier} (measurable : target.toMeasurable.Measurable region) :
    (bind first (bindContext (Hom.constant left (object right) second) family)).val.val region =
      lintegral first.presentation.sourceLaw.val (fun firstSeed =>
        lintegral second.presentation.sourceLaw.val (fun secondSeed =>
          (family (first.presentation.random firstSeed, second.presentation.random secondSeed)).val.val region)) := by
  rw [bind_source, Giry.bind_apply _ _ _ @measurable]
  apply lintegral_congr
  intro firstSeed
  change (bindContext (Hom.constant left (object right) second) family
    (first.presentation.random firstSeed)).val.val region = _
  rw [bindContext_apply]
  change (bind second (Space.curry family (first.presentation.random firstSeed))).val.val region = _
  rw [bind_source, Giry.bind_apply _ _ _ @measurable]
  rfl

/-- Commutativity of independent monadic binds for quasi-Borel probability laws, reducing through paired presentations to Tonelli integration on the real Borel random sources. -/
theorem bind_comm (first : Law left) (second : Law right)
    (family : Hom (Space.product left right) (object target)) :
    bind first (bindContext (Hom.constant left (object right) second) family) =
      bind second (bindContext (Hom.constant right (object left) first)
        (Hom.comp family (Space.swap right left))) := by
  apply Law.ext
  apply Giry.ext
  intro region measurable
  rw [bind_context_source first second family @measurable,
    bind_context_source second first (Hom.comp family (Space.swap right left)) @measurable]
  apply Giry.integral_swap first.presentation.sourceLaw second.presentation.sourceLaw
    (function := fun point =>
      (family (first.presentation.random point.1, second.presentation.random point.2)).val.val region)
  have joint : MeasurableMap (Foundations.Measure.Space.product borel borel)
      (Giry.space target.toMeasurable)
      (fun point => (family (first.presentation.random point.1, second.presentation.random point.2)).val) :=
    MeasurableMap.comp (kernel_measurable family)
      (Space.random_pair_measurable first.presentation.accepted second.presentation.accepted)
  exact ENNRealMeasurable.comp (Giry.evaluation @measurable) joint

end Foundations.QuasiBorel.Probability
