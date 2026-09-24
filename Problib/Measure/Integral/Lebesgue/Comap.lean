module

public import Problib.Measure.Integral.Lebesgue.Transport
public import Problib.Measure.Additive.Comap
import Problib.Measure.Integral.Lebesgue.Algebra

set_option autoImplicit false

/-!
# Lebesgue integration over measurable embeddings

Expresses lower integrals against pulled-back measures as integrals restricted
to the embedding range, and whole-space integrals when the integrand vanishes
outside that range.
-/
namespace Problib.Measure

open Problib.Real

public section

universe u v

variable {α : Type u} {β : Type v} {source : Space α} {target : Space β}

/-- Pull back a lower Lebesgue integral along a measurable embedding to an
integral restricted to the embedding range. -/
theorem lintegral_comap (measure : Measure target)
    (embedding : MeasurableEmbedding source target) {function : β → ENNReal}
    (measurable : ENNRealMeasurable target function) :
    lintegral (measure.comap embedding) (fun input => function (embedding.function input)) =
      lintegral (measure.restrict (Set.range embedding.function)) function := by
  rw [← lintegral_map (measure.comap embedding) embedding.function embedding.measurable
    measurable, Measure.map_comap]

/-- Evaluate a pulled-back lower Lebesgue integral as the full ambient integral
when the integrand vanishes outside the embedding range. -/
theorem lintegral_comap_of_zero_outside (measure : Measure target)
    (embedding : MeasurableEmbedding source target) {function : β → ENNReal}
    (measurable : ENNRealMeasurable target function)
    (zeroOutside : ∀ input, ¬Set.range embedding.function input → function input = ENNReal.zero) :
    lintegral (measure.comap embedding) (fun input => function (embedding.function input)) =
      lintegral measure function := by
  classical
  rw [lintegral_comap measure embedding measurable,
    ← lintegral_indicator measure _ embedding.range_measurable]
  apply lintegral_congr
  intro input
  change (if Set.range embedding.function input then function input else ENNReal.zero) =
    function input
  by_cases member : Set.range embedding.function input
  · exact if_pos member
  · rw [if_neg member, zeroOutside input member]

end

end Problib.Measure
