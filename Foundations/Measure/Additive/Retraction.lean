module

public import Foundations.Measure.Additive.Map
public import Foundations.Measure.Embedding.Retraction

set_option autoImplicit false

namespace Foundations.Measure.Measure

universe u v

/-- Pushforward along a measurable embedding followed by its retraction to an explicit fallback
recovers the original measure on any space, without requiring finiteness or probability premises. -/
public theorem map_retract_map {alpha : Type u} {beta : Type v}
    {source : Space alpha} {target : Space beta}
    (measure : Measure source) (embedding : MeasurableEmbedding source target)
    (fallback : alpha) :
    (measure.map embedding.function embedding.measurable).map
      (embedding.retract fallback) (embedding.retract_measurable fallback) = measure := by
  rw [map_comp]
  have inverse : (fun value => embedding.retract fallback (embedding.function value)) =
      (fun value => value) := funext (embedding.retract_forward fallback)
  simpa only [inverse] using map_id measure

end Foundations.Measure.Measure
