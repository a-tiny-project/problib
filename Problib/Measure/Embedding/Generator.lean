module

public import Problib.Measure.Embedding.Basic
public import Problib.Measure.Space.Generator

set_option autoImplicit false

/-!
# Countable generators under measurable embeddings

Transports countable generators across measurable embeddings by preimage pullback.
-/

namespace Problib.Measure.MeasurableEmbedding

universe u v

variable {α : Type u} {β : Type v} {source : Space α} {target : Space β}

/-- Pullback of a target countable generator along a measurable embedding to obtain
a countable generator of the source space. -/
public def countableGenerator (embedding : MeasurableEmbedding source target)
    (generator : Space.CountableGenerator target) : Space.CountableGenerator source where
  sets := fun index => Set.preimage embedding.function (generator.sets index)
  generated := by
    have same : source = Space.comap embedding.function target := by
      apply Space.ext
      intro region
      constructor
      · intro measurable
        rw [← Set.preimage_image embedding.function embedding.injective region]
        exact Space.comap_map _ target (embedding.image_measurable region measurable)
      · exact Space.comap_minimal embedding.measurable
    exact same.trans (generator.comap embedding.function).generated

end Problib.Measure.MeasurableEmbedding
