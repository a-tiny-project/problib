module

public import Foundations.QuasiBorel.SFinite.Standard.Generator
public import Foundations.QuasiBorel.SFinite.Presentation

set_option autoImplicit false

/-!
# Measure transport between standard-Borel and partial presentations

This module proves measure transport equations relating partial real
generators and standard-Borel generators.
Pushforward along decoders and pullback along seed embeddings coincide with
pushforward along generators and pullback along summand embeddings.
The identities hold for arbitrary measures without s-finiteness premises.
-/

namespace Foundations.QuasiBorel.SFinite

public section

open Foundations.Measure hiding Space
open Foundations.Measure.Real (borel)

universe u v

variable {space : Space realSource}

/-- Proves that pushforward along decode of pullback along the seed embedding
equals pullback along summand injection of pushforward along the generator. -/
theorem Generator.map_comap_decode (generator : Generator space) (measure : Measure borel) :
    (measure.comap generator.seedEmbedding).map generator.decode generator.decode_measurable =
      (measure.map generator.random (Space.random_measurable generator.accepted)).comap
        (Space.inrEmbedding (Space.terminal realSource) space) := by
  apply Measure.ext
  intro region measurable
  let embedding := Space.inrEmbedding (Space.terminal realSource) space
  calc
    ((measure.comap generator.seedEmbedding).map generator.decode
        generator.decode_measurable) region =
        (measure.comap generator.seedEmbedding) (Set.preimage generator.decode region) :=
      Measure.map_apply _ _ generator.decode_measurable @measurable
    _ = measure (Set.image generator.seedEmbedding.function
        (Set.preimage generator.decode region)) :=
      Measure.comap_apply _ generator.seedEmbedding (generator.decode_measurable @measurable)
    _ = measure (Set.preimage generator.random (Set.image embedding.function region)) := by
      rw [generator.image_decode_preimage]
    _ = (measure.map generator.random (Space.random_measurable generator.accepted))
        (Set.image embedding.function region) :=
      (Measure.map_apply _ _ (Space.random_measurable generator.accepted)
        (embedding.imageMeasurable region @measurable)).symm
    _ = ((measure.map generator.random (Space.random_measurable generator.accepted)).comap
        embedding) region := (Measure.comap_apply _ embedding @measurable).symm

/-- Proves that standard-to-partial transport followed by summand pullback
recovers the pushforward measure along the standard generator. -/
theorem Standard.Generator.toPartial_map (generator : Standard.Generator.{u, v} space)
    (measure : Measure generator.source) :
    ((measure.map generator.standard.embeddingReal.function generator.standard.embeddingReal.measurable).map
      generator.toPartial.random (Space.random_measurable generator.toPartial.accepted)).comap
        (Space.inrEmbedding (Space.terminal realSource) space) =
      measure.map generator.random generator.measurable := by
  rw [Measure.map_comp]
  have equal : (fun point => generator.toPartial.random
      (generator.standard.embeddingReal.function point)) =
      (fun point => Sum.inr (generator.random point)) :=
    funext generator.toPartial_forward
  simp only [equal]
  let embedding := Space.inrEmbedding (Space.terminal realSource) space
  have composed := Measure.map_comp measure generator.random embedding.function
    generator.measurable embedding.measurable
  exact (congrArg (fun current => current.comap embedding) composed).symm.trans
    (Measure.comap_map _ embedding)

end

end Foundations.QuasiBorel.SFinite
