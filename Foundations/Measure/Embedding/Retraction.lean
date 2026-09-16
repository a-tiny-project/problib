module

public import Foundations.Measure.Embedding.Basic

set_option autoImplicit false

namespace Foundations.Measure.MeasurableEmbedding

universe u v w

public section

/-- Classical measurable retraction of an embedded space from its ambient space,
mapping range points to their unique preimages and non-range points to an explicit fallback. -/
@[expose] noncomputable def retract {beta : Type v} {gamma : Type w}
    {target : Space beta} {ambient : Space gamma}
    (embedding : MeasurableEmbedding target ambient) (fallback : beta) (output : gamma) : beta := by
  classical
  exact if member : Set.range embedding.function output then Classical.choose member else fallback

/-- Retraction is a left inverse to the embedding map on all target points. -/
theorem retract_forward {beta : Type v} {gamma : Type w}
    {target : Space beta} {ambient : Space gamma}
    (embedding : MeasurableEmbedding target ambient) (fallback point : beta) :
    retract embedding fallback (embedding.function point) = point := by
  have member : Set.range embedding.function (embedding.function point) := ⟨point, rfl⟩
  rw [retract, dif_pos member]
  exact embedding.injective (Classical.choose_spec member)

/-- The retraction map is measurable from the ambient space to the target space. -/
theorem retract_measurable {beta : Type v} {gamma : Type w}
    {target : Space beta} {ambient : Space gamma}
    (embedding : MeasurableEmbedding target ambient) (fallback : beta) :
    MeasurableMap ambient target (retract embedding fallback) := by
  classical
  intro region measurable
  have preimage : Set.preimage (retract embedding fallback) region =
      if region fallback then Set.union (Set.image embedding.function region)
        (Set.complement (Set.range embedding.function)) else Set.image embedding.function region := by
    apply Set.ext
    intro output
    by_cases member : Set.range embedding.function output
    · rcases member with ⟨point, rfl⟩
      have represented : Set.range embedding.function (embedding.function point) := ⟨point, rfl⟩
      have imageIff : Set.image embedding.function region (embedding.function point) ↔ region point :=
        ⟨fun ⟨other, accepted, equal⟩ => embedding.injective equal ▸ accepted,
          fun accepted => ⟨point, accepted, rfl⟩⟩
      by_cases fallbackAccepted : region fallback <;>
        simp [Set.preimage, retract_forward, fallbackAccepted, Set.union, Set.complement, represented, imageIff]
    · have imageAbsent : ¬Set.image embedding.function region output :=
        fun ⟨point, _, equal⟩ => member ⟨point, equal⟩
      by_cases fallbackAccepted : region fallback <;>
        simp [Set.preimage, retract, member, fallbackAccepted, Set.union, Set.complement, imageAbsent]
  rw [preimage]
  split
  · exact ambient.union (embedding.imageMeasurable region measurable)
      (ambient.complement embedding.range_measurable)
  · exact embedding.imageMeasurable region measurable

end

end Foundations.Measure.MeasurableEmbedding
