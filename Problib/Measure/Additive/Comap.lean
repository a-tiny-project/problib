module

public import Problib.Measure.Embedding
public import Problib.Measure.Additive.Sum

set_option autoImplicit false

namespace Problib.Measure

open Problib.Real

universe u v w

namespace Measure

variable {α : Type u} {β : Type v} {γ : Type w}
  {source : Space α} {middle : Space β} {target : Space γ}

/-- Pullback of a measure along a measurable embedding, evaluated on
measurable source sets. -/
@[expose] public def comap (measure : Measure middle)
    (embedding : MeasurableEmbedding source middle) : Measure source where
  content := fun region measurable =>
    measure.content (Set.image embedding.function region)
      (embedding.image_measurable region measurable)
  empty := by
    simpa only [Set.image_empty] using measure.empty
  content_iUnion_disjoint := by
    intro regions measurable disjoint
    simpa only [Set.image_iUnion] using measure.content_iUnion_disjoint
      (fun index => Set.image embedding.function (regions index))
      (fun index => embedding.image_measurable (regions index) (measurable index))
      (Set.image_pairwise embedding.function embedding.injective regions disjoint)

@[simp] public theorem comap_apply (measure : Measure middle)
    (embedding : MeasurableEmbedding source middle)
    {region : Set α} (measurable : source.Measurable region) :
    measure.comap embedding region = measure (Set.image embedding.function region) := by
  rw [(measure.comap embedding).apply_measurable measurable,
    measure.apply_measurable (embedding.image_measurable region measurable)]
  rfl

@[simp] public theorem comap_apply_univ (measure : Measure middle)
    (embedding : MeasurableEmbedding source middle) :
    measure.comap embedding Set.univ = measure (Set.range embedding.function) := by
  rw [comap_apply measure embedding source.univ, Set.image_univ]

@[simp] public theorem comap_id (measure : Measure source) :
    measure.comap (MeasurableEmbedding.identity source) = measure := by
  apply Measure.ext
  intro region measurable
  rw [comap_apply measure _ measurable]
  change measure (Set.image (fun input => input) region) = measure region
  rw [Set.image_id]

public theorem comap_comp (measure : Measure target)
    (before : MeasurableEmbedding source middle)
    (after : MeasurableEmbedding middle target) :
    (measure.comap after).comap before = measure.comap (before.trans after) := by
  apply Measure.ext
  intro region measurable
  rw [comap_apply _ before measurable,
    comap_apply measure after (before.image_measurable region measurable),
    comap_apply measure (before.trans after) measurable]
  change measure (Set.image after.function (Set.image before.function region)) =
    measure (Set.image (fun input => after.function (before.function input)) region)
  exact congrArg (fun set => measure set)
    (Set.image_comp before.function after.function region).symm

@[simp] public theorem comap_map (measure : Measure source)
    (embedding : MeasurableEmbedding source middle) :
    (measure.map embedding.function embedding.measurable).comap embedding = measure := by
  apply Measure.ext
  intro region measurable
  rw [comap_apply _ embedding measurable,
    map_apply measure embedding.function embedding.measurable
      (embedding.image_measurable region measurable),
    Set.preimage_image embedding.function embedding.injective]

public theorem map_comap (measure : Measure middle)
    (embedding : MeasurableEmbedding source middle) :
    (measure.comap embedding).map embedding.function embedding.measurable =
      measure.restrict (Set.range embedding.function) := by
  apply Measure.ext
  intro region measurable
  rw [map_apply _ embedding.function embedding.measurable measurable,
    comap_apply measure embedding (embedding.measurable measurable),
    Set.image_preimage, measure.restrict_apply _ measurable]

/-- Reconstruct the ambient measure when the range complement is outer null. -/
public theorem map_comap_of_complement_null (measure : Measure middle)
    (embedding : MeasurableEmbedding source middle)
    (nullComplement : measure.NullSet (Set.complement (Set.range embedding.function))) :
    (measure.comap embedding).map embedding.function embedding.measurable = measure :=
  (map_comap measure embedding).trans (measure.restrict_eq_self_of_complement_null nullComplement)

@[simp] public theorem comap_zero (embedding : MeasurableEmbedding source middle) :
    (zero middle).comap embedding = zero source := by
  apply Measure.ext
  intro region measurable
  rw [comap_apply _ embedding measurable, zero_apply, zero_apply]

public theorem comap_add (left right : Measure middle)
    (embedding : MeasurableEmbedding source middle) :
    (add left right).comap embedding = add (left.comap embedding) (right.comap embedding) := by
  apply Measure.ext
  intro region measurable
  rw [comap_apply _ embedding measurable,
    add_apply_measurable left right (embedding.image_measurable region measurable),
    add_apply_measurable _ _ measurable,
    comap_apply left embedding measurable, comap_apply right embedding measurable]

public theorem comap_smul (factor : ENNReal) (measure : Measure middle)
    (embedding : MeasurableEmbedding source middle) :
    (smul factor measure).comap embedding = smul factor (measure.comap embedding) := by
  apply Measure.ext
  intro region measurable
  rw [comap_apply _ embedding measurable,
    smul_apply_measurable factor measure (embedding.image_measurable region measurable),
    smul_apply_measurable factor _ measurable, comap_apply measure embedding measurable]

public theorem comap_sum (measures : Nat → Measure middle)
    (embedding : MeasurableEmbedding source middle) :
    (sum measures).comap embedding = sum (fun index => (measures index).comap embedding) := by
  apply Measure.ext
  intro region measurable
  rw [comap_apply _ embedding measurable,
    sum_apply measures (embedding.image_measurable region measurable), sum_apply _ measurable]
  apply ENNReal.tsum_congr
  intro index
  exact (comap_apply (measures index) embedding measurable).symm

/-- Commute measure pullback along an embedding with restriction to a
measurable target region. -/
public theorem comap_restrict (measure : Measure middle)
    (embedding : MeasurableEmbedding source middle)
    {region : Set β} (regionMeasurable : middle.Measurable region) :
    (measure.restrict region).comap embedding =
      (measure.comap embedding).restrict (Set.preimage embedding.function region) := by
  apply Measure.ext
  intro probe measurable
  rw [comap_apply _ embedding measurable,
    measure.restrict_apply region (embedding.image_measurable probe measurable),
    (measure.comap embedding).restrict_apply _ measurable,
    comap_apply measure embedding (source.inter measurable (embedding.measurable regionMeasurable)),
    Set.image_inter_preimage]

public theorem comap_le_comap {left right : Measure middle}
    (included : ∀ region, middle.Measurable region → ENNReal.le (left region) (right region))
    (embedding : MeasurableEmbedding source middle) (region : Set α) :
    ENNReal.le (left.comap embedding region) (right.comap embedding region) := by
  apply le_of_measurable_le _ region
  intro probe measurable
  rw [comap_apply left embedding measurable, comap_apply right embedding measurable]
  exact included _ (embedding.image_measurable probe measurable)

public theorem comap_equivalence (measure : Measure middle)
    (equivalence : MeasurableEquivalence source middle) :
    measure.comap equivalence.toEmbedding =
      measure.map equivalence.inverse equivalence.inverse_measurable := by
  apply Measure.ext
  intro region measurable
  rw [comap_apply measure _ measurable,
    map_apply measure equivalence.inverse equivalence.inverse_measurable measurable]
  exact congrArg (fun set => measure set) (equivalence.image_forward region)

@[simp] public theorem map_comap_equivalence (measure : Measure middle)
    (equivalence : MeasurableEquivalence source middle) :
    (measure.comap equivalence.toEmbedding).map
        equivalence.forward equivalence.forward_measurable = measure := by
  exact (map_comap measure equivalence.toEmbedding).trans (by
    rw [equivalence.toEmbedding_range, restrict_univ])

end Measure

end Problib.Measure
