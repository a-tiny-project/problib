module

public import Foundations.Measure.Kernel.Composition.Bind
public import Foundations.Measure.Kernel.Comap
public import Foundations.Measure.Kernel.Precomp
public import Foundations.Measure.Integral.Lebesgue.Comap

set_option autoImplicit false

/-!
# Measure bind transport along maps and embeddings

Relates measure bind operations with pushforward and pullback maps.
Proves commutation of target pullback with bind, and characterizes source
pullback through range restriction, zero continuation, or null complements.
-/
namespace Foundations.Measure

public section

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
  {parameter : Space α} {source : Space β} {middle : Space γ} {target : Space δ}

namespace Measure

/-- Pushforward on the bound measure commutes with source precomposition on the
kernel. -/
theorem bind_map (measure : Measure parameter) (function : α → β)
    (measurable : MeasurableMap parameter source function) (kernel : Kernel source target) :
    (measure.map function measurable).bind kernel =
      measure.bind (kernel.precomp function measurable) := by
  apply Measure.ext
  intro region regionMeasurable
  rw [bind_apply _ _ regionMeasurable, bind_apply _ _ regionMeasurable]
  exact lintegral_map measure function measurable (kernel.measurable regionMeasurable)

/-- Pushforward of the resulting bound measure along a measurable map commutes
with pushforward on the kernel target. -/
theorem map_bind (measure : Measure parameter) (kernel : Kernel parameter source)
    (function : β → γ) (measurable : MeasurableMap source middle function) :
    (measure.bind kernel).map function measurable =
      measure.bind (kernel.map function measurable) := by
  apply Measure.ext
  intro region regionMeasurable
  rw [map_apply _ _ _ regionMeasurable, bind_apply _ _ (measurable regionMeasurable),
    bind_apply _ _ regionMeasurable]
  apply lintegral_congr
  intro input
  exact (map_apply (kernel input) function measurable regionMeasurable).symm

/-- Pullback of the resulting bound measure along a measurable embedding
commutes with pullback on the kernel target without support premises. -/
theorem comap_bind (measure : Measure parameter) (kernel : Kernel parameter middle)
    (embedding : MeasurableEmbedding source middle) :
    (measure.bind kernel).comap embedding = measure.bind (kernel.comap embedding) := by
  apply Measure.ext
  intro region measurable
  rw [comap_apply _ _ measurable,
    bind_apply _ _ (embedding.imageMeasurable region measurable), bind_apply _ _ measurable]
  apply lintegral_congr
  intro input
  exact (comap_apply (kernel input) embedding measurable).symm

/-- Source pullback of the bound measure equals ambient bind restricted to the
embedding range. -/
theorem bind_comap (measure : Measure middle) (embedding : MeasurableEmbedding source middle)
    (kernel : Kernel middle target) :
    (measure.comap embedding).bind (kernel.precomp embedding.function embedding.measurable) =
      (measure.restrict (Set.range embedding.function)).bind kernel := by
  apply Measure.ext
  intro region measurable
  rw [bind_apply _ _ measurable, bind_apply _ _ measurable]
  exact lintegral_comap measure embedding (kernel.measurable measurable)

/-- Source pullback equals ambient bind when the kernel vanishes everywhere
outside the embedding range. -/
theorem bind_comap_of_zero_outside (measure : Measure middle)
    (embedding : MeasurableEmbedding source middle) (kernel : Kernel middle target)
    (zeroOutside : ∀ input, ¬Set.range embedding.function input → kernel input = zero target) :
    (measure.comap embedding).bind (kernel.precomp embedding.function embedding.measurable) =
      measure.bind kernel := by
  apply Measure.ext
  intro region measurable
  rw [bind_apply _ _ measurable, bind_apply _ _ measurable]
  apply lintegral_comap_of_zero_outside measure embedding (kernel.measurable measurable)
  intro input outside
  rw [zeroOutside input outside, zero_apply]

/-- Source pullback equals ambient bind when the complement of the embedding
range has measure zero. -/
theorem bind_comap_of_complement_null (measure : Measure middle)
    (embedding : MeasurableEmbedding source middle) (kernel : Kernel middle target)
    (nullComplement : measure.NullSet (Set.complement (Set.range embedding.function))) :
    (measure.comap embedding).bind (kernel.precomp embedding.function embedding.measurable) =
      measure.bind kernel := by
  rw [bind_comap, measure.restrict_eq_self_of_complement_null nullComplement]

end Measure

end

end Foundations.Measure
