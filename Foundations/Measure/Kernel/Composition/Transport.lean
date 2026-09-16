module

public import Foundations.Measure.Kernel.Composition
public import Foundations.Measure.Kernel.Composition.Bind.Transport

set_option autoImplicit false

/-!
# Transport laws for transition kernel composition

Establishes how kernel composition interacts with source precomposition,
pushforward, and embedding pullback on intermediate and target spaces.
-/
namespace Foundations.Measure

public section

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
  {parameter : Space α} {source : Space β} {middle : Space γ} {target : Space δ}

namespace Kernel

/-- Source precomposition on the first kernel commutes with kernel
composition. -/
theorem precomp_comp_kernel (first : Kernel source middle) (second : Kernel middle target)
    (function : α → β) (measurable : MeasurableMap parameter source function) :
    (first.precomp function measurable).comp second =
      (first.comp second).precomp function measurable := by
  apply Kernel.ext
  intro input
  rfl

/-- Pushforward on the first kernel exchanges with source precomposition on the
second kernel. -/
theorem map_comp (first : Kernel parameter source) (function : β → γ)
    (measurable : MeasurableMap source middle function) (second : Kernel middle target) :
    (first.map function measurable).comp second =
      first.comp (second.precomp function measurable) := by
  apply Kernel.ext
  intro input
  exact Measure.bind_map (first input) function measurable second

/-- Pushforward on the second kernel commutes with kernel composition on the
target. -/
theorem comp_map (first : Kernel parameter source) (second : Kernel source middle)
    (function : γ → δ) (measurable : MeasurableMap middle target function) :
    (first.comp second).map function measurable =
      first.comp (second.map function measurable) := by
  apply Kernel.ext
  intro input
  exact Measure.map_bind (first input) second function measurable

/-- Pullback along a measurable embedding on the target commutes with kernel
composition. -/
theorem comp_comap (first : Kernel parameter middle) (second : Kernel middle target)
    (embedding : MeasurableEmbedding source target) :
    (first.comp second).comap embedding = first.comp (second.comap embedding) := by
  apply Kernel.ext
  intro input
  exact Measure.comap_bind (first input) second embedding

/-- Intermediate pullback composition equals full composition when the second
kernel vanishes outside the embedding range. -/
theorem comap_comp_of_zero_outside (first : Kernel parameter middle)
    (embedding : MeasurableEmbedding source middle) (second : Kernel middle target)
    (zeroOutside : ∀ input, ¬Set.range embedding.function input →
      second input = Measure.zero target) :
    (first.comap embedding).comp (second.precomp embedding.function embedding.measurable) =
      first.comp second := by
  apply Kernel.ext
  intro input
  exact Measure.bind_comap_of_zero_outside (first input) embedding second zeroOutside

/-- Intermediate pullback composition equals full composition when the first
kernel assigns zero mass to the complement of the embedding range. -/
theorem comap_comp_of_complement_null (first : Kernel parameter middle)
    (embedding : MeasurableEmbedding source middle) (second : Kernel middle target)
    (nullComplement : ∀ input,
      (first input).NullSet (Set.complement (Set.range embedding.function))) :
    (first.comap embedding).comp (second.precomp embedding.function embedding.measurable) =
      first.comp second := by
  apply Kernel.ext
  intro input
  exact Measure.bind_comap_of_complement_null (first input) embedding second (nullComplement input)

end Kernel

end

end Foundations.Measure
