module

public import Foundations.Measure.Kernel.Basic
public import Foundations.Measure.Additive.Comap.Finite

set_option autoImplicit false

namespace Foundations.Measure

open Foundations.Real

universe u v w z

namespace Kernel

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type z}
  {parameter : Space α} {source : Space β} {middle : Space γ} {target : Space δ}

/-- Pullback of a measurable kernel along a target measurable embedding across
arbitrary spaces. -/
@[expose] public noncomputable def comap (kernel : Kernel parameter middle)
    (embedding : MeasurableEmbedding source middle) : Kernel parameter source where
  toFun input := (kernel input).comap embedding
  measurable := by
    intro region measurable
    have equal : (fun input => (kernel input).comap embedding region) =
        (fun input => kernel input (Set.image embedding.function region)) :=
      funext fun input => Measure.comap_apply (kernel input) embedding measurable
    rw [equal]
    exact kernel.measurable (embedding.imageMeasurable region measurable)

@[simp] public theorem comap_apply (kernel : Kernel parameter middle)
    (embedding : MeasurableEmbedding source middle) (input : α) :
    kernel.comap embedding input = (kernel input).comap embedding := rfl

@[simp] public theorem comap_apply_univ (kernel : Kernel parameter middle)
    (embedding : MeasurableEmbedding source middle) (input : α) :
    kernel.comap embedding input Set.univ = kernel input (Set.range embedding.function) :=
  Measure.comap_apply_univ (kernel input) embedding

@[simp] public theorem comap_id (kernel : Kernel parameter source) :
    kernel.comap (MeasurableEmbedding.identity source) = kernel := by
  apply Kernel.ext
  intro input
  exact Measure.comap_id (kernel input)

public theorem comap_comp (kernel : Kernel parameter target)
    (before : MeasurableEmbedding source middle)
    (after : MeasurableEmbedding middle target) :
    (kernel.comap after).comap before = kernel.comap (before.trans after) := by
  apply Kernel.ext
  intro input
  exact Measure.comap_comp (kernel input) before after

@[simp] public theorem comap_map (kernel : Kernel parameter source)
    (embedding : MeasurableEmbedding source middle) :
    (kernel.map embedding.function embedding.measurable).comap embedding = kernel := by
  apply Kernel.ext
  intro input
  exact Measure.comap_map (kernel input) embedding

public theorem map_comap_apply (kernel : Kernel parameter middle)
    (embedding : MeasurableEmbedding source middle) (input : α) :
    (kernel.comap embedding).map embedding.function embedding.measurable input =
      (kernel input).restrict (Set.range embedding.function) :=
  Measure.map_comap (kernel input) embedding

/-- Reconstruct a target kernel when the embedding range complement is
fiberwise outer null. -/
public theorem map_comap_of_complement_null (kernel : Kernel parameter middle)
    (embedding : MeasurableEmbedding source middle)
    (nullComplement : ∀ input,
      (kernel input).NullSet (Set.complement (Set.range embedding.function))) :
    (kernel.comap embedding).map embedding.function embedding.measurable = kernel := by
  apply Kernel.ext
  intro input
  exact Measure.map_comap_of_complement_null (kernel input) embedding (nullComplement input)

@[simp] public theorem comap_zero (embedding : MeasurableEmbedding source middle) :
    (zero parameter middle).comap embedding = zero parameter source := by
  apply Kernel.ext
  intro input
  exact Measure.comap_zero embedding

public theorem comap_add (left right : Kernel parameter middle)
    (embedding : MeasurableEmbedding source middle) :
    (add left right).comap embedding = add (left.comap embedding) (right.comap embedding) := by
  apply Kernel.ext
  intro input
  exact Measure.comap_add (left input) (right input) embedding

public theorem comap_sum (kernels : Nat → Kernel parameter middle)
    (embedding : MeasurableEmbedding source middle) :
    (sum kernels).comap embedding = sum (fun index => (kernels index).comap embedding) := by
  apply Kernel.ext
  intro input
  exact Measure.comap_sum (fun index => kernels index input) embedding

public theorem comap_const (measure : Measure middle)
    (embedding : MeasurableEmbedding source middle) :
    (const parameter measure).comap embedding = const parameter (measure.comap embedding) := by
  apply Kernel.ext
  intro input
  rfl

public theorem comap_equivalence (kernel : Kernel parameter middle)
    (equivalence : MeasurableEquivalence source middle) :
    kernel.comap equivalence.toEmbedding =
      kernel.map equivalence.inverse equivalence.inverse_measurable := by
  apply Kernel.ext
  intro input
  exact Measure.comap_equivalence (kernel input) equivalence

/-- Pulled kernel fibers are probability measures if and only if each target
fiber assigns unit mass to the range. -/
public theorem comap_probability_iff (kernel : Kernel parameter middle)
    (embedding : MeasurableEmbedding source middle) :
    (∀ input, Measure.IsProbability (kernel.comap embedding input)) ↔
      ∀ input, kernel input (Set.range embedding.function) = ENNReal.one := by
  constructor
  · intro probability input
    exact (Measure.comap_probability_iff (kernel input) embedding).mp (probability input)
  · intro mass input
    exact (Measure.comap_probability_iff (kernel input) embedding).mpr (mass input)

/-- Pullback along an embedding preserves uniform finite bounds on kernel
fibers. -/
public theorem IsFinite.comap {kernel : Kernel parameter middle} (finite : IsFinite kernel)
    (embedding : MeasurableEmbedding source middle) : IsFinite (kernel.comap embedding) := by
  rcases finite.exists_bound with ⟨bound, boundFinite, bounded⟩
  refine ⟨⟨bound, boundFinite, ?_⟩⟩
  intro input
  rw [comap_apply_univ]
  exact ENNReal.leTrans ((kernel input).mono (fun _ _ => True.intro)) (bounded input)

/-- Explicit s-finite kernel certificate pulled along a measurable
embedding. -/
public noncomputable def IsSFinite.comap {kernel : Kernel parameter middle}
    (finite : IsSFinite kernel) (embedding : MeasurableEmbedding source middle) :
    IsSFinite (kernel.comap embedding) where
  components := fun index => (finite.components index).comap embedding
  finite := fun index => (finite.finite index).comap embedding
  sum_eq := by
    rw [← comap_sum, finite.sum_eq]

end Kernel

end Foundations.Measure
