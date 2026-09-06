module

public import Foundations.Measure.Additive.Comap
public import Foundations.Measure.Additive.SFinite

set_option autoImplicit false

namespace Foundations.Measure

open Foundations.Real

universe u v

namespace Measure

variable {α : Type u} {β : Type v} {source : Space α} {target : Space β}

/-- Pullback along a measurable embedding preserves finite measures. -/
public theorem IsFinite.comap {measure : Measure target} (finite : IsFinite measure)
    (embedding : MeasurableEmbedding source target) : IsFinite (measure.comap embedding) := by
  constructor
  rw [comap_apply_univ]
  exact finite.apply _

/-- Pullback along a measurable embedding preserves sigma-finite measures. -/
public def SigmaFinite.comap {measure : Measure target} (finite : SigmaFinite measure)
    (embedding : MeasurableEmbedding source target) : SigmaFinite (measure.comap embedding) where
  sets := fun index => Set.preimage embedding.function (finite.sets index)
  measurable := fun index => embedding.measurable (finite.measurable index)
  monotone := by
    intro first second ordered input member
    exact finite.monotone ordered member
  finite := by
    intro index
    rw [comap_apply measure embedding (embedding.measurable (finite.measurable index))]
    exact ENNReal.finiteOfLe
      (measure.mono (fun _ member => Set.image_preimage_subset embedding.function
        (finite.sets index) member)) (finite.finite index)
  cover := by
    rw [← Set.preimage_iUnion, finite.cover, Set.preimage_univ]

/-- Explicit s-finite measure certificate pulled along a measurable
embedding. -/
public noncomputable def SFinite.comap {measure : Measure target} (finite : SFinite measure)
    (embedding : MeasurableEmbedding source target) : SFinite (measure.comap embedding) where
  components := fun index => (finite.components index).comap embedding
  finite := fun index => (finite.finite index).comap embedding
  sum_eq := by
    rw [← comap_sum, finite.sum_eq]

/-- Characterize probability preservation by unit range mass without prior
ambient probability hypotheses. -/
public theorem comap_probability_iff (measure : Measure target)
    (embedding : MeasurableEmbedding source target) :
    IsProbability (measure.comap embedding) ↔
      measure (Set.range embedding.function) = ENNReal.one := by
  constructor
  · intro probability
    rw [← comap_apply_univ measure embedding]
    exact probability.univ_eq_one
  · intro mass
    constructor
    rw [comap_apply_univ, mass]

/-- Pullback along a measurable equivalence unconditionally preserves
probability measures. -/
public theorem IsProbability.comap {measure : Measure target}
    (probability : IsProbability measure)
    (equivalence : MeasurableEquivalence source target) :
    IsProbability (measure.comap equivalence.toEmbedding) := by
  apply (comap_probability_iff measure equivalence.toEmbedding).mpr
  rw [equivalence.toEmbedding_range, probability.univ_eq_one]

end Measure

end Foundations.Measure
