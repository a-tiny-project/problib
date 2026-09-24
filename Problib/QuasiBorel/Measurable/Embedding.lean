module

public import Problib.QuasiBorel.Measurable.Hom
public import Problib.QuasiBorel.Measurable.Induced
public import Problib.Measure.Embedding.Retraction

set_option autoImplicit false

namespace Problib.QuasiBorel

open Problib.Measure

universe u v w x

public section

variable {Ω : Type u} {α : Type v} {β : Type w}

/-- Measurable space recovery: when the domain measurably embeds into the
random source, the induced measurable space recovers the original structure. -/
theorem Space.toMeasurable_of_embedding {source : Problib.Measure.Space Ω}
    {target : Problib.Measure.Space α} (embedding : MeasurableEmbedding target source) :
    Space.toMeasurable (Space.ofMeasurable source target) = target := by
  classical
  apply Problib.Measure.Space.ext
  intro region
  constructor
  · intro measurable
    by_cases inhabited : Nonempty α
    · let fallback := Classical.choice inhabited
      have measured := embedding.measurable
        (measurable (MeasurableEmbedding.retract_measurable embedding fallback))
      have equal : Set.preimage embedding.function
          (Set.preimage (MeasurableEmbedding.retract embedding fallback) region) = region := by
        apply Set.ext
        intro point
        simp only [Set.preimage, MeasurableEmbedding.retract_forward]
      exact equal ▸ measured
    · have equal : region = Set.empty := by
        apply Set.ext
        intro point
        exact False.elim (inhabited ⟨point⟩)
      rw [equal]
      exact target.empty
  · intro measurable random randomMeasurable
    exact randomMeasurable measurable
/-- Every quasi-Borel morphism whose domain measurably embeds into the random
source induces a measurable map into the codomain's induced measurable space. -/
theorem Hom.toMeasurable_of_embedding {source : Problib.Measure.Space Ω}
    {domain : Problib.Measure.Space α} {codomain : Space (Source.ofMeasurable source)}
    (embedding : MeasurableEmbedding domain source)
    (morphism : Hom (Space.ofMeasurable source domain) codomain) :
    MeasurableMap domain codomain.toMeasurable morphism := by
  have measured : MeasurableMap (Space.ofMeasurable source domain).toMeasurable
      codomain.toMeasurable morphism := morphism.toMeasurable
  rw [Space.toMeasurable_of_embedding embedding] at measured
  exact @measured

/-- Every quasi-Borel morphism whose domain measurably embeds into the random
source has a measurable underlying function. -/
theorem Hom.measurable_of_embedding {source : Problib.Measure.Space Ω}
    {domain : Problib.Measure.Space α} {codomain : Problib.Measure.Space β}
    (embedding : MeasurableEmbedding domain source)
    (morphism : Hom (Space.ofMeasurable source domain) (Space.ofMeasurable source codomain)) :
    MeasurableMap domain codomain morphism := by
  intro region regionMeasurable
  have measured : (Space.toMeasurable (Space.ofMeasurable source domain)).Measurable
      (Set.preimage morphism region) := by
    intro random accepted
    exact morphism.map_random accepted regionMeasurable
  exact Eq.mp (congrArg (fun space => space.Measurable (Set.preimage morphism region))
    (Space.toMeasurable_of_embedding embedding)) @measured

/-- Fullness: every quasi-Borel morphism from a measurably embedded domain
arises from a measurable map. -/
theorem Hom.ofMeasurable_full_of_embedding {source : Problib.Measure.Space Ω}
    {domain : Problib.Measure.Space α} {codomain : Problib.Measure.Space β}
    (embedding : MeasurableEmbedding domain source)
    (morphism : Hom (Space.ofMeasurable source domain) (Space.ofMeasurable source codomain)) :
    ∃ (function : α → β) (measurable : MeasurableMap domain codomain function),
      Hom.ofMeasurable measurable = morphism := by
  refine ⟨morphism, Hom.measurable_of_embedding embedding morphism, ?_⟩
  apply Hom.ext
  intro point
  rfl

end

end Problib.QuasiBorel
