module

public import Foundations.QuasiBorel.Measurable.Embedding
public import Foundations.Measure.StandardBorel.Basic

set_option autoImplicit false

namespace Foundations.QuasiBorel

open Foundations.Measure

universe u v w x

public section

variable {Ω : Type u} {α : Type v} {β : Type w}

/-- Recovery of standard-Borel measurable space structure from the Borel unit
interval random source. -/
theorem Space.toMeasurable_ofStandardBorel {target : Foundations.Measure.Space α}
    (presentation : StandardBorel target) :
    Space.toMeasurable (Space.ofMeasurable Real.unitBorel target) = target :=
  Space.toMeasurable_ofEmbedding presentation.embedding

/-- Morphisms from standard-Borel domains to arbitrary measurable spaces over
the Borel unit interval are measurable. -/
theorem Hom.measurable_ofStandardBorel {domain : Foundations.Measure.Space α}
    {codomain : Foundations.Measure.Space β} (presentation : StandardBorel domain)
    (morphism : Hom (Space.ofMeasurable Real.unitBorel domain)
      (Space.ofMeasurable Real.unitBorel codomain)) :
    MeasurableMap domain codomain morphism :=
  Hom.measurable_ofEmbedding presentation.embedding morphism

/-- Fullness of `Hom.ofMeasurable` for standard-Borel domains over the Borel
unit interval. -/
theorem Hom.ofMeasurable_full_ofStandardBorel {domain : Foundations.Measure.Space α}
    {codomain : Foundations.Measure.Space β} (presentation : StandardBorel domain)
    (morphism : Hom (Space.ofMeasurable Real.unitBorel domain)
      (Space.ofMeasurable Real.unitBorel codomain)) :
    ∃ (function : α → β) (measurable : MeasurableMap domain codomain function),
      Hom.ofMeasurable measurable = morphism :=
  Hom.ofMeasurable_full_ofEmbedding presentation.embedding morphism

/-- Recovery of standard-Borel measurable space structure from the real Borel
random source. -/
theorem Space.toMeasurable_ofStandardBorelReal {target : Foundations.Measure.Space α}
    (presentation : StandardBorel target) :
    Space.toMeasurable (Space.ofMeasurable Real.borel target) = target :=
  Space.toMeasurable_ofEmbedding presentation.embeddingReal

/-- Morphisms from standard-Borel domains to arbitrary measurable spaces over
the real Borel random source are measurable. -/
theorem Hom.measurable_ofStandardBorelReal {domain : Foundations.Measure.Space α}
    {codomain : Foundations.Measure.Space β} (presentation : StandardBorel domain)
    (morphism : Hom (Space.ofMeasurable Real.borel domain) (Space.ofMeasurable Real.borel codomain)) :
    MeasurableMap domain codomain morphism :=
  Hom.measurable_ofEmbedding presentation.embeddingReal morphism

/-- Fullness of `Hom.ofMeasurable` for standard-Borel domains over the real
Borel random source. -/
theorem Hom.ofMeasurable_full_ofStandardBorelReal {domain : Foundations.Measure.Space α}
    {codomain : Foundations.Measure.Space β} (presentation : StandardBorel domain)
    (morphism : Hom (Space.ofMeasurable Real.borel domain) (Space.ofMeasurable Real.borel codomain)) :
    ∃ (function : α → β) (measurable : MeasurableMap domain codomain function),
      Hom.ofMeasurable measurable = morphism :=
  Hom.ofMeasurable_full_ofEmbedding presentation.embeddingReal morphism

end

end Foundations.QuasiBorel
