module

public import Problib.QuasiBorel.Measurable.Embedding
public import Problib.Measure.StandardBorel.Basic

set_option autoImplicit false

namespace Problib.QuasiBorel

open Problib.Measure

universe u v w x

public section

variable {Ω : Type u} {α : Type v} {β : Type w}

/-- Recovery of standard-Borel measurable space structure from the Borel unit
interval random source. -/
theorem Space.toMeasurable_of_standardBorel {target : Problib.Measure.Space α}
    (presentation : StandardBorel target) :
    Space.toMeasurable (Space.ofMeasurable Real.unitBorel target) = target :=
  Space.toMeasurable_of_embedding presentation.embedding

/-- Morphisms from standard-Borel domains to arbitrary measurable spaces over
the Borel unit interval are measurable. -/
theorem Hom.measurable_of_standardBorel {domain : Problib.Measure.Space α}
    {codomain : Problib.Measure.Space β} (presentation : StandardBorel domain)
    (morphism : Hom (Space.ofMeasurable Real.unitBorel domain)
      (Space.ofMeasurable Real.unitBorel codomain)) :
    MeasurableMap domain codomain morphism :=
  Hom.measurable_of_embedding presentation.embedding morphism

/-- Fullness of `Hom.ofMeasurable` for standard-Borel domains over the Borel
unit interval. -/
theorem Hom.ofMeasurable_full_of_standardBorel {domain : Problib.Measure.Space α}
    {codomain : Problib.Measure.Space β} (presentation : StandardBorel domain)
    (morphism : Hom (Space.ofMeasurable Real.unitBorel domain)
      (Space.ofMeasurable Real.unitBorel codomain)) :
    ∃ (function : α → β) (measurable : MeasurableMap domain codomain function),
      Hom.ofMeasurable measurable = morphism :=
  Hom.ofMeasurable_full_of_embedding presentation.embedding morphism

/-- Recovery of standard-Borel measurable space structure from the real Borel
random source. -/
theorem Space.toMeasurable_of_standardBorel_real {target : Problib.Measure.Space α}
    (presentation : StandardBorel target) :
    Space.toMeasurable (Space.ofMeasurable Real.borel target) = target :=
  Space.toMeasurable_of_embedding presentation.embeddingReal

/-- Morphisms from standard-Borel domains to arbitrary measurable spaces over
the real Borel random source are measurable. -/
theorem Hom.measurable_of_standardBorel_real {domain : Problib.Measure.Space α}
    {codomain : Problib.Measure.Space β} (presentation : StandardBorel domain)
    (morphism : Hom (Space.ofMeasurable Real.borel domain) (Space.ofMeasurable Real.borel codomain)) :
    MeasurableMap domain codomain morphism :=
  Hom.measurable_of_embedding presentation.embeddingReal morphism

/-- Fullness of `Hom.ofMeasurable` for standard-Borel domains over the real
Borel random source. -/
theorem Hom.ofMeasurable_full_of_standardBorel_real {domain : Problib.Measure.Space α}
    {codomain : Problib.Measure.Space β} (presentation : StandardBorel domain)
    (morphism : Hom (Space.ofMeasurable Real.borel domain) (Space.ofMeasurable Real.borel codomain)) :
    ∃ (function : α → β) (measurable : MeasurableMap domain codomain function),
      Hom.ofMeasurable measurable = morphism :=
  Hom.ofMeasurable_full_of_embedding presentation.embeddingReal morphism

end

end Problib.QuasiBorel
