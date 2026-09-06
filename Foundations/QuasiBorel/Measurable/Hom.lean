module

public import Foundations.QuasiBorel.Measurable.Basic

set_option autoImplicit false

namespace Foundations.QuasiBorel

open Foundations.Measure

universe u v w x

public section

variable {Ω : Type u} {α : Type v} {β : Type w}

/-- Canonical quasi-Borel morphism induced by a measurable map between
spaces over an arbitrary measurable random source. -/
@[expose] def Hom.ofMeasurable {source : Foundations.Measure.Space Ω}
    {domain : Foundations.Measure.Space α} {codomain : Foundations.Measure.Space β}
    {function : α → β} (measurable : MeasurableMap domain codomain function) :
    Hom (Space.ofMeasurable source domain) (Space.ofMeasurable source codomain) where
  toFun := function
  mapRandom := fun random => MeasurableMap.comp measurable random

theorem Hom.ofMeasurable_identity (source : Foundations.Measure.Space Ω)
    (target : Foundations.Measure.Space α) :
    Hom.ofMeasurable (source := source) (MeasurableMap.identity target) =
      Hom.identity (Space.ofMeasurable source target) := by
  apply Hom.ext
  intro point
  rfl

theorem Hom.ofMeasurable_comp {γ : Type x} {source : Foundations.Measure.Space Ω}
    {first : Foundations.Measure.Space α} {second : Foundations.Measure.Space β}
    {third : Foundations.Measure.Space γ} {before : α → β} {after : β → γ}
    (afterMeasurable : MeasurableMap second third after)
    (beforeMeasurable : MeasurableMap first second before) :
    Hom.ofMeasurable (source := source) (MeasurableMap.comp afterMeasurable beforeMeasurable) =
      Hom.comp (Hom.ofMeasurable afterMeasurable) (Hom.ofMeasurable beforeMeasurable) := by
  apply Hom.ext
  intro point
  rfl

/-- Faithful embedding of measurable maps into quasi-Borel morphisms. -/
theorem Hom.ofMeasurable_faithful {source : Foundations.Measure.Space Ω}
    {domain : Foundations.Measure.Space α} {codomain : Foundations.Measure.Space β}
    {left right : α → β} (leftMeasurable : MeasurableMap domain codomain left)
    (rightMeasurable : MeasurableMap domain codomain right) :
    Hom.ofMeasurable (source := source) leftMeasurable = Hom.ofMeasurable rightMeasurable ↔
      left = right := by
  constructor
  · intro equal
    exact congrArg Hom.toFun equal
  · intro equal
    apply Hom.ext
    intro point
    exact congrFun equal point

end

end Foundations.QuasiBorel
