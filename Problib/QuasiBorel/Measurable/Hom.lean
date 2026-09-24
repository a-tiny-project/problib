module

public import Problib.QuasiBorel.Measurable.Basic

set_option autoImplicit false

namespace Problib.QuasiBorel

open Problib.Measure

universe u v w x

public section

variable {Ω : Type u} {α : Type v} {β : Type w}

/-- Canonical quasi-Borel morphism induced by a measurable map between
spaces over an arbitrary measurable random source. -/
@[expose] def Hom.ofMeasurable {source : Problib.Measure.Space Ω}
    {domain : Problib.Measure.Space α} {codomain : Problib.Measure.Space β}
    {function : α → β} (measurable : MeasurableMap domain codomain function) :
    Hom (Space.ofMeasurable source domain) (Space.ofMeasurable source codomain) where
  toFun := function
  map_random := fun random => MeasurableMap.comp measurable random

theorem Hom.ofMeasurable_identity (source : Problib.Measure.Space Ω)
    (target : Problib.Measure.Space α) :
    Hom.ofMeasurable (source := source) (MeasurableMap.identity target) =
      Hom.identity (Space.ofMeasurable source target) := by
  apply Hom.ext
  intro point
  rfl

theorem Hom.ofMeasurable_comp {γ : Type x} {source : Problib.Measure.Space Ω}
    {first : Problib.Measure.Space α} {second : Problib.Measure.Space β}
    {third : Problib.Measure.Space γ} {before : α → β} {after : β → γ}
    (afterMeasurable : MeasurableMap second third after)
    (beforeMeasurable : MeasurableMap first second before) :
    Hom.ofMeasurable (source := source) (MeasurableMap.comp afterMeasurable beforeMeasurable) =
      Hom.comp (Hom.ofMeasurable afterMeasurable) (Hom.ofMeasurable beforeMeasurable) := by
  apply Hom.ext
  intro point
  rfl

/-- Faithful embedding of measurable maps into quasi-Borel morphisms. -/
theorem Hom.ofMeasurable_faithful {source : Problib.Measure.Space Ω}
    {domain : Problib.Measure.Space α} {codomain : Problib.Measure.Space β}
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

end Problib.QuasiBorel
