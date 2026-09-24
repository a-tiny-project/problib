module

public import Problib.QuasiBorel.Measurable.Hom
public import Problib.Measure.Product

set_option autoImplicit false

namespace Problib.QuasiBorel

open Problib.Measure

universe u v w

public section

variable {Ω : Type u} {α : Type v} {β : Type w}

/-- Canonical quasi-Borel morphism from the product of generated quasi-Borel
spaces to the generated space of the binary measurable product. -/
@[expose] def Space.productToMeasurable (source : Problib.Measure.Space Ω)
    (left : Problib.Measure.Space α) (right : Problib.Measure.Space β) :
    Hom (Space.product (Space.ofMeasurable source left) (Space.ofMeasurable source right))
      (Space.ofMeasurable source (Problib.Measure.Space.product left right)) where
  toFun := fun pair => pair
  map_random := by
    intro random accepted
    exact Problib.Measure.Space.pair_measurable accepted.1 accepted.2

/-- Canonical quasi-Borel morphism from the generated space of a binary
measurable product to the product of generated quasi-Borel spaces. -/
@[expose] def Space.productOfMeasurable (source : Problib.Measure.Space Ω)
    (left : Problib.Measure.Space α) (right : Problib.Measure.Space β) :
    Hom (Space.ofMeasurable source (Problib.Measure.Space.product left right))
      (Space.product (Space.ofMeasurable source left) (Space.ofMeasurable source right)) where
  toFun := fun pair => pair
  map_random := by
    intro random accepted
    exact ⟨MeasurableMap.comp (Problib.Measure.Space.first_measurable left right) accepted,
      MeasurableMap.comp (Problib.Measure.Space.second_measurable left right) accepted⟩

theorem Space.productToMeasurable_productOfMeasurable (source : Problib.Measure.Space Ω)
    (left : Problib.Measure.Space α) (right : Problib.Measure.Space β) :
    Hom.comp (Space.productToMeasurable source left right) (Space.productOfMeasurable source left right) =
      Hom.identity (Space.ofMeasurable source (Problib.Measure.Space.product left right)) := by
  apply Hom.ext
  intro pair
  rfl

theorem Space.productOfMeasurable_productToMeasurable (source : Problib.Measure.Space Ω)
    (left : Problib.Measure.Space α) (right : Problib.Measure.Space β) :
    Hom.comp (Space.productOfMeasurable source left right) (Space.productToMeasurable source left right) =
      Hom.identity (Space.product (Space.ofMeasurable source left) (Space.ofMeasurable source right)) := by
  apply Hom.ext
  intro pair
  rfl

end

end Problib.QuasiBorel
