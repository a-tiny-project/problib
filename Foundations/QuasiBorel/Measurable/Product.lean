module

public import Foundations.QuasiBorel.Measurable.Hom
public import Foundations.Measure.Product

set_option autoImplicit false

namespace Foundations.QuasiBorel

open Foundations.Measure

universe u v w

public section

variable {Ω : Type u} {α : Type v} {β : Type w}

/-- Canonical quasi-Borel morphism from the product of generated quasi-Borel
spaces to the generated space of the binary measurable product. -/
@[expose] def Space.productToMeasurable (source : Foundations.Measure.Space Ω)
    (left : Foundations.Measure.Space α) (right : Foundations.Measure.Space β) :
    Hom (Space.product (Space.ofMeasurable source left) (Space.ofMeasurable source right))
      (Space.ofMeasurable source (Foundations.Measure.Space.product left right)) where
  toFun := fun pair => pair
  mapRandom := by
    intro random accepted
    exact Foundations.Measure.Space.pair_measurable accepted.1 accepted.2

/-- Canonical quasi-Borel morphism from the generated space of a binary
measurable product to the product of generated quasi-Borel spaces. -/
@[expose] def Space.productOfMeasurable (source : Foundations.Measure.Space Ω)
    (left : Foundations.Measure.Space α) (right : Foundations.Measure.Space β) :
    Hom (Space.ofMeasurable source (Foundations.Measure.Space.product left right))
      (Space.product (Space.ofMeasurable source left) (Space.ofMeasurable source right)) where
  toFun := fun pair => pair
  mapRandom := by
    intro random accepted
    exact ⟨MeasurableMap.comp (Foundations.Measure.Space.first_measurable left right) accepted,
      MeasurableMap.comp (Foundations.Measure.Space.second_measurable left right) accepted⟩

theorem Space.productToMeasurable_productOfMeasurable (source : Foundations.Measure.Space Ω)
    (left : Foundations.Measure.Space α) (right : Foundations.Measure.Space β) :
    Hom.comp (Space.productToMeasurable source left right) (Space.productOfMeasurable source left right) =
      Hom.identity (Space.ofMeasurable source (Foundations.Measure.Space.product left right)) := by
  apply Hom.ext
  intro pair
  rfl

theorem Space.productOfMeasurable_productToMeasurable (source : Foundations.Measure.Space Ω)
    (left : Foundations.Measure.Space α) (right : Foundations.Measure.Space β) :
    Hom.comp (Space.productOfMeasurable source left right) (Space.productToMeasurable source left right) =
      Hom.identity (Space.product (Space.ofMeasurable source left) (Space.ofMeasurable source right)) := by
  apply Hom.ext
  intro pair
  rfl

end

end Foundations.QuasiBorel
