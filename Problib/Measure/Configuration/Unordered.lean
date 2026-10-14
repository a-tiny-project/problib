module
public import Problib.Measure.Space.Quotient
public import Problib.Measure.Space.List
public import Problib.Measure.Additive.Map

set_option autoImplicit false
namespace Problib.Measure
public section
universe u v
variable {α : Type u} {β : Type v}

public abbrev Unordered (α : Type u) : Type u := Quotient (List.isSetoid α)
namespace Space
@[expose] public def unordered (element : Space α) : Space (Unordered α) :=
  Space.quotient (List.isSetoid α) (Space.list element)
end Space

@[expose] public def unorder (values : List α) : Unordered α := Quotient.mk _ values
public theorem unorder_quotient_map (element : Space α) :
    QuotientMap (Space.list element) (Space.unordered element) unorder :=
  quotient_map_mk _ _

@[expose] public def forgetLabels (setoid : Setoid α) (ret : α → β)
    (invariant : ∀ left right, setoid.r left right → ret left = ret right) :
    Quotient setoid → β := Quotient.lift ret invariant

public theorem forgetLabels_measurable {space : Space α} {result : Space β}
    {setoid : Setoid α} {ret : α → β}
    {invariant : ∀ left right, setoid.r left right → ret left = ret right}
    (retMeasurable : MeasurableMap space result ret) :
    MeasurableMap (Space.quotient setoid space) result
      (forgetLabels setoid ret invariant) := by
  apply (quotient_map_mk setoid space).lift_measurable
  exact retMeasurable

/-- A label-invariant return factors through the quotient law. -/
public theorem configuration_map_sound {space : Space α} {result : Space β}
    {setoid : Setoid α} {ret : α → β}
    {invariant : ∀ left right, setoid.r left right → ret left = ret right}
    (retMeasurable : MeasurableMap space result ret) (law : Measure space) :
    law.map ret retMeasurable =
      (law.map (Quotient.mk setoid) (quotient_map_mk setoid space).measurable).map
        (forgetLabels setoid ret invariant)
        (forgetLabels_measurable retMeasurable) := by
  rw [Measure.map_comp]
  rfl
end
end Problib.Measure
