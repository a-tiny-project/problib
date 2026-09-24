module

public import Problib.Measure.Product

set_option autoImplicit false

/-!
# Measurable selection sets on product spaces

Proves that fiberwise selecting from a countable family of target measurable sets
using a measurable index map yields a product-measurable set.
-/

namespace Problib.Measure.Space

universe u v

/-- Measurability in the product space of a family of sets selected by a measurable
index map into a countable sequence of target measurable sets. -/
public theorem selected_set_measurable {α : Type u} {β : Type v}
    {source : Space α} {target : Space β} {selection : α → Nat}
    (selectionMeasurable : MeasurableMap source (Space.discrete Nat) selection)
    (sets : Nat → Set β) (measurable : ∀ index, target.Measurable (sets index)) :
    (Space.product source target).Measurable (fun pair => sets (selection pair.1) pair.2) := by
  let rectangles : Nat → Set (α × β) := fun index =>
    Set.product (Set.preimage selection (Set.singleton index)) (sets index)
  have equal : (fun pair : α × β => sets (selection pair.1) pair.2) = Set.iUnion rectangles := by
    apply Set.ext
    intro pair
    constructor
    · intro member
      exact ⟨selection pair.1, rfl, member⟩
    · rintro ⟨index, same, member⟩
      change selection pair.1 = index at same
      rw [same]
      exact member
  rw [equal]
  exact (Space.product source target).iUnion (fun index =>
    Space.product_set_measurable source target (selectionMeasurable True.intro) (measurable index))

end Problib.Measure.Space
