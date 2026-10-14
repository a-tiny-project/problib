module

public import Problib.Measure.Product
public import Problib.Measure.Space.Countable
import Problib.Measure.Measurability

set_option autoImplicit false

/-!
# Measurable maps on products with a countable discrete first factor

Supplies joint measurability and its equivalence for uncurried maps from a
product `Space.product (Space.discrete α) source` into an arbitrary target space,
given an injection from `α` into `Nat`, and the same for sets whose sections
are measurable.
-/

namespace Problib.Measure.MeasurableMap

universe u v w

/-- An uncurried function on a product whose first factor is a countable discrete
space is jointly measurable whenever every fiber map is measurable. -/
public theorem uncurry_of_countable_first {α : Type u} {β : Type v} {γ : Type w}
    {source : Space β} {target : Space γ} (code : α → Nat)
    (injective : Function.Injective code) {function : α → β → γ}
    (measurable : ∀ input, MeasurableMap source target (function input)) :
    MeasurableMap (Space.product (Space.discrete α) source) target
      (fun pair => function pair.1 pair.2) := by
  intro region regionMeasurable
  let rectangles := fun input => Set.product (fun value => value = input)
    (Set.preimage (function input) region)
  have rectangleMeasurable : ∀ input,
      (Space.product (Space.discrete α) source).Measurable (rectangles input) :=
    fun input => Space.product_set_measurable _ _ True.intro (measurable input regionMeasurable)
  have equal : Set.preimage (fun pair => function pair.1 pair.2) region =
      (fun pair => ∃ input, rectangles input pair) := by
    apply Set.ext
    intro pair
    constructor
    · intro member
      exact ⟨pair.1, rfl, member⟩
    · rintro ⟨input, same, member⟩
      change region (function input pair.2) at member
      change region (function pair.1 pair.2)
      rw [same]
      exact member
  rw [equal]
  exact (Space.product (Space.discrete α) source).i_union_of_nat_injection code injective
    rectangles rectangleMeasurable

/-- Joint measurability on a product with a countable discrete first factor
is equivalent to fiberwise measurability. -/
public theorem uncurry_measurable_iff_of_countable_first
    {α : Type u} {β : Type v} {γ : Type w} {source : Space β} {target : Space γ}
    (code : α → Nat) (injective : Function.Injective code) {function : α → β → γ} :
    MeasurableMap (Space.product (Space.discrete α) source) target
        (fun pair => function pair.1 pair.2) ↔
      ∀ input, MeasurableMap source target (function input) := by
  constructor
  · intro measurable input
    measurability
  · exact uncurry_of_countable_first code injective

/-- A set on a product with a countable discrete first factor is measurable
whenever every section is measurable. -/
public theorem set_uncurry_of_countable_first {α : Type u} {β : Type v}
    {source : Space β} (code : α → Nat) (injective : Function.Injective code)
    {sets : α → Set β} (measurable : ∀ input, source.Measurable (sets input)) :
    (Space.product (Space.discrete α) source).Measurable
      (fun pair => sets pair.1 pair.2) := by
  let rectangles := fun input => Set.product (fun value => value = input) (sets input)
  have rectangleMeasurable : ∀ input,
      (Space.product (Space.discrete α) source).Measurable (rectangles input) :=
    fun input => Space.product_set_measurable _ _ True.intro (measurable input)
  have equal : (fun pair : α × β => sets pair.1 pair.2) =
      (fun pair => ∃ input, rectangles input pair) := by
    apply Set.ext
    intro pair
    constructor
    · intro member
      exact ⟨pair.1, rfl, member⟩
    · rintro ⟨input, same, member⟩
      change sets input pair.2 at member
      change sets pair.1 pair.2
      rw [same]
      exact member
  rw [equal]
  exact (Space.product (Space.discrete α) source).i_union_of_nat_injection code injective
    rectangles rectangleMeasurable

end Problib.Measure.MeasurableMap
