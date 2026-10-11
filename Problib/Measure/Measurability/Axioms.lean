import Problib.Measure.Measurability.Real
import Problib.Measure.Space.List
import Trust.Command

/-! Regression goals for `measurability`, one per rule family the pilots use. -/

namespace Problib.Measure.Measurability.Examples

open Problib.Real Problib.Measure Problib.Measure.Real Problib.Real.Construction.Dedekind

variable {α β γ : Type} (first : Space α) (second : Space β) (third : Space γ)

/-- Projections and pairs, and an unapplied lemma whose implicit set the
tactic keeps. -/
example : MeasurableMap (Space.product (Space.list first) second) (Space.list first)
    (fun input => input.1.tail) := by
  measurability [ListSpace.tail_measurable first]

/-- A section at a fixed first coordinate. Its function eta-reduces to
`Prod.mk value`, which the pair rule still takes. -/
example (function : α × β → γ)
    (measurable : MeasurableMap (Space.product first second) third function) (value : α) :
    MeasurableMap second third (fun seed => function (value, seed)) := by
  measurability

/-- A binary map through `comp_pair`. -/
example (head : α → β) (tail : α → List β)
    (headMeasurable : MeasurableMap first second head)
    (tailMeasurable : MeasurableMap first (Space.list second) tail) :
    MeasurableMap first (Space.list second) (fun value => head value :: tail value) := by
  measurability [ListSpace.cons_measurable second]

/-- The middle space is fixed by the inner map, then the outer map is discrete. -/
example : MeasurableMap (Space.list first) (Space.discrete Nat)
    (fun values => values.length - 1) := by
  measurability [ListSpace.length_measurable first]

/-- A `Sum.elim` whose branches capture the input, through `distribute`. -/
example (selector : α → Sum Unit β) (selectorMeasurable :
      MeasurableMap first (Space.sum (Space.discrete Unit) second) selector) :
    MeasurableMap first
      (Space.sum (Space.product (Space.discrete Unit) first) (Space.product second first))
      (fun value => Sum.elim (fun empty => Sum.inl (empty, value))
        (fun inner => Sum.inr (inner, value)) (selector value)) := by
  measurability

/-- A real choice on an order comparison, through `ite` and `measurable_le`. -/
example (left right : α → selection.Carrier)
    (leftMeasurable : MeasurableMap first borel left)
    (rightMeasurable : MeasurableMap first borel right) :
    MeasurableMap first borel (fun value =>
      @ite _ (le (left value) (right value)) (Classical.propDecidable _)
        (add (left value) (right value)) (neg (right value))) := by
  measurability

/-- Extended-real products of a real map. -/
example (map : α → selection.Carrier) (mapMeasurable : MeasurableMap first borel map)
    (scale : ENNReal) :
    ENNRealMeasurable first (fun value => ENNReal.mul scale (ENNReal.ofReal (map value))) := by
  measurability

/-- A curried map with a fixed middle argument, through `comp_fixed_middle`.
The hint is stated on pairs, and the middle argument's type depends on it. -/
example {κ : Type} {fiber : κ → Type} (middle : κ) (right : Space (fiber middle))
    (map : β → (index : κ) → fiber index → γ) (inner : α → β) (outer : α → fiber middle)
    (mapMeasurable : MeasurableMap (Space.product second right) third
      (fun input => map input.1 middle input.2))
    (innerMeasurable : MeasurableMap first second inner)
    (outerMeasurable : MeasurableMap first right outer) :
    MeasurableMap first third (fun value => map (inner value) middle (outer value)) := by
  measurability

/-- A fixed coordinate of a map into a power, through `apply_coordinate`, as the
inner map of a composition. -/
example {κ : Type} (map : α → κ → β) (outer : β → γ) (index : κ)
    (mapMeasurable : MeasurableMap first (Space.pi fun _ : κ => second) map)
    (outerMeasurable : MeasurableMap second third outer) :
    MeasurableMap first third (fun value => outer (map value index)) := by
  measurability

/-! A failure names the function and its head, says whether a rule matched,
and names the hint to state. -/

/--
error: measurability could not prove this function measurable:
  fun values => values.length
Its head is `List.length`.
No rule matched it.
Next: state a hint for exactly this function. The hypothesis
  MeasurableMap first.list (Space.discrete Nat) fun values => (values ++ values).length
measures `List.length` in another shape, and the tactic matches shapes first-order.
-/
#guard_msgs in
example (lengthMeasurable : MeasurableMap (Space.list first) (Space.discrete Nat)
      (fun values => (values ++ values).length)) :
    MeasurableMap (Space.list first) (Space.discrete Nat) (fun values => values.length) := by
  measurability

/-! When the missing outer map is a constructor, no lemma is registered for it
and there is no definition to unfold, so the report points at that outer map. -/

/--
error: measurability could not prove this function measurable:
  fun x => ENNReal.finite (NNReal.ofReal (neg (sub x mean)))
Its head is `ENNReal.finite`.
The rule `ENNRealMeasurable.comp` matched, but no hint or registered map measures its outer map:
  ENNReal.finite
Next: add a hypothesis that measures exactly that outer map, or prove this step by hand.
-/
#guard_msgs in
example (mean : Carrier) :
    ENNRealMeasurable borel (fun x => ENNReal.finite (NNReal.ofReal (neg (sub x mean)))) := by
  measurability

end Problib.Measure.Measurability.Examples

#register_trust_claims allowing [propext, Quot.sound, Classical.choice] claims [
  Problib.Measure.MeasurableMap.comp_pair,
  Problib.Measure.MeasurableMap.comp_triple,
  Problib.Measure.MeasurableMap.comp_fixed_right,
  Problib.Measure.MeasurableMap.comp_fixed_middle,
  Problib.Measure.MeasurableMap.apply_coordinate,
  Problib.Measure.MeasurableMap.ite,
  Problib.Measure.MeasurableMap.distribute
]

#audit_registered_claims
