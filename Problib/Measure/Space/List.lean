module

public import Problib.Measure.Space.SumProduct

set_option autoImplicit false

namespace Problib.Measure
public section
universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

namespace ListSpace

/-- A coordinate is absent beyond the end of the finite list. -/
@[expose] def coordinate : Nat → List α → Sum Unit α
  | _, [] => .inl ()
  | 0, head :: _ => .inr head
  | n + 1, _ :: tail => coordinate n tail

/-- Length and optional-coordinate cylinders generate the finite-list space. -/
@[expose] def Generators (element : Space α) (region : Set (List α)) : Prop :=
  (∃ set : Set Nat, region = Set.preimage List.length set) ∨
    (∃ n set, (Space.sum (Space.discrete Unit) element).Measurable set ∧
      region = Set.preimage (coordinate n) set)

end ListSpace

namespace Space

/-- The measurable space of finite lists. Both length and each existing
coordinate are observable, with no padding value required in the element type. -/
@[expose] def list (element : Space α) : Space (List α) :=
  generated (ListSpace.Generators element)

end Space

namespace ListSpace

theorem length_measurable (element : Space α) :
    MeasurableMap (Space.list element) (Space.discrete Nat) List.length := by
  intro region _
  exact Space.Generated.basic (.inl ⟨region, rfl⟩)

theorem coordinate_measurable (element : Space α) (n : Nat) :
    MeasurableMap (Space.list element) (Space.sum (Space.discrete Unit) element) (coordinate n) := by
  intro region measurable
  exact Space.Generated.basic (.inr ⟨n, region, measurable, rfl⟩)

/-- Construct a list-valued measurable map by its length and coordinates. -/
theorem measurable {source : Space β} {element : Space α} {function : β → List α}
    (length : MeasurableMap source (Space.discrete Nat) (fun x => (function x).length))
    (coordinates : ∀ n, MeasurableMap source (Space.sum (Space.discrete Unit) element)
      (fun x => coordinate n (function x))) : MeasurableMap source (Space.list element) function := by
  apply MeasurableMap.into_generated
  intro region generator
  rcases generator with ⟨set, rfl⟩ | ⟨n, set, measured, rfl⟩
  · exact length trivial
  · exact coordinates n measured

theorem cons_measurable (element : Space α) :
    MeasurableMap (Space.product element (Space.list element)) (Space.list element)
      (fun input => input.1 :: input.2) := by
  apply measurable
  · exact MeasurableMap.comp (MeasurableMap.from_discrete (Space.discrete Nat) (fun n : Nat => n + 1))
      (MeasurableMap.comp (length_measurable element) (Space.second_measurable _ _))
  · intro n
    cases n with
    | zero => exact MeasurableMap.comp (MeasurableMap.inr _ _) (Space.first_measurable _ _)
    | succ n => exact MeasurableMap.comp (coordinate_measurable element n) (Space.second_measurable _ _)

theorem tail_measurable (element : Space α) :
    MeasurableMap (Space.list element) (Space.list element) List.tail := by
  apply measurable
  · have measured : MeasurableMap (Space.list element) (Space.discrete Nat)
        (fun values => values.length - 1) := MeasurableMap.comp
      (MeasurableMap.from_discrete (Space.discrete Nat) (fun n : Nat => n - 1))
      (length_measurable element)
    intro region hr
    simpa only [Set.preimage, List.length_tail] using measured hr
  · intro n
    have equal : (fun values : List α => coordinate n values.tail) = coordinate (n + 1) := by
      funext values
      cases values <;> simp [List.tail, coordinate]
    rw [equal]
    exact fun {set} => coordinate_measurable element (n + 1) (set := set)

@[expose] def view (values : List α) : Sum Unit (α × List α) :=
  match values with
  | [] => .inl ()
  | head :: tail => .inr (head, tail)

theorem view_measurable (element : Space α) :
    MeasurableMap (Space.list element)
      (Space.sum (Space.discrete Unit) (Space.product element (Space.list element))) view := by
  have equal : view (α := α) = (fun values =>
      Sum.map (fun _ : Unit × List α => ()) (fun value => value)
        (Sum.elim (fun value => Sum.inl (value, values.tail))
          (fun value => Sum.inr (value, values.tail)) (coordinate 0 values))) := by
    funext values
    cases values <;> rfl
  rw [equal]
  exact fun {set} => MeasurableMap.comp (third :=
      Space.sum (Space.discrete Unit) (Space.product element (Space.list element)))
    (MeasurableMap.sum_map
      (MeasurableMap.constant (Space.product (Space.discrete Unit) (Space.list element))
        (Space.discrete Unit) ())
      (MeasurableMap.identity (Space.product element (Space.list element))))
    (MeasurableMap.comp
      (Space.distribute_sum_measurable (Space.discrete Unit) element (Space.list element))
      (Space.pair_measurable (coordinate_measurable element 0) (tail_measurable element)))

/-- A finite approximation of a fold; fuel is supplied by the input's length. -/
@[expose] def foldN (initial : γ → β) (step : α × (β × γ) → β) :
    Nat → List α × γ → β
  | 0, input => initial input.2
  | _ + 1, ([], captured) => initial captured
  | n + 1, (head :: tail, captured) => step (head, foldN initial step n (tail, captured), captured)

theorem foldN_measurable {element : Space α} {result : Space β} {parameter : Space γ}
    {initial : γ → β} {step : α × (β × γ) → β}
    (initialMeasurable : MeasurableMap parameter result initial)
    (stepMeasurable : MeasurableMap (Space.product element (Space.product result parameter)) result step)
    (n : Nat) : MeasurableMap (Space.product (Space.list element) parameter) result
      (foldN initial step n) := by
  induction n with
  | zero => exact MeasurableMap.comp initialMeasurable (Space.second_measurable _ _)
  | succ n induction =>
      have equal : foldN initial step (n + 1) = (fun input =>
          Sum.elim (fun value => initial value.2)
            (fun value => step (value.1.1, foldN initial step n (value.1.2, value.2), value.2))
            (Sum.elim (fun value => Sum.inl (value, input.2))
              (fun value => Sum.inr (value, input.2)) (view input.1))) := by
        funext input
        rcases input with ⟨values, captured⟩
        cases values <;> rfl
      rw [equal]
      have tailAndParameter : MeasurableMap
          (Space.product (Space.product element (Space.list element)) parameter)
          (Space.product (Space.list element) parameter) (fun x => (x.1.2, x.2)) :=
        Space.pair_measurable
          (MeasurableMap.comp (Space.second_measurable _ _) (Space.first_measurable _ _))
          (Space.second_measurable _ _)
      have onCons : MeasurableMap
          (Space.product (Space.product element (Space.list element)) parameter) result
          (fun value => step (value.1.1, foldN initial step n (value.1.2, value.2), value.2)) :=
        MeasurableMap.comp stepMeasurable
        (Space.pair_measurable
          (MeasurableMap.comp (Space.first_measurable _ _) (Space.first_measurable _ _))
          (Space.pair_measurable (MeasurableMap.comp induction tailAndParameter)
            (Space.second_measurable _ _)))
      exact fun {set} => MeasurableMap.comp (third := result)
        (MeasurableMap.sum_elim
          (MeasurableMap.comp initialMeasurable (Space.second_measurable _ _)) onCons)
        (MeasurableMap.comp
          (Space.distribute_sum_measurable (Space.discrete Unit)
            (Space.product element (Space.list element)) parameter)
          (Space.product_map (view_measurable element) (MeasurableMap.identity parameter)))

theorem foldN_length (initial : γ → β) (step : α × (β × γ) → β)
    (values : List α) (captured : γ) :
    foldN initial step values.length (values, captured) =
      values.foldr (fun head rest => step (head, rest, captured)) (initial captured) := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      change step (head, foldN initial step tail.length (tail, captured), captured) = _
      rw [induction]
      rfl

/-- Structural folding is jointly measurable in the finite list and captured
parameters. The length selects a measurable finite approximation. -/
theorem fold_measurable {element : Space α} {result : Space β} {parameter : Space γ}
    {initial : γ → β} {step : α × (β × γ) → β}
    (initialMeasurable : MeasurableMap parameter result initial)
    (stepMeasurable : MeasurableMap (Space.product element (Space.product result parameter)) result step) :
    MeasurableMap (Space.product (Space.list element) parameter) result
      (fun input => input.1.foldr (fun head rest => step (head, rest, input.2)) (initial input.2)) := by
  have measured : MeasurableMap (Space.product (Space.list element) parameter) result
      (fun input => foldN initial step input.1.length input) :=
    MeasurableMap.countable_piecewise
      (fun n => MeasurableMap.comp (length_measurable element)
        (Space.first_measurable (Space.list element) parameter)
        (set := fun length => length = n) trivial)
      (fun n => foldN_measurable initialMeasurable stepMeasurable n)
  have equal : (fun input : List α × γ => foldN initial step input.1.length input) =
      (fun input => input.1.foldr (fun head rest => step (head, rest, input.2)) (initial input.2)) := by
    funext input
    exact foldN_length initial step input.1 input.2
  rw [← equal]
  exact fun {set} => measured (set := set)

end ListSpace
end
end Problib.Measure
