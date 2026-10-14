module
public import Problib.Measure.Space

set_option autoImplicit false
namespace Problib.Measure
public section
universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

namespace Space
/-- Final σ-algebra on a setoid quotient. -/
@[expose] def quotient (setoid : Setoid α) (space : Space α) : Space (Quotient setoid) where
  Measurable := fun region => space.Measurable (Set.preimage (Quotient.mk setoid) region)
  empty := space.empty
  complement := fun measurable => space.complement measurable
  iUnion := fun measurable => space.iUnion measurable
end Space

/-- A measurable surjection onto its final measurable space. -/
public structure QuotientMap (space : Space α) (result : Space β) (reduce : α → β) : Prop where
  measurable : MeasurableMap space result reduce
  surjective : Function.Surjective reduce
  final : ∀ region, space.Measurable (Set.preimage reduce region) → result.Measurable region

public theorem quotient_map_mk (setoid : Setoid α) (space : Space α) :
    QuotientMap space (Space.quotient setoid space) (Quotient.mk setoid) where
  measurable := fun measured => measured
  surjective := by
    intro quotient
    refine Quotient.inductionOn quotient ?_
    intro value
    exact ⟨value, rfl⟩
  final := fun _ measured => measured

namespace QuotientMap
public theorem lift_measurable {space : Space α} {result : Space β}
    {reduce : α → β} (quotient : QuotientMap space result reduce)
    {target : Space γ} {function : β → γ}
    (composite : MeasurableMap space target (fun input => function (reduce input))) :
    MeasurableMap result target function := by
  intro region measurable
  exact quotient.final _ (composite measurable)
end QuotientMap
end
end Problib.Measure
