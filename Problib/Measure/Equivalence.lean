module

public import Problib.Measure.Space

set_option autoImplicit false

namespace Problib.Measure

universe u v w

/-- A measurable equivalence between explicit measurable spaces. -/
public structure MeasurableEquivalence {alpha : Type u} {beta : Type v}
    (source : Space alpha) (target : Space beta) where
  forward : alpha → beta
  inverse : beta → alpha
  inverse_forward : ∀ value, inverse (forward value) = value
  forward_inverse : ∀ value, forward (inverse value) = value
  forward_measurable : MeasurableMap source target forward
  inverse_measurable : MeasurableMap target source inverse

namespace MeasurableEquivalence

@[expose] public def identity {alpha : Type u} (space : Space alpha) :
    MeasurableEquivalence space space where
  forward := fun value => value
  inverse := fun value => value
  inverse_forward := fun _ => rfl
  forward_inverse := fun _ => rfl
  forward_measurable := MeasurableMap.identity space
  inverse_measurable := MeasurableMap.identity space

variable {α : Type u} {β : Type v} {γ : Type w}
  {source : Space α} {middle : Space β} {target : Space γ}

public theorem forward_injective (equivalence : MeasurableEquivalence source middle) :
    Function.Injective equivalence.forward := by
  intro left right equal
  calc
    left = equivalence.inverse (equivalence.forward left) := (equivalence.inverse_forward left).symm
    _ = equivalence.inverse (equivalence.forward right) := congrArg equivalence.inverse equal
    _ = right := equivalence.inverse_forward right

public theorem inverse_injective (equivalence : MeasurableEquivalence source middle) :
    Function.Injective equivalence.inverse := by
  intro left right equal
  calc
    left = equivalence.forward (equivalence.inverse left) := (equivalence.forward_inverse left).symm
    _ = equivalence.forward (equivalence.inverse right) := congrArg equivalence.forward equal
    _ = right := equivalence.forward_inverse right

@[expose] public def symm (equivalence : MeasurableEquivalence source middle) :
    MeasurableEquivalence middle source where
  forward := equivalence.inverse
  inverse := equivalence.forward
  inverse_forward := equivalence.forward_inverse
  forward_inverse := equivalence.inverse_forward
  forward_measurable := equivalence.inverse_measurable
  inverse_measurable := equivalence.forward_measurable

@[expose] public def trans (before : MeasurableEquivalence source middle)
    (after : MeasurableEquivalence middle target) : MeasurableEquivalence source target where
  forward input := after.forward (before.forward input)
  inverse input := before.inverse (after.inverse input)
  inverse_forward := by
    intro input
    rw [after.inverse_forward, before.inverse_forward]
  forward_inverse := by
    intro input
    rw [before.forward_inverse, after.forward_inverse]
  forward_measurable := MeasurableMap.comp after.forward_measurable before.forward_measurable
  inverse_measurable := MeasurableMap.comp before.inverse_measurable after.inverse_measurable

end MeasurableEquivalence

end Problib.Measure
