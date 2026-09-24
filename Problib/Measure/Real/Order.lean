module

public import Problib.Measure.Real.Borel
public import Problib.Real.Basis

set_option autoImplicit false

namespace Problib.Measure.Real

open Problib.Real.Construction.Dedekind

universe u

variable {α : Type u} {source : Space α} {left right : α → Carrier}

/-- The strict comparison predicate between two real-measurable maps is measurable. -/
public theorem measurable_lt (leftMeasurable : MeasurableMap source borel left)
    (rightMeasurable : MeasurableMap source borel right) :
    source.Measurable (fun value => lt (left value) (right value)) := by
  let pieces : Nat → Set α := fun index =>
    Set.inter (Set.preimage left (Iio (rationalBasis index)))
      (Set.preimage right (Ioi (rationalBasis index)))
  have equal : (fun value => lt (left value) (right value)) = Set.iUnion pieces := by
    apply Set.ext
    intro value
    constructor
    · intro less
      rcases exists_rationalBasis_between less with ⟨index, lower, upper⟩
      exact ⟨index, lower, upper⟩
    · rintro ⟨index, lower, upper⟩
      exact lt_trans lower upper
  rw [equal]
  exact source.iUnion (fun index => source.inter
    (leftMeasurable (measurable_iio (rationalBasis index)))
    (rightMeasurable (measurable_ioi (rationalBasis index))))

/-- The weak comparison predicate between two real-measurable maps is measurable. -/
public theorem measurable_le (leftMeasurable : MeasurableMap source borel left)
    (rightMeasurable : MeasurableMap source borel right) :
    source.Measurable (fun value => le (left value) (right value)) := by
  have equal : (fun value => le (left value) (right value)) =
      Set.complement (fun value => lt (right value) (left value)) := by
    apply Set.ext
    intro value
    exact not_lt_iff_le.symm
  rw [equal]
  exact source.complement (measurable_lt rightMeasurable leftMeasurable)

/-- The equality predicate between two real-measurable maps is measurable. -/
public theorem measurable_eq (leftMeasurable : MeasurableMap source borel left)
    (rightMeasurable : MeasurableMap source borel right) :
    source.Measurable (fun value => left value = right value) := by
  have equal : (fun value => left value = right value) =
      Set.inter (fun value => le (left value) (right value))
        (fun value => le (right value) (left value)) := by
    apply Set.ext
    intro value
    change left value = right value ↔
      le (left value) (right value) ∧ le (right value) (left value)
    constructor
    · intro same
      rw [same]
      exact ⟨le_refl _, le_refl _⟩
    · rintro ⟨forward, backward⟩
      exact le_antisymm forward backward
  rw [equal]
  exact source.inter (measurable_le leftMeasurable rightMeasurable)
    (measurable_le rightMeasurable leftMeasurable)

end Problib.Measure.Real
