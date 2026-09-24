module

public import Problib.Measure.Distribution.Basic

set_option autoImplicit false

namespace Problib.Measure.Real.DistributionFunction

open Problib.Real
open Problib.Real.Construction

universe u
variable {ι : Type u}

public section

private theorem exists_bound_value (thresholds bounds : ι → UnitInterval)
    (point : UnitInterval) :
    ∃ value : UnitInterval,
      (∀ index, Dedekind.lt point.val (thresholds index).val →
        Dedekind.le value.val (bounds index).val) ∧
      ∀ lower : UnitInterval,
        (∀ index, Dedekind.lt point.val (thresholds index).val →
          Dedekind.le lower.val (bounds index).val) → Dedekind.le lower.val value.val := by
  let candidates : Set Carrier := fun value => value = Dedekind.one ∨
    ∃ index, Dedekind.lt point.val (thresholds index).val ∧ value = (bounds index).val
  have nonnegative : ∀ value, candidates value → Dedekind.le Dedekind.zero value := by
    intro value member
    rcases member with rfl | ⟨index, _, rfl⟩
    · exact Dedekind.one_nonnegative
    · exact (bounds index).property.1
  rcases Dedekind.selection.completeOrder.complete.exists_glb candidates
      ⟨Dedekind.one, Or.inl rfl⟩ ⟨Dedekind.zero, nonnegative⟩ with
    ⟨value, lower, greatest⟩
  refine ⟨⟨value, greatest _ nonnegative, lower _ (Or.inl rfl)⟩, ?_, ?_⟩
  · intro index active
    exact lower _ (Or.inr ⟨index, active, rfl⟩)
  · intro candidate bounded
    apply greatest candidate.val
    intro member present
    rcases present with rfl | ⟨index, active, rfl⟩
    · exact candidate.property.2
    · exact bounded index active

private noncomputable def boundValue (thresholds bounds : ι → UnitInterval)
    (point : UnitInterval) : UnitInterval :=
  Classical.choose (exists_bound_value thresholds bounds point)

private theorem boundValue_lower (thresholds bounds : ι → UnitInterval)
    (point : UnitInterval) (index : ι)
    (active : Dedekind.lt point.val (thresholds index).val) :
    Dedekind.le (boundValue thresholds bounds point).val (bounds index).val :=
  (Classical.choose_spec (exists_bound_value thresholds bounds point)).1 index active

private theorem boundValue_greatest (thresholds bounds : ι → UnitInterval)
    (point lower : UnitInterval)
    (bounded : ∀ index, Dedekind.lt point.val (thresholds index).val →
      Dedekind.le lower.val (bounds index).val) :
    Dedekind.le lower.val (boundValue thresholds bounds point).val :=
  (Classical.choose_spec (exists_bound_value thresholds bounds point)).2 lower bounded

private theorem boundValue_lt_iff (thresholds bounds : ι → UnitInterval)
    (point : UnitInterval) (upper : Carrier) :
    Dedekind.lt (boundValue thresholds bounds point).val upper ↔
      Dedekind.lt Dedekind.one upper ∨
      ∃ index, Dedekind.lt point.val (thresholds index).val ∧
        Dedekind.lt (bounds index).val upper := by
  classical
  constructor
  · intro below
    by_cases aboveOne : Dedekind.lt Dedekind.one upper
    · exact Or.inl aboveOne
    · apply Or.inr
      apply Classical.byContradiction
      intro missing
      have upperNonnegative := Dedekind.le_trans
        (boundValue thresholds bounds point).property.1 below.1
      apply below.2
      apply boundValue_greatest thresholds bounds point
        ⟨upper, upperNonnegative, not_lt_iff_le.mp aboveOne⟩
      intro index active
      exact not_lt_iff_le.mp (fun strictlyBelow => missing ⟨index, active, strictlyBelow⟩)
  · intro witness
    rcases witness with aboveOne | ⟨index, active, below⟩
    · exact Dedekind.lt_of_le_of_lt (boundValue thresholds bounds point).property.2 aboveOne
    · exact Dedekind.lt_of_le_of_lt (boundValue_lower thresholds bounds point index active) below

/-- Constructs the greatest distribution function bounded by supplied values.
Takes arbitrary index families of thresholds and upper bounds.
Evaluates as the infimum of one and active bounds where point is below
threshold.
Proves monotonicity, upper normalization, and right-continuity directly. -/
noncomputable def ofUpperBounds (thresholds bounds : ι → UnitInterval) :
    DistributionFunction where
  function := boundValue thresholds bounds
  monotone := by
    intro left right included
    apply boundValue_greatest
    intro index active
    exact boundValue_lower thresholds bounds left index (Dedekind.lt_of_le_of_lt included active)
  upper := by
    apply Subtype.ext
    apply Dedekind.le_antisymm (boundValue thresholds bounds unitOne).property.2
    apply boundValue_greatest thresholds bounds unitOne unitOne
    intro index active
    exact False.elim (active.2 (thresholds index).property.2)
  right_continuous := by
    intro point room upper above
    rcases (boundValue_lt_iff thresholds bounds point upper).mp above with
      aboveOne | ⟨index, active, below⟩
    · exact ⟨unitOne, room,
        Dedekind.lt_of_le_of_lt (boundValue thresholds bounds unitOne).property.2 aboveOne⟩
    · rcases exists_unit_right_below point (thresholds index).val room active with
        ⟨right, rightAbove, rightBelow⟩
      exact ⟨right, rightAbove, (boundValue_lt_iff thresholds bounds right upper).mpr
        (Or.inr ⟨index, rightBelow, below⟩)⟩

/-- Proves the constructed distribution respects every active upper bound.
When the evaluation point is strictly below a threshold, the output is
bounded by that threshold upper bound. -/
theorem ofUpperBounds_le (thresholds bounds : ι → UnitInterval)
    (point : UnitInterval) (index : ι)
    (active : Dedekind.lt point.val (thresholds index).val) :
    Dedekind.le ((ofUpperBounds thresholds bounds).function point).val (bounds index).val :=
  boundValue_lower thresholds bounds point index active

/-- Maximality of the constructed distribution function.
Any lower value respecting all active bounds is bounded above by this
construction. -/
theorem le_ofUpperBounds (thresholds bounds : ι → UnitInterval)
    (point lower : UnitInterval)
    (bounded : ∀ index, Dedekind.lt point.val (thresholds index).val →
      Dedekind.le lower.val (bounds index).val) :
    Dedekind.le lower.val ((ofUpperBounds thresholds bounds).function point).val :=
  boundValue_greatest thresholds bounds point lower bounded

/-- Exact strict output threshold characterization.
Output is strictly below `upper` iff `1 < upper` or some index has point
strictly below threshold and bound strictly below `upper`. -/
theorem ofUpperBounds_lt_iff (thresholds bounds : ι → UnitInterval)
    (point : UnitInterval) (upper : Carrier) :
    Dedekind.lt ((ofUpperBounds thresholds bounds).function point).val upper ↔
      Dedekind.lt Dedekind.one upper ∨
      ∃ index, Dedekind.lt point.val (thresholds index).val ∧
        Dedekind.lt (bounds index).val upper :=
  boundValue_lt_iff thresholds bounds point upper

/-- Pointwise monotonicity with respect to the input bound family.
Increasing the bounding family at each index preserves or increases the
constructed distribution function. -/
theorem ofUpperBounds_mono (thresholds left right : ι → UnitInterval)
    (included : ∀ index, Dedekind.le (left index).val (right index).val)
    (point : UnitInterval) :
    Dedekind.le ((ofUpperBounds thresholds left).function point).val
      ((ofUpperBounds thresholds right).function point).val := by
  apply le_ofUpperBounds
  intro index active
  exact Dedekind.le_trans (ofUpperBounds_le thresholds left point index active) (included index)

/-- Inactive bound evaluation.
When every threshold is at or below the evaluation point, no bound is
active and the distribution function evaluates to one. -/
theorem ofUpperBounds_of_inactive (thresholds bounds : ι → UnitInterval)
    (point : UnitInterval)
    (inactive : ∀ index, Dedekind.le (thresholds index).val point.val) :
    (ofUpperBounds thresholds bounds).function point = unitOne := by
  apply Subtype.ext
  apply Dedekind.le_antisymm ((ofUpperBounds thresholds bounds).function point).property.2
  apply le_ofUpperBounds thresholds bounds point unitOne
  intro index active
  exact False.elim (active.2 (inactive index))

/-- Coherent recovery of an existing distribution function.
Recovers the original distribution when bounding values come from that
distribution and thresholds are right-dense in the unit interval. -/
theorem ofUpperBounds_eq (distribution : DistributionFunction)
    (thresholds : ι → UnitInterval)
    (dense : ∀ point right : UnitInterval, Dedekind.lt point.val right.val →
      ∃ index, Dedekind.lt point.val (thresholds index).val ∧
        Dedekind.le (thresholds index).val right.val) :
    ofUpperBounds thresholds (fun index => distribution.function (thresholds index)) =
      distribution := by
  have same : (ofUpperBounds thresholds
      (fun index => distribution.function (thresholds index))).function =
        distribution.function := by
    funext point
    apply Subtype.ext
    apply Dedekind.le_antisymm
    · apply Classical.byContradiction
      intro missing
      have below := not_le_iff_lt.mp missing
      have room : Dedekind.lt point.val Dedekind.one := by
        refine ⟨point.property.2, ?_⟩
        intro reverse
        have equal : point = unitOne := Subtype.ext (Dedekind.le_antisymm point.property.2 reverse)
        rw [equal, distribution.upper] at below
        exact below.2 ((ofUpperBounds thresholds
          (fun index => distribution.function (thresholds index))).function unitOne).property.2
      rcases distribution.right_continuous point room _ below with ⟨right, above, valueBelow⟩
      rcases dense point right above with ⟨index, active, included⟩
      exact valueBelow.2 (Dedekind.le_trans
        (ofUpperBounds_le thresholds (fun index => distribution.function (thresholds index))
          point index active) (distribution.monotone included))
    · exact le_ofUpperBounds thresholds _ point (distribution.function point)
        (fun index active => distribution.monotone active.1)
  exact DistributionFunction.ext same

end

end Problib.Measure.Real.DistributionFunction
