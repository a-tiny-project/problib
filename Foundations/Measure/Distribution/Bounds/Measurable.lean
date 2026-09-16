module

public import Foundations.Measure.Distribution.Bounds

set_option autoImplicit false

namespace Foundations.Measure.Real.DistributionFunction

open Foundations.Real.Construction

universe u
variable {α : Type u} {source : Space α}

/-- Measurability of parameter-dependent bound constructions.
Takes Nat-indexed measurable parameter bounds and fixed thresholds.
Proves the evaluation map at any fixed point is measurable from the source
space to the unit Borel space.
Preserves arbitrary parameter measurable spaces, universes, and empty types. -/
public theorem ofUpperBounds_measurable (thresholds : Nat → UnitInterval)
    (bounds : Nat → α → UnitInterval)
    (measurable : ∀ index, MeasurableMap source unitBorel (bounds index))
    (point : UnitInterval) :
    MeasurableMap source unitBorel
      (fun input => (ofUpperBounds thresholds (fun index => bounds index input)).function point) := by
  classical
  apply measurableMap_unitBorel_iff_Iio.mpr
  intro upper
  by_cases aboveOne : Dedekind.lt Dedekind.one upper
  · have same : (fun input => Dedekind.lt
        ((ofUpperBounds thresholds (fun index => bounds index input)).function point).val upper) =
          (Set.univ : Set α) := by
      apply Set.ext
      intro input
      exact ⟨fun _ => True.intro, fun _ => (ofUpperBounds_lt_iff thresholds _ point upper).mpr
        (Or.inl aboveOne)⟩
    rw [same]
    exact source.univ
  · let regions : Nat → Set α := fun index input =>
      Dedekind.lt point.val (thresholds index).val ∧ Dedekind.lt (bounds index input).val upper
    have regionsMeasurable : ∀ index, source.Measurable (regions index) := by
      intro index
      by_cases active : Dedekind.lt point.val (thresholds index).val
      · have same : regions index = (fun input => Dedekind.lt (bounds index input).val upper) := by
          apply Set.ext
          intro input
          exact ⟨fun member => member.2, fun member => ⟨active, member⟩⟩
        rw [same]
        exact (measurableMap_unitBorel_iff_Iio.mp (measurable index)) upper
      · have same : regions index = Set.empty := by
          apply Set.ext
          intro input
          exact ⟨fun member => active member.1, False.elim⟩
        rw [same]
        exact source.empty
    have same : (fun input => Dedekind.lt
        ((ofUpperBounds thresholds (fun index => bounds index input)).function point).val upper) =
          Set.iUnion regions := by
      apply Set.ext
      intro input
      constructor
      · intro below
        rcases (ofUpperBounds_lt_iff thresholds _ point upper).mp below with
          contradiction | witness
        · exact False.elim (aboveOne contradiction)
        · exact witness
      · intro witness
        exact (ofUpperBounds_lt_iff thresholds _ point upper).mpr (Or.inr witness)
    rw [same]
    exact source.iUnion regionsMeasurable

end Foundations.Measure.Real.DistributionFunction
