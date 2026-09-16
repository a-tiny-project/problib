module

public import Foundations.Measure.Real.Borel
public import Foundations.Measure.Additive.Continuity
public import Foundations.Measure.Additive.Finite

set_option autoImplicit false

namespace Foundations.Measure.Real

open Foundations.Real
open Foundations.Real.Construction

/-- For a finite measure on the unit interval, countable right-dense thresholds
bound initial-interval mass from below. The candidate scalar is bounded by total
mass and all active threshold masses. -/
public theorem le_measure_unitInitial_of_rightDense
    {measure : Measure unitBorel} (finite : Measure.IsFinite measure)
    (thresholds : Nat → UnitInterval)
    (dense : ∀ point right : UnitInterval, Dedekind.lt point.val right.val →
      ∃ index, Dedekind.lt point.val (thresholds index).val ∧
        Dedekind.le (thresholds index).val right.val)
    (point : UnitInterval) {value : ENNReal}
    (totalBound : ENNReal.le value (measure Set.univ))
    (bounds : ∀ index, Dedekind.lt point.val (thresholds index).val →
      ENNReal.le value (measure (unitInitial (thresholds index)))) :
    ENNReal.le value (measure (unitInitial point)) := by
  classical
  let upper : Nat → UnitInterval := fun index =>
    if Dedekind.lt point.val (thresholds index).val then thresholds index else unitOne
  let sets : Nat → Set UnitInterval := fun index => unitInitial (upper index)
  have upperAbove (index : Nat) : Dedekind.le point.val (upper index).val := by
    dsimp [upper]
    split
    · exact ‹Dedekind.lt point.val (thresholds index).val›.1
    · exact point.property.2
  have upperBound (index : Nat) : ENNReal.le value (measure (sets index)) := by
    dsimp [sets, upper]
    split
    · exact bounds index ‹_›
    · rw [unitInitial_one]
      exact totalBound
  have prefixBound : ∀ count, ∃ endpoint : UnitInterval,
      Set.prefixInter sets count = unitInitial endpoint ∧
        ENNReal.le value (measure (unitInitial endpoint)) := by
    intro count
    induction count with
    | zero => exact ⟨unitOne, unitInitial_one.symm, by simpa only [unitInitial_one] using totalBound⟩
    | succ count induction =>
        rcases induction with ⟨endpoint, same, bounded⟩
        change ∃ result, Set.inter (Set.prefixInter sets count) (sets count) =
          unitInitial result ∧ ENNReal.le value (measure (unitInitial result))
        rw [same]
        rcases Dedekind.leTotal endpoint.val (upper count).val with included | included
        · refine ⟨endpoint, ?_, bounded⟩
          apply Set.ext
          intro input
          exact ⟨fun member => member.1,
            fun member => ⟨member, Dedekind.leTrans member included⟩⟩
        · refine ⟨upper count, ?_, upperBound count⟩
          apply Set.ext
          intro input
          exact ⟨fun member => member.2,
            fun member => ⟨Dedekind.leTrans member included, member⟩⟩
  have prefixMeasurable : ∀ count, unitBorel.Measurable (Set.prefixInter sets count) := by
    intro count
    rcases prefixBound count with ⟨endpoint, same, _⟩
    rw [same]
    exact unitInitialMeasurable endpoint
  have intersection : Set.iInter sets = unitInitial point := by
    apply Set.ext
    intro input
    constructor
    · intro member
      apply Classical.byContradiction
      intro missing
      have above := notLeIffLt.mp missing
      rcases existsUnitRightBelow point input.val
          (ltOfLtOfLe above input.property.2) above with ⟨right, rightAbove, rightBelow⟩
      rcases dense point right rightAbove with ⟨index, active, below⟩
      have atIndex := member index
      change Dedekind.le input.val (upper index).val at atIndex
      simp only [upper, if_pos active] at atIndex
      exact rightBelow.2 (Dedekind.leTrans atIndex below)
    · intro member index
      exact Dedekind.leTrans member (upperAbove index)
  have continuous := measure.continuity_from_above (Set.prefixInter sets)
    prefixMeasurable (Set.prefixInter_antitone sets) (finite.apply _)
  rw [Set.iInter_prefixInter, intersection] at continuous
  rw [continuous]
  apply ENNReal.leIInf
  intro count
  rcases prefixBound count with ⟨endpoint, same, bounded⟩
  rw [same]
  exact bounded

end Foundations.Measure.Real
