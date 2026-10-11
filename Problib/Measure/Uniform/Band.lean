module

public import Problib.Measure.Uniform
public import Problib.Measure.Additive.Partition

set_option autoImplicit false

/-! # Uniform mass of a band

A band is the half-open stretch of the unit interval at or above one threshold
and strictly below another. Its uniform mass is its width. The band is the
difference of two initial intervals, so the mass follows from the initial
interval law and Caratheodory additivity, with no appeal to Lebesgue measure
beyond that law.
-/

namespace Problib.Measure.Real

open Problib.Real
open Problib.Real.Construction

public section

/-- The samples at or above `lower` and strictly below `upper`. -/
@[expose] def unitBand (lower upper : Carrier) : Set UnitInterval :=
  fun value => Dedekind.le lower value.val ∧ Dedekind.lt value.val upper

/-- A band is Borel in the unit interval. -/
theorem unitBand_measurable (lower upper : Carrier) :
    unitBorel.Measurable (unitBand lower upper) :=
  unitBorel.inter (unitInclusion_measurable (measurable_ici lower))
    (unitInclusion_measurable (measurable_iio upper))

/-- A band whose upper end does not exceed its lower end holds no sample. -/
theorem unitBand_empty {lower upper : Carrier} (ordered : Dedekind.le upper lower) :
    unitBand lower upper = Set.empty := by
  apply Set.ext
  intro value
  exact ⟨fun member => not_lt_iff_le.mpr (Dedekind.le_trans ordered member.1) member.2,
    fun member => member.elim⟩

/-- The uniform mass of a band between rational thresholds in the unit interval
is its width. -/
theorem uniform01_unitBand (lower upper : Rat) (lowerNonnegative : 0 ≤ lower)
    (ordered : lower ≤ upper) (atMostOne : upper ≤ 1) :
    uniform01 (unitBand (Dedekind.selection.ofRat lower) (Dedekind.selection.ofRat upper)) =
      ENNReal.ofReal (Dedekind.selection.ofRat (upper - lower)) := by
  have embeddedOrdered :
      Dedekind.le (Dedekind.selection.ofRat lower) (Dedekind.selection.ofRat upper) :=
    (Dedekind.ofRat_le_iff lower upper).mpr ordered
  have embeddedAtMostOne (value : Rat) (bounded : value ≤ 1) :
      Dedekind.le (Dedekind.selection.ofRat value) Dedekind.one := by
    rw [← Dedekind.ofRat_one]
    exact (Dedekind.ofRat_le_iff value 1).mpr bounded
  have below : Set.inter
      (fun value : UnitInterval => Dedekind.lt value.val (Dedekind.selection.ofRat upper))
      (fun value => Dedekind.lt value.val (Dedekind.selection.ofRat lower)) =
      fun value => Dedekind.lt value.val (Dedekind.selection.ofRat lower) := by
    apply Set.ext
    intro value
    exact ⟨fun member => member.2, fun member => ⟨Dedekind.lt_of_lt_of_le member embeddedOrdered, member⟩⟩
  have band : Set.difference
      (fun value : UnitInterval => Dedekind.lt value.val (Dedekind.selection.ofRat upper))
      (fun value => Dedekind.lt value.val (Dedekind.selection.ofRat lower)) =
      unitBand (Dedekind.selection.ofRat lower) (Dedekind.selection.ofRat upper) := by
    apply Set.ext
    intro value
    exact ⟨fun member => ⟨not_lt_iff_le.mp member.2, member.1⟩,
      fun member => ⟨member.2, not_lt_iff_le.mpr member.1⟩⟩
  have partition := uniform01.inter_add_difference
    (fun value : UnitInterval => Dedekind.lt value.val (Dedekind.selection.ofRat upper))
    (right := fun value => Dedekind.lt value.val (Dedekind.selection.ofRat lower))
    (unitInclusion_measurable (measurable_iio (Dedekind.selection.ofRat lower)))
  rw [below, band, uniform01_real_initial _ (embeddedAtMostOne upper atMostOne),
    uniform01_real_initial _ (embeddedAtMostOne lower (Rat.le_trans ordered atMostOne))]
    at partition
  have embeddedNonnegative (value : Rat) (nonnegative : 0 ≤ value) :
      Dedekind.le Dedekind.zero (Dedekind.selection.ofRat value) := by
    rw [← Dedekind.ofRat_zero]
    exact (Dedekind.ofRat_le_iff 0 value).mpr nonnegative
  have widthNonnegative : 0 ≤ upper - lower := by grind
  apply ENNReal.add_left_cancel_of_finite (ENNReal.ofReal_finite (Dedekind.selection.ofRat lower))
  rw [partition, ← ENNReal.ofReal_add (embeddedNonnegative lower lowerNonnegative)
    (embeddedNonnegative _ widthNonnegative), ← Dedekind.ofRat_add,
    show lower + (upper - lower) = upper by grind]

/-- Every sample lies below a threshold of at least one, up to the endpoint
itself, which carries no mass. So the initial interval below such a threshold
has full uniform mass. With `uniform01_real_initial`, this gives the mass below
every real threshold: the threshold clamped to the unit interval. -/
theorem uniform01_real_initial_of_one_le (threshold : Carrier)
    (atLeastOne : Dedekind.le Dedekind.one threshold) :
    uniform01 (fun value => Dedekind.lt value.val threshold) = ENNReal.one := by
  classical
  by_cases above : Dedekind.lt Dedekind.one threshold
  · have full : (fun value : UnitInterval => Dedekind.lt value.val threshold) = Set.univ := by
      apply Set.ext
      intro value
      exact ⟨fun _ => trivial, fun _ => Dedekind.lt_of_le_of_lt value.property.2 above⟩
    rw [full, uniform01_univ]
  · have atMostOne : Dedekind.le threshold Dedekind.one :=
      Classical.byContradiction fun notBelow => above ⟨atLeastOne, notBelow⟩
    rw [uniform01_real_initial threshold atMostOne,
      Dedekind.le_antisymm atMostOne atLeastOne, ENNReal.ofReal_one]

end

end Problib.Measure.Real
