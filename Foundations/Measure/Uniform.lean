module

public import Foundations.Measure.Space.Indicator
public import Foundations.Measure.Additive.Finite
public import Foundations.Measure.Real.Lebesgue

set_option autoImplicit false

/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Gaëtan Serré

Adapted from Mathlib/MeasureTheory/Constructions/UnitInterval.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny uses an explicit Borel space and an explicit probability certificate.
-/

namespace Foundations.Measure.Real

open Foundations.Real
open Foundations.Real.Construction

public section

/-- Lebesgue volume restricted to the closed unit interval. -/
@[expose] noncomputable def restrictedUnit : Measure borel :=
  volume.restrict unitSet

@[simp] theorem restrictedUnit_univ :
    restrictedUnit Set.univ = ENNReal.one := by
  rw [restrictedUnit, Measure.restrict_apply_univ,
    volume_Icc_zero_one]

/-- Restricted volume has total mass one. -/
theorem restrictedUnit_isProbability :
    Measure.IsProbability restrictedUnit :=
  Measure.IsProbability.restrict unitSet volume_Icc_zero_one

/-- Uniform measure on the Borel unit interval. -/
@[expose] noncomputable def uniform01 : Measure unitBorel :=
  restrictedUnit.map clamp01 clamp01Measurable

@[simp] theorem uniform01_univ :
    uniform01 Set.univ = ENNReal.one := by
  rw [uniform01, Measure.map_apply restrictedUnit clamp01
    clamp01Measurable unitBorel.univ, Set.preimage_univ,
    restrictedUnit_univ]

/-- The uniform measure on the unit interval has total mass one. -/
theorem uniform01_isProbability :
    Measure.IsProbability uniform01 :=
  restrictedUnit_isProbability.map clamp01 clamp01Measurable

/-- Including the uniform unit-interval measure recovers restricted volume. -/
theorem uniform01_map_unitInclusion :
    uniform01.map unitInclusion unitInclusionMeasurable = restrictedUnit := by
  rw [uniform01, Measure.map_comp restrictedUnit clamp01 unitInclusion
    clamp01Measurable unitInclusionMeasurable]
  apply Measure.ext
  intro set setMeasurable
  have compositeMeasurable : MeasurableMap borel borel
      (fun value => unitInclusion (clamp01 value)) :=
    MeasurableMap.comp unitInclusionMeasurable clamp01Measurable
  rw [Measure.map_apply restrictedUnit
    (fun value => unitInclusion (clamp01 value))
    compositeMeasurable setMeasurable]
  change (volume.restrict unitSet)
      (Set.preimage (fun value => unitInclusion (clamp01 value)) set) =
    (volume.restrict unitSet) set
  rw [Measure.restrict_apply volume unitSet
      (compositeMeasurable setMeasurable),
    Measure.restrict_apply volume unitSet setMeasurable]
  apply congrArg (fun region : Set Carrier => volume region)
  apply Set.ext
  intro value
  constructor
  · rintro ⟨member, unitMember⟩
    change set (unitInclusion (clamp01 value)) at member
    change set value ∧ unitSet value
    rw [clamp01_of_mem unitMember] at member
    exact ⟨member, unitMember⟩
  · rintro ⟨member, unitMember⟩
    refine ⟨?_, unitMember⟩
    change set (unitInclusion (clamp01 value))
    rw [clamp01_of_mem unitMember]
    exact member

/-- The uniform measure of the closed initial interval `[0, x]` equals `x`. -/
public theorem uniform01_unitInitial (upper : UnitInterval) :
    uniform01 (unitInitial upper) = ENNReal.ofReal upper.val := by
  have region : Set.inter (Iic upper.val) unitSet = Icc Dedekind.zero upper.val := by
    apply Set.ext
    intro value
    exact ⟨fun member => ⟨member.2.1, member.1⟩,
      fun member => ⟨member.2, member.1, Dedekind.leTrans member.2 upper.property.2⟩⟩
  calc
    uniform01 (unitInitial upper) =
        (uniform01.map unitInclusion unitInclusionMeasurable) (Iic upper.val) :=
      (Measure.map_apply uniform01 unitInclusion unitInclusionMeasurable
        (measurable_Iic upper.val)).symm
    _ = restrictedUnit (Iic upper.val) :=
      congrArg (fun current : Measure borel => current (Iic upper.val))
        uniform01_map_unitInclusion
    _ = volume (Set.inter (Iic upper.val) unitSet) :=
      volume.restrict_apply unitSet (measurable_Iic upper.val)
    _ = volume (Icc Dedekind.zero upper.val) := by rw [region]
    _ = ENNReal.ofReal upper.val := by
      rw [volume_Icc, Dedekind.subEqAddNeg, Dedekind.negZero, Dedekind.addZero]

/-- Singletons have measure zero under `uniform01`. -/
theorem uniform01_singleton (point : UnitInterval) :
    uniform01 (Set.singleton point) = ENNReal.zero := by
  have preimage : Set.preimage unitInclusion (Set.singleton point.val) = Set.singleton point := by
    apply Set.ext
    intro value
    exact ⟨fun equal => Subtype.ext equal, fun equal => congrArg Subtype.val equal⟩
  have transported := Measure.map_apply uniform01 unitInclusion unitInclusionMeasurable
    (measurable_singleton point.val)
  rw [uniform01_map_unitInclusion, preimage] at transported
  rw [← transported]
  apply ENNReal.eqZeroOfLeZero
  have restricted : restrictedUnit (Set.singleton point.val) =
      volume (Set.inter (Set.singleton point.val) unitSet) :=
    volume.restrict_apply unitSet (measurable_singleton point.val)
  rw [restricted]
  have bound := volume.mono (Set.inter_subset_left (Set.singleton point.val) unitSet)
  rw [volume_singleton] at bound
  exact bound

/-- The uniform measure of the strict initial interval `{y | y < x}` equals `x`, by nullness of singletons. -/
theorem uniform01_strict_initial (upper : UnitInterval) :
    uniform01 (fun value => Dedekind.lt value.val upper.val) = ENNReal.ofReal upper.val := by
  have same : uniform01 (fun value => Dedekind.lt value.val upper.val) =
      uniform01 (unitInitial upper) := by
    apply Measure.measure_eq_of_null_difference
    · apply uniform01.null_empty.mono
      intro value member
      exact member.2 member.1.1
    · apply Measure.NullSet.mono
        (show uniform01.NullSet (Set.singleton upper) from uniform01_singleton upper)
      intro value member
      apply Subtype.ext
      exact Dedekind.leAntisymm member.1 (notLtIffLe.mp member.2)
  exact same.trans (uniform01_unitInitial upper)

/-- Boolean indicator testing whether a point in the unit interval is strictly below a threshold. -/
noncomputable def unitThreshold (upper : UnitInterval) : UnitInterval → Bool :=
  boolIndicator (fun value => Dedekind.lt value.val upper.val)

/-- The threshold indicator is a measurable map from `unitBorel` to discrete `Bool`. -/
theorem unitThreshold_measurable (upper : UnitInterval) :
    MeasurableMap unitBorel (Space.discrete Bool) (unitThreshold upper) :=
  boolIndicator_measurable (unitInclusionMeasurable (measurable_Iio upper.val))

/-- The pushforward of `uniform01` under `unitThreshold upper` assigns exact mass `upper.val` to `{true}`. -/
theorem uniform01_threshold_true (upper : UnitInterval) :
    (uniform01.map (unitThreshold upper) (unitThreshold_measurable upper)) (Set.singleton true) =
      ENNReal.ofReal upper.val := by
  rw [Measure.map_apply _ _ _ (Space.discrete_measurable _)]
  have preimage : Set.preimage (unitThreshold upper) (Set.singleton true) =
      (fun value => Dedekind.lt value.val upper.val) := by
    apply Set.ext
    intro input
    simp [Set.preimage, Set.singleton, unitThreshold, boolIndicator]
  rw [preimage, uniform01_strict_initial]

end

end Foundations.Measure.Real
