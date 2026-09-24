module

public import Problib.Measure.Null.Basic
public import Problib.Measure.Additive.Order

public import Problib.Measure.Additive.Algebra
import Problib.Measure.Additive.Partition

set_option autoImplicit false

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Adapted from Mathlib/MeasureTheory/Measure/Restrict.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.
-/

namespace Problib.Measure

open Problib.Real

universe u

namespace Measure

variable {α : Type u} {space : Space α}

private theorem inter_inter_swap (set region probe : Set α) :
    Set.inter (Set.inter set region) probe =
      Set.inter (Set.inter set probe) region := by
  apply Set.ext
  intro value
  exact ⟨fun member => ⟨⟨member.1.1, member.2⟩, member.1.2⟩,
    fun member => ⟨⟨member.1.1, member.2⟩, member.1.2⟩⟩

private theorem difference_inter (set region probe : Set α) :
    Set.difference (Set.inter set region) probe =
      Set.inter (Set.difference set probe) region := by
  apply Set.ext
  intro value
  exact ⟨fun member => ⟨⟨member.1.1, member.2⟩, member.1.2⟩,
    fun member => ⟨⟨member.1.1, member.2⟩, member.1.2⟩⟩

/-- The outer restriction. Its region need not be measurable. -/
@[expose] public noncomputable def restrictOuter
    (measure : Measure space) (region : Set α) : OuterMeasure α where
  measure := fun set => measure (Set.inter set region)
  empty := by
    rw [Set.inter_empty_left, measure.empty_apply]
  mono := by
    intro left right included
    apply measure.mono
    intro value member
    exact ⟨included member.1, member.2⟩
  iUnion_le := by
    intro sets
    change ENNReal.le
      (measure (Set.inter (Set.iUnion sets) region))
      (ENNReal.tsum (fun index =>
        measure (Set.inter (sets index) region)))
    rw [Set.iUnion_inter]
    exact measure.iUnion_le _

public theorem restrictOuter_isCaratheodory
    (measure : Measure space) (region : Set α) {probe : Set α}
    (probeMeasurable : space.Measurable probe) :
    (measure.restrictOuter region).IsCaratheodory probe := by
  intro set
  change measure (Set.inter set region) =
    ENNReal.add
      (measure (Set.inter (Set.inter set probe) region))
      (measure (Set.inter (Set.difference set probe) region))
  have split := measure.isCaratheodory probeMeasurable
    (Set.inter set region)
  rw [inter_inter_swap, difference_inter] at split
  exact split

/-- Restriction to an arbitrary region, canonically extended from measurable
probes through the restricted outer measure. -/
@[expose] public noncomputable def restrict
    (measure : Measure space) (region : Set α) : Measure space :=
  (measure.restrictOuter region).toMeasure fun _ probeMeasurable =>
    measure.restrictOuter_isCaratheodory region probeMeasurable

@[simp] public theorem restrict_apply (measure : Measure space)
    (region : Set α) {set : Set α}
    (setMeasurable : space.Measurable set) :
    (measure.restrict region) set = measure (Set.inter set region) := by
  unfold restrict
  rw [OuterMeasure.toMeasure_apply (measure.restrictOuter region)
    (fun _ probeMeasurable =>
      measure.restrictOuter_isCaratheodory region probeMeasurable)
    setMeasurable]
  unfold restrictOuter
  rfl

@[simp] public theorem restrict_apply_univ (measure : Measure space)
    (region : Set α) :
    (measure.restrict region) Set.univ = measure region := by
  rw [measure.restrict_apply region space.univ, Set.inter_univ_left]

@[simp] public theorem restrict_univ (measure : Measure space) :
    measure.restrict Set.univ = measure := by
  apply Measure.ext
  intro set setMeasurable
  rw [measure.restrict_apply Set.univ setMeasurable,
    Set.inter_univ_right]

@[simp] public theorem restrict_empty (measure : Measure space) :
    measure.restrict Set.empty = zero space := by
  apply Measure.ext
  intro set setMeasurable
  rw [measure.restrict_apply Set.empty setMeasurable,
    Set.inter_empty_right, measure.empty_apply, zero_apply]

public theorem restrict_add (left right : Measure space)
    {region : Set α} (regionMeasurable : space.Measurable region) :
    (add left right).restrict region =
      add (left.restrict region) (right.restrict region) := by
  apply Measure.ext
  intro set setMeasurable
  have interMeasurable := space.inter setMeasurable regionMeasurable
  rw [(add left right).restrict_apply region setMeasurable,
    add_apply_measurable left right interMeasurable,
    add_apply_measurable (left.restrict region)
      (right.restrict region) setMeasurable,
    left.restrict_apply region setMeasurable,
    right.restrict_apply region setMeasurable]

public theorem restrict_smul (factor : ENNReal) (measure : Measure space)
    {region : Set α} (regionMeasurable : space.Measurable region) :
    (smul factor measure).restrict region =
      smul factor (measure.restrict region) := by
  apply Measure.ext
  intro set setMeasurable
  have interMeasurable := space.inter setMeasurable regionMeasurable
  rw [(smul factor measure).restrict_apply region setMeasurable,
    smul_apply_measurable factor measure interMeasurable,
    smul_apply_measurable factor (measure.restrict region) setMeasurable,
    measure.restrict_apply region setMeasurable]

public theorem restrict_le (measure : Measure space) (region set : Set α) :
    ENNReal.le ((measure.restrict region) set) (measure set) := by
  apply le_of_measurable_le
  intro test testMeasurable
  rw [measure.restrict_apply region testMeasurable]
  exact measure.mono (fun {_} member => member.1)

/-- Preserve measure domination under restriction to an arbitrary region. -/
public theorem restrict_le_restrict {left right : Measure space}
    (included : ∀ set, space.Measurable set → ENNReal.le (left set) (right set))
    (region set : Set α) :
    ENNReal.le ((left.restrict region) set) ((right.restrict region) set) := by
  apply le_of_measurable_le _ set
  intro probe probeMeasurable
  rw [left.restrict_apply region probeMeasurable, right.restrict_apply region probeMeasurable]
  exact le_of_measurable_le included _

public theorem NullSet.restrict {measure : Measure space} {set : Set α}
    (nullSet : measure.NullSet set) (region : Set α) :
    (measure.restrict region).NullSet set := by
  apply ENNReal.eq_zero_of_le_zero
  have bound := measure.restrict_le region set
  rw [nullSet] at bound
  exact bound

/-- Restricting a measure to a region whose complement is outer-null yields the
original measure. -/
public theorem restrict_eq_self_of_complement_null (measure : Measure space)
    {region : Set α} (nullComplement : measure.NullSet (Set.complement region)) :
    measure.restrict region = measure := by
  apply Measure.ext
  intro set setMeasurable
  rw [measure.restrict_apply region setMeasurable]
  apply measure_eq_of_null_difference
  · apply measure.null_empty.mono
    intro value member
    exact member.2 member.1.1
  · apply nullComplement.mono
    intro value member regionMember
    exact member.2 ⟨member.1, regionMember⟩

public theorem restrict_eq_zero_of_null (measure : Measure space)
    {region : Set α} (nullRegion : measure.NullSet region) :
    measure.restrict region = Measure.zero space := by
  apply Measure.ext
  intro set setMeasurable
  rw [measure.restrict_apply region setMeasurable, Measure.zero_apply]
  exact nullRegion.mono (fun {_} member => member.2)

/-- Restricting a restricted measure to a measurable set equals restriction
to the intersection of the two regions. -/
public theorem restrict_restrict (measure : Measure space) (region : Set α)
    {set : Set α} (setMeasurable : space.Measurable set) :
    (measure.restrict region).restrict set =
      measure.restrict (Set.inter set region) := by
  apply Measure.ext
  intro test testMeasurable
  rw [(measure.restrict region).restrict_apply set testMeasurable,
    measure.restrict_apply region (space.inter testMeasurable setMeasurable),
    measure.restrict_apply (Set.inter set region) testMeasurable]
  apply congrArg measure
  apply Set.ext
  intro value
  exact ⟨fun member => ⟨member.1.1, member.1.2, member.2⟩,
    fun member => ⟨⟨member.1, member.2.1⟩, member.2.2⟩⟩

/-- Summing the restrictions of a measure to a measurable region and its complement reconstructs the original measure. -/
public theorem restrict_add_complement (measure : Measure space) {region : Set α}
    (measurable : space.Measurable region) :
    Measure.add (measure.restrict region) (measure.restrict (Set.complement region)) = measure := by
  apply Measure.ext
  intro set setMeasurable
  rw [Measure.add_apply_measurable _ _ setMeasurable,
    Measure.restrict_apply _ _ setMeasurable, Measure.restrict_apply _ _ setMeasurable]
  exact measure.inter_add_difference set measurable

end Measure

end Problib.Measure
