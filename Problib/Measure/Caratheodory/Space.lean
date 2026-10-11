module

public import Problib.Measure.Caratheodory.Basic
public import Problib.Measure.Space

set_option autoImplicit false

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Adapted from Mathlib/MeasureTheory/OuterMeasure/Caratheodory.lean and
Mathlib/MeasureTheory/OuterMeasure/OfFunction.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny constructs the sigma-algebra directly from natural-number indexed
families. The proof is independent of Mathlib.
-/

namespace Problib.Measure

open Problib.Real

universe u

namespace OuterMeasure

variable {α : Type u}

public theorem inter_iUnion_apply (outer : OuterMeasure α)
    (probe : Set α) {sets : Nat → Set α}
    (caratheodory : ∀ index, outer.IsCaratheodory (sets index))
    (pairwise : Set.PairwiseDisjoint sets) :
    outer (Set.inter probe (Set.iUnion sets)) =
      ENNReal.tsum (fun index => outer (Set.inter probe (sets index))) := by
  apply ENNReal.le_antisymm
  · rw [Set.inter_iUnion]
    exact outer.iUnion_apply_le _
  · apply ENNReal.tsum_le
    intro count
    rw [outer.partialSum_inter_eq caratheodory pairwise probe count]
    apply outer.mono_apply
    intro value member
    exact ⟨member.1,
      Set.prefixUnion_subset_iUnion sets count member.2⟩

public theorem iUnion_eq_of_caratheodory (outer : OuterMeasure α)
    {sets : Nat → Set α}
    (caratheodory : ∀ index, outer.IsCaratheodory (sets index))
    (pairwise : Set.PairwiseDisjoint sets) :
    outer (Set.iUnion sets) = ENNReal.tsum (fun index => outer (sets index)) := by
  simpa only [Set.inter_univ_left] using
    outer.inter_iUnion_apply Set.univ caratheodory pairwise

public theorem isCaratheodory_iUnion_of_disjoint
    (outer : OuterMeasure α) {sets : Nat → Set α}
    (caratheodory : ∀ index, outer.IsCaratheodory (sets index))
    (pairwise : Set.PairwiseDisjoint sets) :
    outer.IsCaratheodory (Set.iUnion sets) := by
  apply (isCaratheodory_iff_reverse outer (Set.iUnion sets)).mpr
  intro set
  let pieces : Nat → ENNReal :=
    fun index => outer (Set.inter set (sets index))
  have splitUnion :
      outer (Set.inter set (Set.iUnion sets)) = ENNReal.tsum pieces :=
    outer.inter_iUnion_apply set caratheodory pairwise
  rw [splitUnion]
  unfold ENNReal.tsum
  rw [ENNReal.add_comm, ENNReal.add_iSup]
  apply ENNReal.iSup_le
  intro count
  rw [ENNReal.add_comm]
  have remainingBound : ENNReal.le
      (outer (Set.difference set (Set.iUnion sets)))
      (outer (Set.difference set (Set.prefixUnion sets count))) := by
    apply outer.mono_apply
    intro value member
    exact ⟨member.1, fun prefixMember =>
      member.2 (Set.prefixUnion_subset_iUnion sets count prefixMember)⟩
  have bound := ENNReal.add_le_add_left remainingBound
    (ENNReal.partialSum pieces count)
  rw [outer.partialSum_inter_eq caratheodory pairwise set count,
    ← outer.isCaratheodory_prefixUnion caratheodory count set] at bound
  rw [outer.partialSum_inter_eq caratheodory pairwise set count]
  exact bound

public theorem isCaratheodory_disjointed (outer : OuterMeasure α)
    {sets : Nat → Set α}
    (caratheodory : ∀ index, outer.IsCaratheodory (sets index))
    (index : Nat) : outer.IsCaratheodory (Set.disjointed sets index) :=
  outer.isCaratheodory_difference (caratheodory index)
    (outer.isCaratheodory_prefixUnion caratheodory index)

public theorem isCaratheodory_iUnion (outer : OuterMeasure α)
    {sets : Nat → Set α}
    (caratheodory : ∀ index, outer.IsCaratheodory (sets index)) :
    outer.IsCaratheodory (Set.iUnion sets) := by
  have disjointedMeasurable : ∀ index,
      outer.IsCaratheodory (Set.disjointed sets index) :=
    fun index => outer.isCaratheodory_disjointed caratheodory index
  have result := outer.isCaratheodory_iUnion_of_disjoint
    disjointedMeasurable (Set.disjointed_pairwise sets)
  rw [Set.iUnion_disjointed] at result
  exact result

@[expose] public def caratheodory (outer : OuterMeasure α) : Space α where
  Measurable := outer.IsCaratheodory
  empty := outer.isCaratheodory_empty
  complement := outer.isCaratheodory_complement
  iUnion := outer.isCaratheodory_iUnion

@[simp] public theorem caratheodory_measurable_iff
    (outer : OuterMeasure α) (region : Set α) :
    (outer.caratheodory).Measurable region ↔ outer.IsCaratheodory region :=
  Iff.rfl

public theorem ofFunction_caratheodory
    (cost : Set α → ENNReal)
    (emptyCost : cost Set.empty = ENNReal.zero) {region : Set α}
    (split : ∀ set, ENNReal.le
      (ENNReal.add (cost (Set.inter set region))
        (cost (Set.difference set region)))
      (cost set)) :
    (OuterMeasure.ofFunction cost emptyCost).IsCaratheodory region := by
  let outer := OuterMeasure.ofFunction cost emptyCost
  apply (isCaratheodory_iff_reverse outer region).mpr
  intro set
  apply OuterMeasure.le_ofFunction_apply cost emptyCost set
  intro cover
  have interCovered : Set.Subset (Set.inter set region)
      (Set.iUnion (fun index => Set.inter (cover.sets index) region)) := by
    intro value member
    rcases cover.covers member.1 with ⟨index, covered⟩
    exact ⟨index, covered, member.2⟩
  have differenceCovered : Set.Subset (Set.difference set region)
      (Set.iUnion
        (fun index => Set.difference (cover.sets index) region)) := by
    intro value member
    rcases cover.covers member.1 with ⟨index, covered⟩
    exact ⟨index, covered, member.2⟩
  have interBound : ENNReal.le (outer (Set.inter set region))
      (ENNReal.tsum
        (fun index => cost (Set.inter (cover.sets index) region))) :=
    ENNReal.le_trans (outer.mono_apply interCovered)
      (ENNReal.le_trans (outer.iUnion_apply_le _)
        (ENNReal.tsum_le_tsum fun index =>
          OuterMeasure.ofFunction_le cost emptyCost _))
  have differenceBound : ENNReal.le (outer (Set.difference set region))
      (ENNReal.tsum
        (fun index => cost (Set.difference (cover.sets index) region))) :=
    ENNReal.le_trans (outer.mono_apply differenceCovered)
      (ENNReal.le_trans (outer.iUnion_apply_le _)
        (ENNReal.tsum_le_tsum fun index =>
          OuterMeasure.ofFunction_le cost emptyCost _))
  have firstBound := ENNReal.add_le_add interBound differenceBound
  have splitBound := ENNReal.tsum_le_tsum fun index =>
    split (cover.sets index)
  rw [ENNReal.tsum_add] at splitBound
  unfold coverCost
  exact ENNReal.le_trans firstBound splitBound

end OuterMeasure

end Problib.Measure
