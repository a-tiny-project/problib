module

public import Problib.Measure.Additive.Core
public import Problib.Measure.Set.Family
public import Problib.Real.Series

set_option autoImplicit false

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Adapted from Mathlib/MeasureTheory/Measure/Continuity.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny proves continuity directly from countable additivity and its local
extended-nonnegative-real supremum.
-/

namespace Problib.Measure

open Problib.Real

universe u

namespace Measure

variable {alpha : Type u} {space : Space alpha}

private theorem measure_prefixUnion_disjointed (measure : Measure space)
    (sets : Nat → Set alpha)
    (measurable : ∀ index, space.Measurable (sets index)) :
    ∀ count,
      measure (Set.prefixUnion (Set.disjointed sets) count) =
        ENNReal.partialSum
          (fun index => measure (Set.disjointed sets index)) count := by
  intro count
  induction count with
  | zero =>
      rw [Set.prefixUnion_zero, ENNReal.partialSum, Measure.empty_apply]
  | succ count induction =>
      rw [Set.prefixUnion_succ, ENNReal.partialSum,
        measure.union_disjoint
          (space.prefixUnion_measurable
            (space.disjointed_measurable measurable) count)
          (space.disjointed_measurable measurable count)
          (Set.prefixUnion_disjoint_right
            (Set.disjointed_pairwise sets) count), induction]

private theorem add_lt_add_right_of_finite {left right shift : ENNReal}
    (strict : ENNReal.lt left right) (shiftFinite : ENNReal.Finite shift) :
    ENNReal.lt (ENNReal.add left shift) (ENNReal.add right shift) := by
  constructor
  · exact ENNReal.add_le_add_right strict.1 shift
  · intro reverse
    exact strict.2
      (ENNReal.le_of_add_le_add_right_of_finite shiftFinite reverse)

private theorem union_difference_of_subset {left right : Set alpha}
    (included : Set.Subset right left) :
    Set.union right (Set.difference left right) = left := by
  classical
  apply Set.ext
  intro value
  constructor
  · intro member
    cases member with
    | inl rightMember => exact included rightMember
    | inr differenceMember => exact differenceMember.1
  · intro leftMember
    by_cases rightMember : right value
    · exact Or.inl rightMember
    · exact Or.inr ⟨leftMember, rightMember⟩

private theorem disjoint_difference (left right : Set alpha) :
    Set.Disjoint right (Set.difference left right) := by
  intro value rightMember differenceMember
  exact differenceMember.2 rightMember

private theorem iUnion_difference_iInter (sets : Nat → Set alpha) :
    Set.iUnion (fun index => Set.difference (sets 0) (sets index)) =
      Set.difference (sets 0) (Set.iInter sets) := by
  classical
  apply Set.ext
  intro value
  constructor
  · rintro ⟨index, firstMember, missing⟩
    exact ⟨firstMember, fun allMembers => missing (allMembers index)⟩
  · rintro ⟨firstMember, notAll⟩
    apply Classical.byContradiction
    intro noWitness
    apply notAll
    intro index
    apply Classical.byContradiction
    intro missing
    exact noWitness ⟨index, firstMember, missing⟩

public theorem continuity_from_below (measure : Measure space)
    (sets : Nat → Set alpha)
    (measurable : ∀ index, space.Measurable (sets index))
    (monotone : Set.MonotoneFamily sets) :
    measure (Set.iUnion sets) =
      ENNReal.iSup (fun index => measure (sets index)) := by
  let pieces := Set.disjointed sets
  have piecesMeasurable : ∀ index, space.Measurable (pieces index) :=
    space.disjointed_measurable measurable
  have piecesPairwise : Set.PairwiseDisjoint pieces :=
    Set.disjointed_pairwise sets
  have partialBound (count : Nat) :
      ENNReal.le
        (ENNReal.partialSum (fun index => measure (pieces index)) count)
        (ENNReal.iSup (fun index => measure (sets index))) := by
    rw [← measure_prefixUnion_disjointed measure sets measurable count]
    cases count with
    | zero =>
        rw [Set.prefixUnion_zero, Measure.empty_apply]
        exact ENNReal.zero_le _
    | succ index =>
        rw [Set.prefixUnion_disjointed,
          Set.prefixUnion_succ_eq_of_monotone monotone]
        exact ENNReal.le_iSup (fun current => measure (sets current)) index
  have seriesUpper :
      ENNReal.le (ENNReal.tsum (fun index => measure (pieces index)))
        (ENNReal.iSup (fun index => measure (sets index))) :=
    ENNReal.tsum_le partialBound
  have supremumUpper :
      ENNReal.le (ENNReal.iSup (fun index => measure (sets index)))
        (ENNReal.tsum (fun index => measure (pieces index))) := by
    apply ENNReal.iSup_le
    intro index
    have prefixMeasure :
        measure (sets index) =
          ENNReal.partialSum (fun current => measure (pieces current))
            (index + 1) := by
      calc
        measure (sets index) =
            measure (Set.prefixUnion pieces (index + 1)) := by
          rw [Set.prefixUnion_disjointed,
            Set.prefixUnion_succ_eq_of_monotone monotone]
        _ = ENNReal.partialSum (fun current => measure (pieces current))
            (index + 1) :=
          measure_prefixUnion_disjointed measure sets measurable (index + 1)
    rw [prefixMeasure]
    exact ENNReal.partialSum_le_tsum _ _
  calc
    measure (Set.iUnion sets) = measure (Set.iUnion pieces) := by
      rw [Set.iUnion_disjointed]
    _ = ENNReal.tsum (fun index => measure (pieces index)) :=
      measure.iUnion_disjoint pieces piecesMeasurable piecesPairwise
    _ = ENNReal.iSup (fun index => measure (sets index)) :=
      ENNReal.le_antisymm seriesUpper supremumUpper

public theorem continuity_from_above (measure : Measure space)
    (sets : Nat → Set alpha)
    (measurable : ∀ index, space.Measurable (sets index))
    (antitone : Set.AntitoneFamily sets)
    (firstFinite : ENNReal.Finite (measure (sets 0))) :
    measure (Set.iInter sets) =
      ENNReal.iInf (fun index => measure (sets index)) := by
  let differences : Nat → Set alpha :=
    fun index => Set.difference (sets 0) (sets index)
  have differencesMeasurable :
      ∀ index, space.Measurable (differences index) :=
    fun index => space.difference (measurable 0) (measurable index)
  have differencesMonotone : Set.MonotoneFamily differences := by
    intro first second firstSecond value member
    exact ⟨member.1, fun secondMember =>
      member.2 (antitone firstSecond secondMember)⟩
  have differencesContinuous :=
    continuity_from_below measure differences differencesMeasurable
      differencesMonotone
  have unionDifferences :
      Set.iUnion differences =
        Set.difference (sets 0) (Set.iInter sets) :=
    iUnion_difference_iInter sets
  have supremumDifferences :
      ENNReal.iSup (fun index => measure (differences index)) =
        measure (Set.difference (sets 0) (Set.iInter sets)) := by
    rw [← differencesContinuous, unionDifferences]
  have intersectionMeasurable : space.Measurable (Set.iInter sets) :=
    space.iInter measurable
  have intersectionSubset : Set.Subset (Set.iInter sets) (sets 0) :=
    Set.iInter_subset sets 0
  have intersectionPartition :
      ENNReal.add (measure (Set.iInter sets))
          (measure (Set.difference (sets 0) (Set.iInter sets))) =
        measure (sets 0) := by
    rw [← measure.union_disjoint intersectionMeasurable
      (space.difference (measurable 0) intersectionMeasurable)
      (disjoint_difference (sets 0) (Set.iInter sets)),
      union_difference_of_subset intersectionSubset]
  have differenceFinite :
      ENNReal.Finite
        (measure (Set.difference (sets 0) (Set.iInter sets))) :=
    ENNReal.finite_of_le
      (measure.mono (Set.difference_subset (sets 0) (Set.iInter sets)))
      firstFinite
  have pointPartition (index : Nat) :
      ENNReal.add (measure (sets index)) (measure (differences index)) =
        measure (sets 0) := by
    have included : Set.Subset (sets index) (sets 0) :=
      antitone (Nat.zero_le index)
    rw [← measure.union_disjoint (measurable index)
      (differencesMeasurable index)
      (disjoint_difference (sets 0) (sets index)),
      union_difference_of_subset included]
  apply ENNReal.le_antisymm
  · apply ENNReal.le_iInf
    intro index
    exact measure.mono (Set.iInter_subset sets index)
  · apply Classical.byContradiction
    intro notIncluded
    have strict :
        ENNReal.lt (measure (Set.iInter sets))
          (ENNReal.iInf (fun index => measure (sets index))) :=
      ⟨ENNReal.le_iInf fun index =>
          measure.mono (Set.iInter_subset sets index), notIncluded⟩
    have shifted := add_lt_add_right_of_finite strict differenceFinite
    have upper :
        ENNReal.le
          (ENNReal.add (ENNReal.iInf (fun index => measure (sets index)))
            (measure (Set.difference (sets 0) (Set.iInter sets))))
          (measure (sets 0)) := by
      rw [← supremumDifferences, ENNReal.add_iSup]
      apply ENNReal.iSup_le
      intro index
      exact ENNReal.le_trans
        (ENNReal.add_le_add_right
          (ENNReal.iInf_le (fun current => measure (sets current)) index)
          (measure (differences index)))
        (by rw [pointPartition index]; exact ENNReal.le_refl _)
    apply shifted.2
    rw [intersectionPartition]
    exact upper

end Measure

end Problib.Measure
