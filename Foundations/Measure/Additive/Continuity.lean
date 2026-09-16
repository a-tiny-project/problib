module

public import Foundations.Measure.Additive.Core
public import Foundations.Measure.Set.Family
public import Foundations.Real.Series

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

namespace Foundations.Measure

open Foundations.Real

universe u

namespace Measure

variable {alpha : Type u} {space : Space alpha}

private theorem prefixUnionMeasurable (sets : Nat → Set alpha)
    (measurable : ∀ index, space.Measurable (sets index)) :
    ∀ count, space.Measurable (Set.prefixUnion sets count) := by
  intro count
  induction count with
  | zero => exact space.empty
  | succ count induction =>
      exact space.union induction (measurable count)

private theorem disjointedMeasurable (sets : Nat → Set alpha)
    (measurable : ∀ index, space.Measurable (sets index))
    (index : Nat) :
    space.Measurable (Set.disjointed sets index) :=
  space.difference (measurable index)
    (prefixUnionMeasurable sets measurable index)

private theorem measurePrefixUnionDisjointed (measure : Measure space)
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
          (prefixUnionMeasurable (Set.disjointed sets)
            (disjointedMeasurable sets measurable) count)
          (disjointedMeasurable sets measurable count)
          (Set.prefixUnion_disjoint_right
            (Set.disjointed_pairwise sets) count), induction]

private theorem addLtAddRightOfFinite {left right shift : ENNReal}
    (strict : ENNReal.lt left right) (shiftFinite : ENNReal.Finite shift) :
    ENNReal.lt (ENNReal.add left shift) (ENNReal.add right shift) := by
  constructor
  · exact ENNReal.addLeAddRight strict.1 shift
  · intro reverse
    exact strict.2
      (ENNReal.leOfAddLeAddRightOfFinite shiftFinite reverse)

private theorem unionDifferenceOfSubset {left right : Set alpha}
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

private theorem disjointDifference (left right : Set alpha) :
    Set.Disjoint right (Set.difference left right) := by
  intro value rightMember differenceMember
  exact differenceMember.2 rightMember

private theorem iUnionDifferenceIInter (sets : Nat → Set alpha) :
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
    disjointedMeasurable sets measurable
  have piecesPairwise : Set.PairwiseDisjoint pieces :=
    Set.disjointed_pairwise sets
  have partialBound (count : Nat) :
      ENNReal.le
        (ENNReal.partialSum (fun index => measure (pieces index)) count)
        (ENNReal.iSup (fun index => measure (sets index))) := by
    rw [← measurePrefixUnionDisjointed measure sets measurable count]
    cases count with
    | zero =>
        rw [Set.prefixUnion_zero, Measure.empty_apply]
        exact ENNReal.zeroLe _
    | succ index =>
        rw [Set.prefixUnion_disjointed,
          Set.prefixUnion_succ_eq_of_monotone monotone]
        exact ENNReal.leISup (fun current => measure (sets current)) index
  have seriesUpper :
      ENNReal.le (ENNReal.tsum (fun index => measure (pieces index)))
        (ENNReal.iSup (fun index => measure (sets index))) :=
    ENNReal.tsumLe partialBound
  have supremumUpper :
      ENNReal.le (ENNReal.iSup (fun index => measure (sets index)))
        (ENNReal.tsum (fun index => measure (pieces index))) := by
    apply ENNReal.iSupLe
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
          measurePrefixUnionDisjointed measure sets measurable (index + 1)
    rw [prefixMeasure]
    exact ENNReal.partialSumLeTsum _ _
  calc
    measure (Set.iUnion sets) = measure (Set.iUnion pieces) := by
      rw [Set.iUnion_disjointed]
    _ = ENNReal.tsum (fun index => measure (pieces index)) :=
      measure.iUnion_disjoint pieces piecesMeasurable piecesPairwise
    _ = ENNReal.iSup (fun index => measure (sets index)) :=
      ENNReal.leAntisymm seriesUpper supremumUpper

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
    iUnionDifferenceIInter sets
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
      (disjointDifference (sets 0) (Set.iInter sets)),
      unionDifferenceOfSubset intersectionSubset]
  have differenceFinite :
      ENNReal.Finite
        (measure (Set.difference (sets 0) (Set.iInter sets))) :=
    ENNReal.finiteOfLe
      (measure.mono (Set.difference_subset (sets 0) (Set.iInter sets)))
      firstFinite
  have pointPartition (index : Nat) :
      ENNReal.add (measure (sets index)) (measure (differences index)) =
        measure (sets 0) := by
    have included : Set.Subset (sets index) (sets 0) :=
      antitone (Nat.zero_le index)
    rw [← measure.union_disjoint (measurable index)
      (differencesMeasurable index)
      (disjointDifference (sets 0) (sets index)),
      unionDifferenceOfSubset included]
  apply ENNReal.leAntisymm
  · apply ENNReal.leIInf
    intro index
    exact measure.mono (Set.iInter_subset sets index)
  · apply Classical.byContradiction
    intro notIncluded
    have strict :
        ENNReal.lt (measure (Set.iInter sets))
          (ENNReal.iInf (fun index => measure (sets index))) :=
      ⟨ENNReal.leIInf fun index =>
          measure.mono (Set.iInter_subset sets index), notIncluded⟩
    have shifted := addLtAddRightOfFinite strict differenceFinite
    have upper :
        ENNReal.le
          (ENNReal.add (ENNReal.iInf (fun index => measure (sets index)))
            (measure (Set.difference (sets 0) (Set.iInter sets))))
          (measure (sets 0)) := by
      rw [← supremumDifferences, ENNReal.addISup]
      apply ENNReal.iSupLe
      intro index
      exact ENNReal.leTrans
        (ENNReal.addLeAddRight
          (ENNReal.iInfLe (fun current => measure (sets current)) index)
          (measure (differences index)))
        (by rw [pointPartition index]; exact ENNReal.leRefl _)
    apply shifted.2
    rw [intersectionPartition]
    exact upper

end Measure

end Foundations.Measure
