module

public import Foundations.Measure.Decomposition.Hahn.Score
public import Foundations.Measure.Additive.Continuity

set_option autoImplicit false

/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Loic Simon

Adapted from Mathlib/MeasureTheory/Measure/Decomposition/Hahn.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny uses positive summable errors, finite prefix intersections, and continuity
from above to construct a maximal score region.
-/

namespace Foundations.Measure.Measure.Hahn

open Foundations.Real

universe u

variable {alpha : Type u} {space : Space alpha}

/-- For an antitone sequence of measurable regions and finite left measure,
a uniform defect bound on the sequence bounds the defect of the countable
intersection. -/
public theorem defect_iInter_le {left right : Measure space}
    (leftFinite : IsFinite left) (regions : Nat → Set alpha)
    (measurable : ∀ index, space.Measurable (regions index))
    (antitone : Set.AntitoneFamily regions) {bound : ENNReal}
    (bounds : ∀ index, ENNReal.le (defect left right (regions index)) bound) :
    ENNReal.le (defect left right (Set.iInter regions)) bound := by
  have comparisons : ∀ index, ENNReal.le (supremum left right)
      (ENNReal.add (ENNReal.add bound (right (Set.complement (Set.iInter regions))))
        (left (regions index))) := by
    intro index
    have included : Set.Subset (Set.complement (regions index))
        (Set.complement (Set.iInter regions)) :=
      fun {_} outside member => outside (member index)
    have comparison := ENNReal.leTrans (ENNReal.subLeIffLeAdd.mp (bounds index))
      (ENNReal.addLeAddLeft (ENNReal.addLeAddLeft (right.mono included)
        (left (regions index))) bound)
    rw [← ENNReal.addAssoc,
      ENNReal.addRightComm bound (left (regions index))] at comparison
    exact comparison
  have limit := ENNReal.leIInf comparisons
  rw [← ENNReal.addIInf,
    ← left.continuity_from_above regions measurable antitone (leftFinite.apply (regions 0)),
    ENNReal.addRightComm bound _ _, ENNReal.addAssoc] at limit
  exact ENNReal.subLeIffLeAdd.mpr limit

/-- Liminf (lower limit set) $\bigcup_m \bigcap_{n \ge m} A_n$ of a sequence of sets. -/
@[expose] public def limitSet (sets : Nat → Set alpha) : Set alpha :=
  Set.iUnion (fun start => Set.iInter (fun index => sets (start + index)))

/-- Measurability of the lower limit set of a sequence of measurable sets. -/
public theorem limitSet_measurable (sets : Nat → Set alpha)
    (measurable : ∀ index, space.Measurable (sets index)) :
    space.Measurable (limitSet sets) :=
  space.iUnion (fun start => space.iInter (fun index => measurable (start + index)))

/-- The lower limit set of an approximating sequence with summable defects achieves
maximal Hahn score against any measurable set. -/
public theorem score_le_limitSet {left right : Measure space}
    (leftFinite : IsFinite left) (rightFinite : IsFinite right)
    (sets : Nat → Set alpha)
    (measurable : ∀ index, space.Measurable (sets index))
    (errors : Nat → ENNReal) (errorsFinite : ENNReal.Finite (ENNReal.tsum errors))
    (bounds : ∀ index, ENNReal.le (defect left right (sets index)) (errors index))
    {other : Set alpha} (otherMeasurable : space.Measurable other) :
    ENNReal.le (score left right other) (score left right (limitSet sets)) := by
  have prefixMeasurable (start : Nat) :
      ∀ count, space.Measurable (Set.prefixInter (fun index => sets (start + index)) count) := by
    intro count
    induction count with
    | zero => exact space.univ
    | succ count induction => exact space.inter induction (measurable (start + count))
  have prefixBound (start : Nat) : ∀ count,
      ENNReal.le (defect left right
        (Set.prefixInter (fun index => sets (start + index)) (count + 1)))
        (ENNReal.partialSum (fun index => errors (start + index)) (count + 1)) := by
    intro count
    induction count with
    | zero =>
        change ENNReal.le (defect left right (Set.inter Set.univ (sets start)))
          (ENNReal.add ENNReal.zero (errors start))
        rw [Set.inter_univ_left, ENNReal.zeroAdd]
        exact bounds start
    | succ count induction =>
        apply ENNReal.leTrans
          (defect_inter_le leftFinite rightFinite (prefixMeasurable start (count + 1))
            (measurable (start + (count + 1))))
        exact ENNReal.addLeAdd induction (bounds (start + (count + 1)))
  let regions : Nat → Set alpha :=
    fun start => Set.iInter (fun index => sets (start + index))
  have regionsMeasurable : ∀ start, space.Measurable (regions start) :=
    fun start => space.iInter (fun index => measurable (start + index))
  have regionsBound : ∀ start, ENNReal.le (defect left right (regions start))
      (ENNReal.tsum (fun index => errors (start + index))) := by
    intro start
    have same :
        Set.iInter (fun count => Set.prefixInter (fun index => sets (start + index))
          (count + 1)) = regions start := by
      apply Set.ext
      intro value
      constructor
      · intro member index
        exact (Set.mem_prefixInter _ (index + 1) value).mp (member index) index (by omega)
      · intro member count
        exact (Set.mem_prefixInter _ (count + 1) value).mpr (fun index _ => member index)
    rw [← same]
    apply defect_iInter_le leftFinite _ (fun count => prefixMeasurable start (count + 1))
    · intro first second included
      exact Set.prefixInter_antitone _ (by omega : first + 1 ≤ second + 1)
    · intro count
      exact ENNReal.leTrans (prefixBound start count)
        (ENNReal.partialSumLeTsum _ (count + 1))
  have regionsMonotone : Set.MonotoneFamily regions := by
    intro first second included value member index
    have current := member (second - first + index)
    simpa only [← Nat.add_assoc, Nat.add_sub_of_le included] using current
  have complementAntitone :
      Set.AntitoneFamily (fun index => Set.complement (regions index)) := by
    intro first second included value outside member
    exact outside (regionsMonotone included member)
  have comparisons : ∀ index, ENNReal.le (supremum left right)
      (ENNReal.add (left (Set.iUnion regions))
        (ENNReal.add (right (Set.complement (regions index)))
          (ENNReal.tsum (fun current => errors (index + current))))) := by
    intro index
    have comparison := ENNReal.leTrans (ENNReal.subLeIffLeAdd.mp (regionsBound index))
      (ENNReal.addLeAddLeft
        (ENNReal.addLeAddRight (left.mono (Set.subset_iUnion regions index))
          (right (Set.complement (regions index))))
        (ENNReal.tsum (fun current => errors (index + current))))
    rw [ENNReal.addLeftComm, ENNReal.addComm
      (ENNReal.tsum (fun current => errors (index + current)))] at comparison
    exact comparison
  have limit := ENNReal.leIInf comparisons
  rw [← ENNReal.addIInf,
    ENNReal.iInfDiagonalAdd _ _
      (fun {_ _} included => right.mono (complementAntitone included))
      (fun {_ _} included => ENNReal.tailAntitone errors included),
    ENNReal.iInfTailEqZero errorsFinite, ENNReal.addZero,
    ← right.continuity_from_above _
      (fun index => space.complement (regionsMeasurable index)) complementAntitone
      (rightFinite.apply (Set.complement (regions 0))),
    ← Set.complement_iUnion] at limit
  exact ENNReal.leTrans (score_le_supremum left right otherMeasurable) limit


/-- For any two finite measures, there exists a measurable region that achieves
the maximal score across all measurable sets. -/
public theorem exists_maximizer {left right : Measure space}
    (leftFinite : IsFinite left) (rightFinite : IsFinite right) :
    ∃ region, space.Measurable region ∧
      ∀ other, space.Measurable other →
        ENNReal.le (score left right other) (score left right region) := by
  classical
  rcases ENNReal.existsPositiveSummableError ENNReal.one True.intro
    ENNReal.onePositive with ⟨errors, positive, summable⟩
  have errorsFinite : ENNReal.Finite (ENNReal.tsum errors) :=
    ENNReal.finiteOfLe summable True.intro
  have choices := fun index => exists_defect_le leftFinite rightFinite (positive index)
  let sets : Nat → Set alpha := fun index => Classical.choose (choices index)
  have properties := fun index => Classical.choose_spec (choices index)
  exact ⟨limitSet sets, limitSet_measurable sets (fun index => (properties index).1),
    fun _ measurable => score_le_limitSet leftFinite rightFinite sets
      (fun index => (properties index).1) errors errorsFinite
      (fun index => (properties index).2) measurable⟩

end Foundations.Measure.Measure.Hahn
