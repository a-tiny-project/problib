module

public import Foundations.Measure.Additive.Map
public import Foundations.Measure.Additive.Restrict

set_option autoImplicit false

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Adapted from Mathlib/MeasureTheory/Measure/Sum.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.
-/

namespace Foundations.Measure

open Foundations.Real

universe u v

namespace Measure

variable {α : Type u} {β : Type v}
  {source : Space α} {target : Space β}

/-- Countable sum, defined pointwise on measurable content. -/
@[expose] public noncomputable def sum
    (measures : Nat → Measure source) : Measure source where
  content := fun set measurable => ENNReal.tsum
    (fun index => (measures index).content set measurable)
  empty := by
    calc
      ENNReal.tsum (fun index =>
          (measures index).content Set.empty source.empty) =
          ENNReal.tsum (fun _ => ENNReal.zero) := by
        apply ENNReal.tsumCongr
        intro index
        exact (measures index).empty
      _ = ENNReal.zero := ENNReal.tsumZero
  content_iUnion_disjoint := by
    intro sets measurable pairwise
    calc
      ENNReal.tsum (fun measureIndex =>
          (measures measureIndex).content (Set.iUnion sets)
            (source.iUnion measurable)) =
          ENNReal.tsum (fun measureIndex =>
            ENNReal.tsum (fun setIndex =>
              (measures measureIndex).content (sets setIndex)
                (measurable setIndex))) := by
        apply ENNReal.tsumCongr
        intro measureIndex
        exact (measures measureIndex).content_iUnion_disjoint
          sets measurable pairwise
      _ = ENNReal.tsum (fun setIndex =>
          ENNReal.tsum (fun measureIndex =>
            (measures measureIndex).content (sets setIndex)
              (measurable setIndex))) :=
        ENNReal.tsumComm fun measureIndex setIndex =>
          (measures measureIndex).content (sets setIndex)
            (measurable setIndex)

@[simp] public theorem sum_apply (measures : Nat → Measure source)
    {set : Set α} (setMeasurable : source.Measurable set) :
    (sum measures) set = ENNReal.tsum (fun index => measures index set) := by
  rw [(sum measures).apply_measurable setMeasurable]
  apply ENNReal.tsumCongr
  intro index
  exact ((measures index).apply_measurable setMeasurable).symm

/-- Each component measure is bounded by the countable sum of measures on any
arbitrary set. -/
public theorem le_sum (measures : Nat → Measure source) (index : Nat) (set : Set α) :
    ENNReal.le (measures index set) (Measure.sum measures set) := by
  apply Measure.le_of_measurable_le _ set
  intro region measurable
  rw [Measure.sum_apply measures measurable]
  exact ENNReal.termLeTsum (fun stage => measures stage region) index

@[simp] public theorem sum_zero :
    sum (fun _ => zero source) = zero source := by
  apply Measure.ext
  intro set setMeasurable
  rw [sum_apply (fun _ => zero source) setMeasurable,
    zero_apply, ENNReal.tsumZero]

public theorem sum_add (left right : Nat → Measure source) :
    sum (fun index => add (left index) (right index)) =
      add (sum left) (sum right) := by
  apply Measure.ext
  intro set setMeasurable
  rw [sum_apply (fun index => add (left index) (right index))
      setMeasurable,
    add_apply_measurable (sum left) (sum right) setMeasurable,
    sum_apply left setMeasurable, sum_apply right setMeasurable]
  calc
    ENNReal.tsum (fun index => add (left index) (right index) set) =
        ENNReal.tsum (fun index =>
          ENNReal.add (left index set) (right index set)) := by
      apply ENNReal.tsumCongr
      intro index
      exact add_apply_measurable (left index) (right index) setMeasurable
    _ = ENNReal.add (ENNReal.tsum (fun index => left index set))
        (ENNReal.tsum (fun index => right index set)) :=
      ENNReal.tsumAdd
        (fun index => left index set) (fun index => right index set)

public theorem sum_reindex (equivalence : Bijection Nat Nat)
    (measures : Nat → Measure source) :
    sum (fun index => measures (equivalence.forward index)) =
      sum measures := by
  apply Measure.ext
  intro set setMeasurable
  rw [sum_apply (fun index => measures (equivalence.forward index))
      setMeasurable,
    sum_apply measures setMeasurable]
  exact ENNReal.tsumReindex equivalence (fun index => measures index set)

public theorem sum_comm (measures : Nat → Nat → Measure source) :
    sum (fun first => sum (measures first)) =
      sum (fun second => sum (fun first => measures first second)) := by
  apply Measure.ext
  intro set setMeasurable
  rw [sum_apply (fun first => sum (measures first)) setMeasurable,
    sum_apply (fun second => sum (fun first => measures first second))
      setMeasurable]
  have leftValues : (fun first => sum (measures first) set) =
      (fun first => ENNReal.tsum
        (fun second => measures first second set)) := by
    funext first
    exact sum_apply (measures first) setMeasurable
  have rightValues :
      (fun second => sum (fun first => measures first second) set) =
      (fun second => ENNReal.tsum
        (fun first => measures first second set)) := by
    funext second
    exact sum_apply (fun first => measures first second) setMeasurable
  rw [leftValues, rightValues]
  exact ENNReal.tsumComm fun first second => measures first second set

@[expose] public def flatten
    (measures : Nat → Nat → Measure source) : Nat → Measure source :=
  fun index =>
    let pair := NatProductBijection.decode index
    measures pair.1 pair.2

public theorem sum_double (measures : Nat → Nat → Measure source) :
    sum (flatten measures) = sum (fun row => sum (measures row)) := by
  apply Measure.ext
  intro set setMeasurable
  rw [sum_apply (flatten measures) setMeasurable,
    sum_apply (fun row => sum (measures row)) setMeasurable]
  have rows : (fun row => sum (measures row) set) =
      (fun row => ENNReal.tsum
        (fun column => measures row column set)) := by
    funext row
    exact sum_apply (measures row) setMeasurable
  rw [rows]
  exact ENNReal.tsumFlatten fun row column => measures row column set

public theorem map_sum (measures : Nat → Measure source)
    (function : α → β)
    (measurable : MeasurableMap source target function) :
    (sum measures).map function measurable =
      sum (fun index => (measures index).map function measurable) := by
  apply Measure.ext
  intro set setMeasurable
  rw [(sum measures).map_apply function measurable setMeasurable,
    sum_apply measures (measurable setMeasurable),
    sum_apply (fun index => (measures index).map function measurable)
      setMeasurable]
  apply ENNReal.tsumCongr
  intro index
  exact ((measures index).map_apply function measurable setMeasurable).symm

public theorem restrict_sum (measures : Nat → Measure source)
    {region : Set α} (regionMeasurable : source.Measurable region) :
    (sum measures).restrict region =
      sum (fun index => (measures index).restrict region) := by
  apply Measure.ext
  intro set setMeasurable
  have interMeasurable := source.inter setMeasurable regionMeasurable
  rw [(sum measures).restrict_apply region setMeasurable,
    sum_apply measures interMeasurable,
    sum_apply (fun index => (measures index).restrict region)
      setMeasurable]
  apply ENNReal.tsumCongr
  intro index
  exact ((measures index).restrict_apply region setMeasurable).symm

public theorem restrict_iUnion (measure : Measure source)
    (regions : Nat → Set α)
    (measurable : ∀ index, source.Measurable (regions index))
    (pairwise : Set.PairwiseDisjoint regions) :
    measure.restrict (Set.iUnion regions) =
      sum (fun index => measure.restrict (regions index)) := by
  apply Measure.ext
  intro set setMeasurable
  have intersectionsMeasurable : ∀ index,
      source.Measurable (Set.inter set (regions index)) :=
    fun index => source.inter setMeasurable (measurable index)
  have intersectionsPairwise : Set.PairwiseDisjoint
      (fun index => Set.inter set (regions index)) := by
    intro first second different value firstMember secondMember
    exact pairwise first second different firstMember.2 secondMember.2
  rw [measure.restrict_apply (Set.iUnion regions) setMeasurable,
    Set.inter_iUnion,
    measure.iUnion_disjoint
      (fun index => Set.inter set (regions index))
      intersectionsMeasurable intersectionsPairwise,
    sum_apply (fun index => measure.restrict (regions index))
      setMeasurable]
  apply ENNReal.tsumCongr
  intro index
  exact (measure.restrict_apply (regions index) setMeasurable).symm

/-- A countable sum of identical measures equals scaling by positive infinity. -/
public theorem sum_const (measure : Measure source) :
    sum (fun _ : Nat => measure) = smul ENNReal.top measure := by
  classical
  apply Measure.ext
  intro set measurable
  rw [sum_apply _ measurable, smul_apply_measurable _ _ measurable]
  by_cases zero : measure set = ENNReal.zero
  · rw [zero, ENNReal.mulZero, ENNReal.tsumZero]
  · rw [ENNReal.tsumConstOfNeZero zero, ENNReal.topMulOfNeZero zero]

end Measure

end Foundations.Measure
