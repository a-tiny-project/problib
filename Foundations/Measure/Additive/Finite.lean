module

public import Foundations.Measure.Additive.Map
public import Foundations.Measure.Additive.Restrict
public import Foundations.Measure.Additive.Dirac
import Foundations.Measure.Additive.Partition

set_option autoImplicit false

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Adapted from Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean and
Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny uses explicit proposition-valued certificates instead of typeclasses.
-/

namespace Foundations.Measure

open Foundations.Real

universe u v

namespace Measure

variable {alpha : Type u} {space : Space alpha}

/-- A certificate that the total mass is finite. -/
public structure IsFinite (measure : Measure space) : Prop where
  univFinite : ENNReal.Finite (measure Set.univ)

/-- A certificate that the total mass is one. -/
public structure IsProbability (measure : Measure space) : Prop where
  univ_eq_one : measure Set.univ = ENNReal.one

namespace IsFinite

/-- Every set has finite measure under a finite measure. -/
public theorem apply {measure : Measure space} (finite : IsFinite measure) (set : Set alpha) :
    ENNReal.Finite (measure set) :=
  ENNReal.finiteOfLe (measure.mono (Set.subset_univ set)) finite.univFinite

public theorem of_le {measure : Measure space} (finite : IsFinite measure)
    {other : Measure space}
    (included : ENNReal.le (other Set.univ) (measure Set.univ)) :
    IsFinite other :=
  ⟨ENNReal.finiteOfLe included finite.univFinite⟩

public theorem zero (space : Space alpha) : IsFinite (Measure.zero space) := by
  constructor
  rw [Measure.zero_apply]
  exact True.intro

public theorem add {left right : Measure space}
    (leftFinite : IsFinite left) (rightFinite : IsFinite right) :
    IsFinite (Measure.add left right) := by
  constructor
  rw [Measure.add_apply_measurable left right space.univ]
  exact ENNReal.addFinite leftFinite.univFinite rightFinite.univFinite

public theorem smul {measure : Measure space} (factor : ENNReal)
    (factorFinite : ENNReal.Finite factor) (finite : IsFinite measure) :
    IsFinite (Measure.smul factor measure) := by
  constructor
  rw [Measure.smul_apply_measurable factor measure space.univ]
  exact ENNReal.mulFinite factorFinite finite.univFinite

public theorem map {beta : Type v} {target : Space beta}
    {measure : Measure space} (finite : IsFinite measure)
    (function : alpha → beta)
    (measurable : MeasurableMap space target function) :
    IsFinite (measure.map function measurable) := by
  constructor
  rw [measure.map_apply function measurable target.univ,
    Set.preimage_univ]
  exact finite.univFinite

public theorem restrict {measure : Measure space}
    (finite : IsFinite measure) (region : Set alpha) :
    IsFinite (measure.restrict region) := by
  constructor
  rw [measure.restrict_apply_univ]
  exact ENNReal.finiteOfLe (measure.mono (Set.subset_univ region))
    finite.univFinite

public theorem dirac (space : Space alpha) (point : alpha) :
    IsFinite (Measure.dirac space point) := by
  constructor
  rw [Measure.dirac_apply_univ]
  exact True.intro

end IsFinite

/-- Cancel a finite left summand in an equality of measure sums. -/
public theorem add_left_cancel_of_finite {factor left right : Measure space}
    (factorFinite : IsFinite factor)
    (equal : Measure.add factor left = Measure.add factor right) : left = right := by
  apply Measure.ext
  intro set measurable
  have same := congrArg (fun measure : Measure space => measure set) equal
  rw [Measure.add_apply_measurable _ _ measurable,
    Measure.add_apply_measurable _ _ measurable] at same
  exact ENNReal.addLeftCancelOfFinite (factorFinite.apply set) same

/-- Cancel a finite right summand in an equality of measure sums. -/
public theorem add_right_cancel_of_finite {factor left right : Measure space}
    (factorFinite : IsFinite factor)
    (equal : Measure.add left factor = Measure.add right factor) : left = right := by
  apply add_left_cancel_of_finite factorFinite
  rw [Measure.add_comm factor left, Measure.add_comm factor right]
  exact equal

namespace IsProbability

/-- Any space carrying a probability measure is inhabited; empty carriers have total mass zero. -/
public theorem nonempty {measure : Measure space}
    (probability : IsProbability measure) : Nonempty alpha := by
  classical
  apply Classical.byContradiction
  intro empty
  have same : (Set.univ : Set alpha) = Set.empty := by
    apply Set.ext
    intro input
    exact False.elim (empty ⟨input⟩)
  have total := probability.univ_eq_one
  rw [same, measure.empty_apply] at total
  exact ENNReal.oneNeZero total.symm

/-- Every set under a probability measure has measure bounded by one. -/
public theorem apply_le_one {measure : Measure space}
    (probability : IsProbability measure) (set : Set alpha) :
    ENNReal.le (measure set) ENNReal.one := by
  rw [← probability.univ_eq_one]
  exact measure.mono (Set.subset_univ set)

/-- Two probability measures on discrete `Bool` that agree on `{true}` are equal. -/
public theorem bool_ext {left right : Measure (Space.discrete Bool)}
    (leftProbability : IsProbability left) (rightProbability : IsProbability right)
    (sameTrue : left (Set.singleton true) = right (Set.singleton true)) : left = right := by
  classical
  have leftSum := left.add_complement (Space.discrete_measurable (Set.singleton true))
  have rightSum := right.add_complement (Space.discrete_measurable (Set.singleton true))
  rw [leftProbability.univ_eq_one] at leftSum
  rw [rightProbability.univ_eq_one, ← sameTrue] at rightSum
  have finiteTrue : ENNReal.Finite (left (Set.singleton true)) := by
    apply ENNReal.finiteOfLe (left.mono (Set.subset_univ _))
    rw [leftProbability.univ_eq_one]
    exact True.intro
  have sameComplement := ENNReal.addLeftCancelOfFinite finiteTrue (leftSum.trans rightSum.symm)
  have complement : Set.complement (Set.singleton true) = Set.singleton false := by
    apply Set.ext
    intro value
    cases value <;> simp [Set.complement, Set.singleton]
  rw [complement] at sameComplement
  apply Measure.ext
  intro set _
  by_cases includeTrue : set true
  · by_cases includeFalse : set false
    · have equal : set = Set.univ := by
        apply Set.ext
        intro value
        cases value <;> simp [Set.univ, includeTrue, includeFalse]
      rw [equal, leftProbability.univ_eq_one, rightProbability.univ_eq_one]
    · have equal : set = Set.singleton true := by
        apply Set.ext
        intro value
        cases value <;> simp [Set.singleton, includeTrue, includeFalse]
      rw [equal, sameTrue]
  · by_cases includeFalse : set false
    · have equal : set = Set.singleton false := by
        apply Set.ext
        intro value
        cases value <;> simp [Set.singleton, includeTrue, includeFalse]
      rw [equal, sameComplement]
    · have equal : set = Set.empty := by
        apply Set.ext
        intro value
        cases value <;> simp [Set.empty, includeTrue, includeFalse]
      rw [equal, left.empty_apply, right.empty_apply]

/-- Every probability measure is a finite measure with total mass one. -/
public theorem toFinite {measure : Measure space}
    (probability : IsProbability measure) : IsFinite measure := by
  constructor
  rw [probability.univ_eq_one]
  exact True.intro

/-- Pushforward along a measurable map preserves probability measures. -/
public theorem map {beta : Type v} {target : Space beta}
    {measure : Measure space} (probability : IsProbability measure)
    (function : alpha → beta)
    (measurable : MeasurableMap space target function) :
    IsProbability (measure.map function measurable) := by
  constructor
  rw [measure.map_apply function measurable target.univ,
    Set.preimage_univ, probability.univ_eq_one]

/-- Restricting a measure to a region of mass one produces a probability measure. -/
public theorem restrict {measure : Measure space} (region : Set alpha)
    (regionFull : measure region = ENNReal.one) :
    IsProbability (measure.restrict region) := by
  constructor
  rw [measure.restrict_apply_univ, regionFull]

/-- The Dirac measure at any point is a probability measure. -/
public theorem dirac (space : Space alpha) (point : alpha) :
    IsProbability (Measure.dirac space point) := by
  constructor
  rw [Measure.dirac_apply_univ]

end IsProbability

end Measure

end Foundations.Measure
