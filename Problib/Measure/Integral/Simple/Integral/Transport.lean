module

public import Problib.Measure.Additive.Dirac
public import Problib.Measure.Additive.Map
public import Problib.Measure.Integral.Simple.Integral.Partition

set_option autoImplicit false

/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl

Adapted from Mathlib/MeasureTheory/Function/SimpleFunc.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.
-/

namespace Problib.Measure

open Problib.Real

universe u v

namespace SimpleFunction

variable {alpha : Type u} {source : Space alpha}

/-- Integration against a pushforward equals integration after
precomposition. -/
public theorem integral_map {beta : Type v} {target : Space beta}
    (function : SimpleFunction target) (measure : Measure source)
    (before : alpha → beta)
    (beforeMeasurable : MeasurableMap source target before) :
    integral function (measure.map before beforeMeasurable) =
      integral (comp function before beforeMeasurable) measure := by
  let pieces := fun value => Set.preimage before (function.fiber value)
  calc
    integral function (measure.map before beforeMeasurable) =
        finiteSum (function.values.map fun value =>
          ENNReal.mul value (measure (pieces value))) := by
      rw [integral_eq_finiteSum]
      apply congrArg finiteSum
      apply List.map_congr_left
      intro value _
      rw [Measure.map_apply measure before beforeMeasurable
        (function.fiber_measurable value)]
    _ = integral (comp function before beforeMeasurable) measure := by
      apply (integral_eq_partition
        (comp function before beforeMeasurable) measure
        function.values function.values_nodup pieces (fun value => value)
        (fun value _ => beforeMeasurable
          (function.fiber_measurable value))
        ?_ ?_ ?_).symm
      · intro first _ second _ different input
          firstMember secondMember
        exact function.levelSet_disjoint different
          firstMember secondMember
      · intro input
        exact ⟨function (before input),
          function.value_mem_values (before input), rfl⟩
      · intro value _ input member
        rw [comp_apply]
        exact member

/-- Integration against a Dirac measure evaluates the simple function at
the mass point. -/
public theorem integral_dirac (function : SimpleFunction source)
    (point : alpha) :
    integral function (Measure.dirac source point) = function point := by
  let terms := fun value => ENNReal.mul value
    ((Measure.dirac source point) (function.fiber value))
  rw [integral_eq_finiteSum]
  change finiteSum (function.values.map terms) = function point
  rw [finiteSum_eq_unique function.values (function point)
    function.values_nodup (function.value_mem_values point) terms]
  · unfold terms
    rw [Measure.dirac_apply source point
      (function.fiber_measurable (function point)),
      if_pos (show function.fiber (function point) point from rfl),
      ENNReal.mul_one]
  · intro value _ different
    unfold terms
    rw [Measure.dirac_apply source point
      (function.fiber_measurable value)]
    have notMember : ¬function.fiber value point := by
      intro member
      exact different member.symm
    rw [if_neg notMember, ENNReal.mul_zero]

end SimpleFunction

end Problib.Measure
