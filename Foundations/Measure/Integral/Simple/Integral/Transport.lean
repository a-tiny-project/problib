module

public import Foundations.Measure.Additive.Dirac
public import Foundations.Measure.Additive.Map
public import Foundations.Measure.Integral.Simple.Integral.Partition

set_option autoImplicit false

/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl

Adapted from Mathlib/MeasureTheory/Function/SimpleFunc.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.
-/

namespace Foundations.Measure

open Foundations.Real

universe u v

namespace SimpleFunction

variable {alpha : Type u} {source : Space alpha}

private theorem finiteSum_map_eq_zero {Index : Type v}
    (indices : List Index) (values : Index → ENNReal)
    (zero : ∀ index, index ∈ indices →
      values index = ENNReal.zero) :
    finiteSum (indices.map values) = ENNReal.zero := by
  induction indices with
  | nil => rfl
  | cons index indices induction =>
      simp only [List.map, finiteSum, zero index List.mem_cons_self,
        induction (fun tailIndex tailMember =>
          zero tailIndex (List.mem_cons_of_mem index tailMember)),
        ENNReal.zeroAdd]

private theorem finiteSum_eq_unique {Index : Type v}
    (indices : List Index) (target : Index) (nodup : indices.Nodup)
    (targetMember : target ∈ indices) (values : Index → ENNReal)
    (zeroAway : ∀ index, index ∈ indices → index ≠ target →
      values index = ENNReal.zero) :
    finiteSum (indices.map values) = values target := by
  induction indices with
  | nil => exact False.elim (List.not_mem_nil targetMember)
  | cons index indices induction =>
      have indexNotTail := (List.nodup_cons.mp nodup).1
      have tailNodup := (List.nodup_cons.mp nodup).2
      rcases List.mem_cons.mp targetMember with equal | inTail
      · subst index
        have tailZero := finiteSum_map_eq_zero indices values
          (fun tailIndex tailMember => zeroAway tailIndex
            (List.mem_cons_of_mem target tailMember)
            (fun tailEqual => indexNotTail (tailEqual ▸ tailMember)))
        simp only [List.map, finiteSum, tailZero, ENNReal.addZero]
      · have different : index ≠ target := by
          intro equal
          exact indexNotTail (equal ▸ inTail)
        simp only [List.map, finiteSum,
          zeroAway index List.mem_cons_self different, ENNReal.zeroAdd]
        exact induction tailNodup inTail
          (fun tailIndex tailMember tailDifferent =>
            zeroAway tailIndex (List.mem_cons_of_mem index tailMember)
              tailDifferent)

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
      ENNReal.mulOne]
  · intro value _ different
    unfold terms
    rw [Measure.dirac_apply source point
      (function.fiber_measurable value)]
    have notMember : ¬function.fiber value point := by
      intro member
      exact different member.symm
    rw [if_neg notMember, ENNReal.mulZero]

end SimpleFunction

end Foundations.Measure
