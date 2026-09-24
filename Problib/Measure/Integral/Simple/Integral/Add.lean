module

public import Problib.Measure.Integral.Simple.Integral.Algebra
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

universe u

namespace SimpleFunction

variable {alpha : Type u} {source : Space alpha}

private def valuePairs (left right : List ENNReal) :
    List (ENNReal × ENNReal) :=
  left.flatMap fun leftValue =>
    right.map fun rightValue => (leftValue, rightValue)

private theorem valuePairs_nodup (left right : List ENNReal)
    (leftNodup : left.Nodup) (rightNodup : right.Nodup) :
    (valuePairs left right).Nodup := by
  unfold valuePairs List.Nodup
  rw [List.pairwise_flatMap]
  constructor
  · intro leftValue _
    rw [List.pairwise_map]
    apply rightNodup.imp
    intro first second different equal
    exact different (congrArg Prod.snd equal)
  · apply leftNodup.imp
    intro first second different firstPair firstMember secondPair secondMember
      equal
    rcases List.mem_map.mp firstMember with ⟨firstRight, _, rfl⟩
    rcases List.mem_map.mp secondMember with ⟨secondRight, _, rfl⟩
    exact different (congrArg Prod.fst equal)

/-- Simple integration is additive in the integrand. -/
public theorem add_integral (left right : SimpleFunction source)
    (measure : Measure source) :
    integral (add left right) measure =
      ENNReal.add (integral left measure) (integral right measure) := by
  let mass := fun leftValue rightValue =>
    measure (Set.inter (left.fiber leftValue) (right.fiber rightValue))
  have pairPartition : integral (add left right) measure =
      finiteSum (left.values.map fun leftValue =>
        finiteSum (right.values.map fun rightValue =>
          ENNReal.mul (ENNReal.add leftValue rightValue)
            (mass leftValue rightValue))) := by
    have partition := integral_eq_partition (add left right) measure
      (valuePairs left.values right.values)
      (valuePairs_nodup left.values right.values
        left.values_nodup right.values_nodup)
      (fun pair => Set.inter (left.fiber pair.1) (right.fiber pair.2))
      (fun pair => ENNReal.add pair.1 pair.2)
      (by
        intro pair _
        exact source.inter (left.fiber_measurable pair.1)
          (right.fiber_measurable pair.2))
      (by
        intro first _ second _ different input firstMember secondMember
        have firstEqual : first.1 = second.1 :=
          ((left.mem_fiber_iff first.1 input).mp firstMember.1).symm.trans
            ((left.mem_fiber_iff second.1 input).mp secondMember.1)
        have secondEqual : first.2 = second.2 :=
          ((right.mem_fiber_iff first.2 input).mp firstMember.2).symm.trans
            ((right.mem_fiber_iff second.2 input).mp secondMember.2)
        exact different (Prod.ext firstEqual secondEqual))
      (by
        intro input
        refine ⟨(left input, right input), ?_, rfl, rfl⟩
        unfold valuePairs
        exact List.mem_flatMap.mpr
          ⟨left input, left.value_mem_values input,
            List.mem_map.mpr
              ⟨right input, right.value_mem_values input, rfl⟩⟩)
      (by
        intro pair _ input member
        rw [add_apply,
          (left.mem_fiber_iff pair.1 input).mp member.1,
          (right.mem_fiber_iff pair.2 input).mp member.2])
    rw [partition]
    unfold valuePairs
    rw [List.map_flatMap]
    simp only [List.map_map]
    exact finiteSum_flatMap left.values (fun _ => right.values)
      (fun leftValue rightValue =>
        ENNReal.mul (ENNReal.add leftValue rightValue)
          (mass leftValue rightValue))
  have leftExpansion : integral left measure =
      finiteSum (left.values.map fun leftValue =>
        finiteSum (right.values.map fun rightValue =>
          ENNReal.mul leftValue (mass leftValue rightValue))) := by
    unfold integral
    apply congrArg finiteSum
    apply List.map_congr_left
    intro leftValue _
    rw [measure_fiber_split measure (left.fiber leftValue)
      (left.fiber_measurable leftValue) right]
    exact (finiteSum_map_mul_left right.values leftValue
      (mass leftValue)).symm
  have interSwap (leftValue rightValue : ENNReal) :
      Set.inter (right.fiber rightValue) (left.fiber leftValue) =
        Set.inter (left.fiber leftValue) (right.fiber rightValue) :=
    Set.inter_comm _ _
  have rightExpansion : integral right measure =
      finiteSum (left.values.map fun leftValue =>
        finiteSum (right.values.map fun rightValue =>
          ENNReal.mul rightValue (mass leftValue rightValue))) := by
    calc
      integral right measure =
          finiteSum (right.values.map fun rightValue =>
            finiteSum (left.values.map fun leftValue =>
              ENNReal.mul rightValue (mass leftValue rightValue))) := by
        unfold integral
        apply congrArg finiteSum
        apply List.map_congr_left
        intro rightValue _
        rw [measure_fiber_split measure (right.fiber rightValue)
          (right.fiber_measurable rightValue) left]
        apply Eq.trans _ (finiteSum_map_mul_left left.values rightValue
          (fun leftValue => mass leftValue rightValue)).symm
        apply congrArg (ENNReal.mul rightValue)
        apply congrArg finiteSum
        apply List.map_congr_left
        intro leftValue _
        rw [interSwap]
      _ = finiteSum (left.values.map fun leftValue =>
          finiteSum (right.values.map fun rightValue =>
            ENNReal.mul rightValue (mass leftValue rightValue))) :=
        finiteSum_comm right.values left.values
          (fun rightValue leftValue =>
            ENNReal.mul rightValue (mass leftValue rightValue))
  have splitTerm (leftValue rightValue : ENNReal) :
      ENNReal.mul (ENNReal.add leftValue rightValue)
          (mass leftValue rightValue) =
        ENNReal.add
          (ENNReal.mul leftValue (mass leftValue rightValue))
          (ENNReal.mul rightValue (mass leftValue rightValue)) := by
    calc
      ENNReal.mul (ENNReal.add leftValue rightValue)
          (mass leftValue rightValue) =
          ENNReal.mul (mass leftValue rightValue)
            (ENNReal.add leftValue rightValue) := ENNReal.mul_comm _ _
      _ = ENNReal.add
          (ENNReal.mul (mass leftValue rightValue) leftValue)
          (ENNReal.mul (mass leftValue rightValue) rightValue) :=
        ENNReal.mul_add _ _ _
      _ = ENNReal.add
          (ENNReal.mul leftValue (mass leftValue rightValue))
          (ENNReal.mul rightValue (mass leftValue rightValue)) := by
        rw [ENNReal.mul_comm (mass leftValue rightValue) leftValue,
          ENNReal.mul_comm (mass leftValue rightValue) rightValue]
  rw [pairPartition]
  calc
    finiteSum (left.values.map fun leftValue =>
        finiteSum (right.values.map fun rightValue =>
          ENNReal.mul (ENNReal.add leftValue rightValue)
            (mass leftValue rightValue))) =
        finiteSum (left.values.map fun leftValue =>
          finiteSum (right.values.map fun rightValue =>
            ENNReal.add
              (ENNReal.mul leftValue (mass leftValue rightValue))
              (ENNReal.mul rightValue (mass leftValue rightValue)))) := by
      apply congrArg finiteSum
      apply List.map_congr_left
      intro leftValue _
      apply congrArg finiteSum
      apply List.map_congr_left
      intro rightValue _
      exact splitTerm leftValue rightValue
    _ = finiteSum (left.values.map fun leftValue =>
        ENNReal.add
          (finiteSum (right.values.map fun rightValue =>
            ENNReal.mul leftValue (mass leftValue rightValue)))
          (finiteSum (right.values.map fun rightValue =>
            ENNReal.mul rightValue (mass leftValue rightValue)))) := by
      apply congrArg finiteSum
      apply List.map_congr_left
      intro leftValue _
      exact finiteSum_map_add right.values
        (fun rightValue =>
          ENNReal.mul leftValue (mass leftValue rightValue))
        (fun rightValue =>
          ENNReal.mul rightValue (mass leftValue rightValue))
    _ = ENNReal.add
        (finiteSum (left.values.map fun leftValue =>
          finiteSum (right.values.map fun rightValue =>
            ENNReal.mul leftValue (mass leftValue rightValue))))
        (finiteSum (left.values.map fun leftValue =>
          finiteSum (right.values.map fun rightValue =>
            ENNReal.mul rightValue (mass leftValue rightValue)))) :=
      finiteSum_map_add left.values
        (fun leftValue => finiteSum (right.values.map fun rightValue =>
          ENNReal.mul leftValue (mass leftValue rightValue)))
        (fun leftValue => finiteSum (right.values.map fun rightValue =>
          ENNReal.mul rightValue (mass leftValue rightValue)))
    _ = ENNReal.add (integral left measure) (integral right measure) := by
      rw [← leftExpansion, ← rightExpansion]

end SimpleFunction

end Problib.Measure
