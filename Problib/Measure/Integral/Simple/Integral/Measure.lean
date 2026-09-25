module

public import Problib.Measure.Additive.Sum
public import Problib.Measure.Integral.Simple.Integral.Basic

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

public theorem integral_zero_measure (function : SimpleFunction source) :
    integral function (Measure.zero source) = ENNReal.zero := by
  unfold integral
  have termsZero : function.values.map (fun value =>
      ENNReal.mul value ((Measure.zero source) (function.fiber value))) =
      function.values.map (fun _ => ENNReal.zero) := by
    apply List.map_congr_left
    intro value _
    rw [Measure.zero_apply, ENNReal.mul_zero]
  rw [termsZero]
  induction function.values with
  | nil => rfl
  | cons value values induction =>
      simp only [List.map, finiteSum, induction, ENNReal.zero_add]

public theorem integral_add_measure (function : SimpleFunction source)
    (left right : Measure source) :
    integral function (Measure.add left right) =
      ENNReal.add (integral function left) (integral function right) := by
  calc
    integral function (Measure.add left right) =
        finiteSum (function.values.map fun value =>
          ENNReal.add
            (ENNReal.mul value (left (function.fiber value)))
            (ENNReal.mul value (right (function.fiber value)))) := by
      unfold integral
      apply congrArg finiteSum
      apply List.map_congr_left
      intro value _
      rw [Measure.add_apply_measurable left right
        (function.fiber_measurable value), ENNReal.mul_add]
    _ = ENNReal.add
        (finiteSum (function.values.map fun value =>
          ENNReal.mul value (left (function.fiber value))))
        (finiteSum (function.values.map fun value =>
          ENNReal.mul value (right (function.fiber value)))) :=
      finiteSum_map_add function.values
        (fun value => ENNReal.mul value (left (function.fiber value)))
        (fun value => ENNReal.mul value (right (function.fiber value)))
    _ = ENNReal.add (integral function left) (integral function right) :=
      rfl

public theorem integral_smul_measure (function : SimpleFunction source)
    (factor : ENNReal) (measure : Measure source) :
    integral function (Measure.smul factor measure) =
      ENNReal.mul factor (integral function measure) := by
  calc
    integral function (Measure.smul factor measure) =
        finiteSum (function.values.map fun value =>
          ENNReal.mul factor
            (ENNReal.mul value (measure (function.fiber value)))) := by
      unfold integral
      apply congrArg finiteSum
      apply List.map_congr_left
      intro value _
      rw [Measure.smul_apply_measurable factor measure
        (function.fiber_measurable value)]
      calc
        ENNReal.mul value
            (ENNReal.mul factor (measure (function.fiber value))) =
          ENNReal.mul (ENNReal.mul value factor)
            (measure (function.fiber value)) :=
          (ENNReal.mul_assoc _ _ _).symm
        _ = ENNReal.mul (ENNReal.mul factor value)
            (measure (function.fiber value)) := by
          rw [ENNReal.mul_comm value factor]
        _ = ENNReal.mul factor
            (ENNReal.mul value (measure (function.fiber value))) :=
          ENNReal.mul_assoc _ _ _
    _ = ENNReal.mul factor
        (finiteSum (function.values.map fun value =>
          ENNReal.mul value (measure (function.fiber value)))) :=
      finiteSum_map_mul_left function.values factor
        (fun value => ENNReal.mul value (measure (function.fiber value)))
    _ = ENNReal.mul factor (integral function measure) := rfl

public theorem integral_mono_measure (function : SimpleFunction source)
    {left right : Measure source}
    (included : ∀ set, source.Measurable set →
      ENNReal.le (left set) (right set)) :
    ENNReal.le (integral function left) (integral function right) := by
  unfold integral
  apply finiteSum_map_mono
  intro value
  exact ENNReal.mul_le_mul_left
    (included (function.fiber value) (function.fiber_measurable value)) value

public theorem integral_sum_measure (function : SimpleFunction source)
    (measures : Nat → Measure source) :
    integral function (Measure.sum measures) =
      ENNReal.tsum (fun index => integral function (measures index)) := by
  calc
    integral function (Measure.sum measures) =
        finiteSum (function.values.map fun value =>
          ENNReal.tsum (fun index =>
            ENNReal.mul value
              (measures index (function.fiber value)))) := by
      unfold integral
      apply congrArg finiteSum
      apply List.map_congr_left
      intro value _
      rw [Measure.sum_apply measures (function.fiber_measurable value),
        ENNReal.tsum_mul_left]
    _ = ENNReal.tsum (fun index =>
        finiteSum (function.values.map fun value =>
          ENNReal.mul value
            (measures index (function.fiber value)))) :=
      finiteSum_map_tsum function.values fun index value =>
        ENNReal.mul value (measures index (function.fiber value))
    _ = ENNReal.tsum (fun index => integral function (measures index)) :=
      rfl

end SimpleFunction

end Problib.Measure
