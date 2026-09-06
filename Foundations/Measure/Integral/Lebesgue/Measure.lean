module

public import Foundations.Measure.Integral.Lebesgue.Basic
public import Foundations.Measure.Additive.Sum
import Foundations.Measure.Integral.Simple.Algebra
import Foundations.Measure.Integral.Simple.Integral.Algebra
import Foundations.Measure.Integral.Simple.Integral.Measure

set_option autoImplicit false

/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl

Adapted from Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.
-/

namespace Foundations.Measure

open Foundations.Real

universe u

variable {alpha : Type u} {space : Space alpha}

public theorem lintegral_mono_measure (function : alpha → ENNReal)
    (left right : Measure space)
    (included : ∀ set, space.Measurable set →
      ENNReal.le (left set) (right set)) :
    ENNReal.le (lintegral left function) (lintegral right function) := by
  apply lintegral_le
  intro simple simpleBelow
  exact ENNReal.leTrans
    (simple.integral_mono_measure included)
    (simple.integral_le_lintegral right simpleBelow)

@[simp] public theorem lintegral_zero_measure
    (function : alpha → ENNReal) :
    lintegral (Measure.zero space) function = ENNReal.zero := by
  apply ENNReal.leAntisymm
  · apply lintegral_le
    intro simple _
    rw [simple.integral_zero_measure]
    exact ENNReal.leRefl _
  · exact ENNReal.zeroLe _

@[simp] public theorem lintegral_add_measure
    (function : alpha → ENNReal) (left right : Measure space) :
    lintegral (Measure.add left right) function =
      ENNReal.add (lintegral left function) (lintegral right function) := by
  apply ENNReal.leAntisymm
  · apply lintegral_le
    intro simple simpleBelow
    rw [simple.integral_add_measure]
    exact ENNReal.addLeAdd
      (simple.integral_le_lintegral left simpleBelow)
      (simple.integral_le_lintegral right simpleBelow)
  · unfold lintegral
    let leftCandidates : ENNReal → Prop := fun value =>
      ∃ lower : SimpleFunction space,
        SimpleFunction.PointwiseLe lower function ∧
        value = lower.integral left
    let rightCandidates : ENNReal → Prop := fun value =>
      ∃ lower : SimpleFunction space,
        SimpleFunction.PointwiseLe lower function ∧
        value = lower.integral right
    let sumCandidates : ENNReal → Prop := fun value =>
      ∃ lower : SimpleFunction space,
        SimpleFunction.PointwiseLe lower function ∧
        value = lower.integral (Measure.add left right)
    change ENNReal.le
      (ENNReal.add (ENNReal.supremum leftCandidates)
        (ENNReal.supremum rightCandidates))
      (ENNReal.supremum sumCandidates)
    have leftNonempty : ∃ value, leftCandidates value :=
      ⟨(SimpleFunction.zero space).integral left,
        SimpleFunction.zero space,
        fun input => by
          rw [SimpleFunction.zero_apply]
          exact ENNReal.zeroLe (function input), rfl⟩
    have rightNonempty : ∃ value, rightCandidates value :=
      ⟨(SimpleFunction.zero space).integral right,
        SimpleFunction.zero space,
        fun input => by
          rw [SimpleFunction.zero_apply]
          exact ENNReal.zeroLe (function input), rfl⟩
    rw [ENNReal.addSupremum (ENNReal.supremum leftCandidates)
      rightNonempty]
    apply ENNReal.supremumLe
    rintro _ ⟨rightValue, rightMember, rfl⟩
    rw [ENNReal.addComm,
      ENNReal.addSupremum rightValue leftNonempty]
    apply ENNReal.supremumLe
    rintro _ ⟨leftValue, leftMember, rfl⟩
    rcases leftMember with ⟨leftSimple, leftBelow, rfl⟩
    rcases rightMember with ⟨rightSimple, rightBelow, rfl⟩
    let joined := SimpleFunction.sup leftSimple rightSimple
    have joinedBelow : SimpleFunction.PointwiseLe joined function :=
      SimpleFunction.sup_le leftBelow rightBelow
    have combinedBound := ENNReal.addLeAdd
      (SimpleFunction.integral_mono_function
        (SimpleFunction.le_sup_left leftSimple rightSimple) left)
      (SimpleFunction.integral_mono_function
        (SimpleFunction.le_sup_right leftSimple rightSimple) right)
    rw [← joined.integral_add_measure left right] at combinedBound
    rw [ENNReal.addComm (leftSimple.integral left)
      (rightSimple.integral right)] at combinedBound
    exact ENNReal.leTrans combinedBound
      (ENNReal.leSupremum ⟨joined, joinedBelow, rfl⟩)

/-- Scaling a measure by an extended nonnegative scalar scales the Lebesgue integral by that factor. -/
public theorem lintegral_smul_measure (function : alpha → ENNReal)
    (factor : ENNReal) (measure : Measure space) :
    lintegral (Measure.smul factor measure) function =
      ENNReal.mul factor (lintegral measure function) := by
  apply ENNReal.leAntisymm
  · apply lintegral_le
    intro simple below
    rw [simple.integral_smul_measure]
    exact ENNReal.mulLeMul (ENNReal.leRefl factor) (simple.integral_le_lintegral measure below)
  · rw [lintegral, ENNReal.mulSupremum]
    apply ENNReal.supremumLe
    rintro _ ⟨_, ⟨simple, below, rfl⟩, rfl⟩
    rw [← simple.integral_smul_measure]
    exact simple.integral_le_lintegral _ below

private def measurePartialSum (measures : Nat → Measure space) :
    Nat → Measure space
  | 0 => Measure.zero space
  | count + 1 => Measure.add (measurePartialSum measures count)
      (measures count)

private theorem measurePartialSum_apply (measures : Nat → Measure space)
    (count : Nat) {set : Set alpha} (setMeasurable : space.Measurable set) :
    measurePartialSum measures count set =
      ENNReal.partialSum (fun index => measures index set) count := by
  induction count with
  | zero =>
      rw [measurePartialSum, Measure.zero_apply]
      rfl
  | succ count induction =>
      rw [measurePartialSum,
        Measure.add_apply_measurable _ _ setMeasurable,
        induction, ENNReal.partialSum]

private theorem lintegral_measurePartialSum
    (measures : Nat → Measure space) (function : alpha → ENNReal)
    (count : Nat) :
    lintegral (measurePartialSum measures count) function =
      ENNReal.partialSum
        (fun index => lintegral (measures index) function) count := by
  induction count with
  | zero => rw [measurePartialSum, lintegral_zero_measure,
      ENNReal.partialSum]
  | succ count induction =>
      rw [measurePartialSum, lintegral_add_measure, induction,
        ENNReal.partialSum]

private theorem measurePartialSum_le_sum
    (measures : Nat → Measure space) (count : Nat)
    (set : Set alpha) (setMeasurable : space.Measurable set) :
    ENNReal.le (measurePartialSum measures count set)
      (Measure.sum measures set) := by
  rw [measurePartialSum_apply measures count setMeasurable,
    Measure.sum_apply measures setMeasurable]
  exact ENNReal.partialSumLeTsum (fun index => measures index set) count

@[simp] public theorem lintegral_sum_measure
    (function : alpha → ENNReal) (measures : Nat → Measure space) :
    lintegral (Measure.sum measures) function =
      ENNReal.tsum (fun index => lintegral (measures index) function) := by
  apply ENNReal.leAntisymm
  · apply lintegral_le
    intro simple simpleBelow
    rw [simple.integral_sum_measure]
    apply ENNReal.tsumLeTsum
    intro index
    exact simple.integral_le_lintegral (measures index) simpleBelow
  · apply ENNReal.tsumLe
    intro count
    rw [← lintegral_measurePartialSum measures function count]
    exact lintegral_mono_measure function
      (measurePartialSum measures count) (Measure.sum measures)
      (measurePartialSum_le_sum measures count)

/-- Countable additivity in the measure argument, with the measure family
first for APIs that build measures compositionally. -/
public theorem lintegral_sum (measures : Nat → Measure space)
    (function : alpha → ENNReal) :
    lintegral (Measure.sum measures) function =
      ENNReal.tsum (fun index => lintegral (measures index) function) :=
  lintegral_sum_measure function measures

end Foundations.Measure
