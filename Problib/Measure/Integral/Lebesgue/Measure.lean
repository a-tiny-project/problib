module

public import Problib.Measure.Integral.Lebesgue.Basic
public import Problib.Measure.Additive.Sum
public import Problib.Measure.Additive.Supremum
import Problib.Measure.Integral.Simple.Algebra
import Problib.Measure.Integral.Simple.Integral.Algebra
import Problib.Measure.Integral.Simple.Integral.Measure

set_option autoImplicit false

/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl

Adapted from Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.
-/

namespace Problib.Measure

open Problib.Real

universe u

variable {alpha : Type u} {space : Space alpha}

public theorem lintegral_mono_measure (function : alpha → ENNReal)
    (left right : Measure space)
    (included : ∀ set, space.Measurable set →
      ENNReal.le (left set) (right set)) :
    ENNReal.le (lintegral left function) (lintegral right function) := by
  apply lintegral_le
  intro simple simpleBelow
  exact ENNReal.le_trans
    (simple.integral_mono_measure included)
    (simple.integral_le_lintegral right simpleBelow)

/-- The integral of a fixed function is continuous in an increasing measure chain. -/
public theorem lintegral_iSupIncreasing_measure (function : alpha → ENNReal)
    (measures : Nat → Measure space)
    (increasing : ∀ index set, space.Measurable set →
      ENNReal.le (measures index set) (measures (index + 1) set)) :
    lintegral (Measure.iSupIncreasing measures increasing) function =
      ENNReal.iSup (fun index => lintegral (measures index) function) := by
  have simple_limit (simple : SimpleFunction space) :
      simple.integral (Measure.iSupIncreasing measures increasing) =
        ENNReal.iSup (fun index => simple.integral (measures index)) := by
    calc
      simple.integral (Measure.iSupIncreasing measures increasing) =
          SimpleFunction.finiteSum (simple.values.map fun value =>
            ENNReal.mul value
              (ENNReal.iSup (fun index => measures index (simple.fiber value)))) := by
        unfold SimpleFunction.integral
        apply congrArg SimpleFunction.finiteSum
        apply List.map_congr_left
        intro value _
        rw [Measure.iSupIncreasing_apply_measurable measures increasing
          (simple.fiber_measurable value)]
      _ = SimpleFunction.finiteSum (simple.values.map fun value =>
          ENNReal.iSup (fun index =>
            ENNReal.mul value (measures index (simple.fiber value)))) := by
        apply congrArg SimpleFunction.finiteSum
        apply List.map_congr_left
        intro value _
        exact ENNReal.mul_iSup value _
      _ = ENNReal.iSup (fun index => simple.integral (measures index)) :=
        SimpleFunction.finiteSum_map_iSup simple.values
          (fun index value => ENNReal.mul value (measures index (simple.fiber value)))
          (fun index value => ENNReal.mul_le_mul_left
            (increasing index (simple.fiber value) (simple.fiber_measurable value)) value)
  apply ENNReal.le_antisymm
  · apply lintegral_le
    intro simple below
    rw [simple_limit simple]
    exact ENNReal.iSup_le fun index =>
      ENNReal.le_trans (simple.integral_le_lintegral (measures index) below)
        (ENNReal.le_iSup (fun stage => lintegral (measures stage) function) index)
  · apply ENNReal.iSup_le
    intro index
    apply lintegral_mono_measure function
    intro set measurable
    rw [Measure.iSupIncreasing_apply_measurable measures increasing measurable]
    exact ENNReal.le_iSup (fun stage => measures stage set) index

@[simp] public theorem lintegral_zero_measure
    (function : alpha → ENNReal) :
    lintegral (Measure.zero space) function = ENNReal.zero := by
  apply ENNReal.le_antisymm
  · apply lintegral_le
    intro simple _
    rw [simple.integral_zero_measure]
    exact ENNReal.le_refl _
  · exact ENNReal.zero_le _

@[simp] public theorem lintegral_add_measure
    (function : alpha → ENNReal) (left right : Measure space) :
    lintegral (Measure.add left right) function =
      ENNReal.add (lintegral left function) (lintegral right function) := by
  apply ENNReal.le_antisymm
  · apply lintegral_le
    intro simple simpleBelow
    rw [simple.integral_add_measure]
    exact ENNReal.add_le_add
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
          exact ENNReal.zero_le (function input), rfl⟩
    have rightNonempty : ∃ value, rightCandidates value :=
      ⟨(SimpleFunction.zero space).integral right,
        SimpleFunction.zero space,
        fun input => by
          rw [SimpleFunction.zero_apply]
          exact ENNReal.zero_le (function input), rfl⟩
    rw [ENNReal.add_supremum (ENNReal.supremum leftCandidates)
      rightNonempty]
    apply ENNReal.supremum_le
    rintro _ ⟨rightValue, rightMember, rfl⟩
    rw [ENNReal.add_comm,
      ENNReal.add_supremum rightValue leftNonempty]
    apply ENNReal.supremum_le
    rintro _ ⟨leftValue, leftMember, rfl⟩
    rcases leftMember with ⟨leftSimple, leftBelow, rfl⟩
    rcases rightMember with ⟨rightSimple, rightBelow, rfl⟩
    let joined := SimpleFunction.sup leftSimple rightSimple
    have joinedBelow : SimpleFunction.PointwiseLe joined function :=
      SimpleFunction.sup_le leftBelow rightBelow
    have combinedBound := ENNReal.add_le_add
      (SimpleFunction.integral_mono
        (SimpleFunction.le_sup_left leftSimple rightSimple) left)
      (SimpleFunction.integral_mono
        (SimpleFunction.le_sup_right leftSimple rightSimple) right)
    rw [← joined.integral_add_measure left right] at combinedBound
    rw [ENNReal.add_comm (leftSimple.integral left)
      (rightSimple.integral right)] at combinedBound
    exact ENNReal.le_trans combinedBound
      (ENNReal.le_supremum ⟨joined, joinedBelow, rfl⟩)

/-- Scaling a measure by an extended nonnegative scalar scales the Lebesgue integral by that factor. -/
public theorem lintegral_smul_measure (function : alpha → ENNReal)
    (factor : ENNReal) (measure : Measure space) :
    lintegral (Measure.smul factor measure) function =
      ENNReal.mul factor (lintegral measure function) := by
  apply ENNReal.le_antisymm
  · apply lintegral_le
    intro simple below
    rw [simple.integral_smul_measure]
    exact ENNReal.mul_le_mul (ENNReal.le_refl factor) (simple.integral_le_lintegral measure below)
  · rw [lintegral, ENNReal.mul_supremum]
    apply ENNReal.supremum_le
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
  exact ENNReal.partialSum_le_tsum (fun index => measures index set) count

@[simp] public theorem lintegral_sum_measure
    (function : alpha → ENNReal) (measures : Nat → Measure space) :
    lintegral (Measure.sum measures) function =
      ENNReal.tsum (fun index => lintegral (measures index) function) := by
  apply ENNReal.le_antisymm
  · apply lintegral_le
    intro simple simpleBelow
    rw [simple.integral_sum_measure]
    apply ENNReal.tsum_le_tsum
    intro index
    exact simple.integral_le_lintegral (measures index) simpleBelow
  · apply ENNReal.tsum_le
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

open SimpleFunction (finiteSum)

namespace Measure

/-- The finite sum of a list of measures. -/
@[expose] public noncomputable def listSum : List (Measure space) → Measure space
  | [] => zero space
  | measure :: measures => add measure (listSum measures)

public theorem listSum_apply (measures : List (Measure space)) {set : Set alpha}
    (setMeasurable : space.Measurable set) :
    listSum measures set = finiteSum (measures.map fun measure => measure set) := by
  induction measures with
  | nil => exact zero_apply set
  | cons measure measures induction =>
      rw [listSum, add_apply_measurable _ _ setMeasurable, induction]
      rfl

end Measure

/-- Integration against a finite sum of measures is the finite sum of the
integrals. -/
public theorem lintegral_listSum (measures : List (Measure space)) (function : alpha → ENNReal) :
    lintegral (Measure.listSum measures) function =
      finiteSum (measures.map fun measure => lintegral measure function) := by
  induction measures with
  | nil => exact lintegral_zero_measure function
  | cons measure measures induction =>
      rw [Measure.listSum, lintegral_add_measure, induction]
      rfl

end Problib.Measure
