module

public import Foundations.Measure.Integral.Simple.Approximation

set_option autoImplicit false

/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl

Adapted from Mathlib/MeasureTheory/Function/SimpleFunc.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny states every closure premise explicitly and reconstructs through the
canonical rational simple approximations.
-/

namespace Foundations.Measure

open Foundations.Real

universe u

namespace ENNRealMeasurable

variable {alpha : Type u} {source : Space alpha}

/-- Prove a property of every measurable extended-nonnegative function from
zero, measurable constant indicators, addition, and increasing suprema. -/
public theorem induction {motive : (alpha → ENNReal) → Prop}
    (zeroCase : motive (fun _ => ENNReal.zero))
    (indicatorCase : ∀ (region : Set alpha),
      source.Measurable region → ∀ value : ENNReal,
      motive (ennrealIndicator region (fun _ => value)))
    (addCase : ∀ {left right : alpha → ENNReal},
      ENNRealMeasurable source left →
      ENNRealMeasurable source right →
      motive left → motive right →
      motive (fun input => ENNReal.add (left input) (right input)))
    (iSupCase : ∀ {functions : Nat → alpha → ENNReal},
      (∀ index, ENNRealMeasurable source (functions index)) →
      (∀ input index,
        ENNReal.le (functions index input) (functions (index + 1) input)) →
      (∀ index, motive (functions index)) →
      motive (fun input => ENNReal.iSup
        (fun index => functions index input)))
    {function : alpha → ENNReal}
    (functionMeasurable : ENNRealMeasurable source function) :
    motive function := by
  let simpleMotive : SimpleFunction source → Prop :=
    fun simple => motive simple
  have simpleZero : simpleMotive (SimpleFunction.zero source) := by
    unfold simpleMotive
    have equal : (SimpleFunction.zero source).toFunction =
        (fun _ => ENNReal.zero) := by
      funext input
      exact SimpleFunction.zero_apply source input
    rw [equal]
    exact zeroCase
  have simpleIndicator : ∀ (region : Set alpha)
      (regionMeasurable : source.Measurable region) (value : ENNReal),
      simpleMotive
        (SimpleFunction.indicator region regionMeasurable value) := by
    intro region regionMeasurable value
    unfold simpleMotive
    have equal :
        (SimpleFunction.indicator region regionMeasurable value).toFunction =
        ennrealIndicator region (fun _ => value) := by
      funext input
      exact SimpleFunction.indicator_apply
        region regionMeasurable value input
    rw [equal]
    exact indicatorCase region regionMeasurable value
  have simpleAdd : ∀ left right : SimpleFunction source,
      simpleMotive left → simpleMotive right →
      simpleMotive (SimpleFunction.add left right) := by
    intro left right leftMotive rightMotive
    unfold simpleMotive at leftMotive rightMotive ⊢
    have equal : (SimpleFunction.add left right).toFunction =
        (fun input => ENNReal.add (left input) (right input)) := by
      funext input
      exact SimpleFunction.add_apply left right input
    rw [equal]
    exact addCase left.measurable right.measurable leftMotive rightMotive
  let approximations : Nat → SimpleFunction source :=
    fun index => SimpleFunction.approximation
      function functionMeasurable index
  have approximationMotive : ∀ index,
      motive (approximations index) := by
    intro index
    exact SimpleFunction.induction
      (motive := simpleMotive) simpleZero simpleIndicator simpleAdd
      (approximations index)
  have supremumMotive : motive (fun input => ENNReal.iSup
      (fun index => approximations index input)) := by
    apply iSupCase
    · intro index
      exact (approximations index).measurable
    · intro input index
      exact SimpleFunction.approximation_mono
        function functionMeasurable index input
    · exact approximationMotive
  have equal : (fun input => ENNReal.iSup
      (fun index => approximations index input)) = function := by
    funext input
    exact SimpleFunction.iSup_approximation
      function functionMeasurable input
  rw [equal] at supremumMotive
  exact supremumMotive

end ENNRealMeasurable

end Foundations.Measure
