module

public import Foundations.Measure.Extended.Algebra.Fixed

set_option autoImplicit false

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov

Adapted from Mathlib/MeasureTheory/Constructions/BorelSpace/Real.lean at
commit 15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny lifts finite-section measurability through canonical rational
approximations. This avoids a product-topology dependency.
-/

namespace Foundations.Measure

open Foundations.Real

universe u

namespace ENNRealMeasurable

variable {α : Type u} {source : Space α}
  {function left right : α → ENNReal}

private theorem mulApproximationLeft
    (leftMeasurable : ENNRealMeasurable source left)
    (rightMeasurable : ENNRealMeasurable source right) (index : Nat) :
    ENNRealMeasurable source (fun value =>
      ENNReal.mul (ENNReal.approximation (left value) index)
        (right value)) := by
  induction index with
  | zero =>
      have equal : (fun value : α =>
          ENNReal.mul (ENNReal.approximation (left value) 0)
            (right value)) = (fun _ => ENNReal.zero) := by
        funext value
        exact ENNReal.zeroMul _
      rw [equal]
      exact constant source ENNReal.zero
  | succ index induction =>
      let included : Set α := fun value =>
        ENNReal.le (ENNReal.rationalBasis index) (left value)
      let dominates : Set α := fun value =>
        ENNReal.le (ENNReal.approximation (left value) index)
          (ENNReal.rationalBasis index)
      have includedMeasurable :=
        ici leftMeasurable (ENNReal.rationalBasis index)
      have dominatesMeasurable :=
        iic (approximation leftMeasurable index)
          (ENNReal.rationalBasis index)
      have basisBranch := const_mul (ENNReal.rationalBasis index)
        rightMeasurable
      have inner := piecewise dominatesMeasurable basisBranch induction
      have outer := piecewise includedMeasurable inner induction
      have equal : (fun value : α =>
          ENNReal.mul (ENNReal.approximation (left value) (index + 1))
            (right value)) =
          ennrealPiecewise included
            (ennrealPiecewise dominates
              (fun value => ENNReal.mul (ENNReal.rationalBasis index)
                (right value))
              (fun value => ENNReal.mul
                (ENNReal.approximation (left value) index) (right value)))
            (fun value => ENNReal.mul
              (ENNReal.approximation (left value) index) (right value)) := by
        classical
        funext value
        by_cases valueIncluded :
            ENNReal.le (ENNReal.rationalBasis index) (left value)
        · by_cases valueDominates : ENNReal.le
              (ENNReal.approximation (left value) index)
              (ENNReal.rationalBasis index)
          · simp [ENNReal.approximation, ennrealPiecewise, included,
              dominates, valueIncluded, valueDominates]
          · simp [ENNReal.approximation, ennrealPiecewise, included,
              dominates, valueIncluded, valueDominates]
        · simp [ENNReal.approximation, ennrealPiecewise, included,
            valueIncluded]
      rw [equal]
      exact outer

public theorem mul
    (leftMeasurable : ENNRealMeasurable source left)
    (rightMeasurable : ENNRealMeasurable source right) :
    ENNRealMeasurable source
      (fun value => ENNReal.mul (left value) (right value)) := by
  have approximations : ∀ index, ENNRealMeasurable source (fun value =>
      ENNReal.mul (ENNReal.approximation (left value) index)
        (right value)) :=
    mulApproximationLeft leftMeasurable rightMeasurable
  have supremumMeasurable := iSup approximations
  have equal : (fun value : α => ENNReal.mul (left value) (right value)) =
      (fun value => ENNReal.iSup (fun index =>
        ENNReal.mul (ENNReal.approximation (left value) index)
          (right value))) := by
    funext value
    calc
      ENNReal.mul (left value) (right value) =
          ENNReal.mul (right value) (left value) := ENNReal.mulComm _ _
      _ = ENNReal.mul (right value)
          (ENNReal.iSup (ENNReal.approximation (left value))) := by
        rw [ENNReal.iSupApproximation]
      _ = ENNReal.iSup (fun index => ENNReal.mul (right value)
          (ENNReal.approximation (left value) index)) :=
        ENNReal.mulISup _ _
      _ = ENNReal.iSup (fun index => ENNReal.mul
          (ENNReal.approximation (left value) index) (right value)) := by
        apply congrArg ENNReal.iSup
        funext index
        exact ENNReal.mulComm _ _
  rw [equal]
  exact supremumMeasurable

/-- Extended-nonnegative subtraction preserves measurability without finiteness
hypotheses. -/
public theorem sub
    (leftMeasurable : ENNRealMeasurable source left)
    (rightMeasurable : ENNRealMeasurable source right) :
    ENNRealMeasurable source (fun input => ENNReal.sub (left input) (right input)) := by
  intro threshold
  have comparison := ENNRealMeasurable.lt_set
    (ENNRealMeasurable.add (ENNRealMeasurable.constant source threshold) rightMeasurable)
    leftMeasurable
  have same : Set.preimage (fun input => ENNReal.sub (left input) (right input))
      (ennrealIoi threshold) =
      (fun input => ENNReal.lt (ENNReal.add threshold (right input)) (left input)) :=
    Set.ext fun _ => ENNReal.ltSubIffAddLt
  rw [same]
  exact comparison

public theorem min
    (leftMeasurable : ENNRealMeasurable source left)
    (rightMeasurable : ENNRealMeasurable source right) :
    ENNRealMeasurable source
      (fun value => ENNReal.min (left value) (right value)) := by
  let included : Set α := fun value =>
    ENNReal.le (left value) (right value)
  have includedMeasurable := le_set leftMeasurable rightMeasurable
  have selected := piecewise includedMeasurable
    leftMeasurable rightMeasurable
  have equal : (fun value : α => ENNReal.min (left value) (right value)) =
      ennrealPiecewise included left right := by
    classical
    funext value
    by_cases leftRight : ENNReal.le (left value) (right value)
    · rw [ENNReal.minEqLeft leftRight]
      simp [ennrealPiecewise, included, leftRight]
    · have rightLeft := Or.resolve_left
        (ENNReal.leTotal (left value) (right value)) leftRight
      rw [ENNReal.minEqRight rightLeft]
      simp [ennrealPiecewise, included, leftRight]
  rw [equal]
  exact selected

end ENNRealMeasurable

end Foundations.Measure
