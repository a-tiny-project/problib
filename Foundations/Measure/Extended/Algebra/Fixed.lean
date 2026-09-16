module

public import Foundations.Measure.Extended.Order

set_option autoImplicit false

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov

Adapted from Mathlib/MeasureTheory/Constructions/BorelSpace/Real.lean at
commit 15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny proves binary measurability from its canonical finite rational
approximations. Multiplication follows the convention zero times top is zero.
-/

namespace Foundations.Measure

open Foundations.Real

universe u

namespace ENNRealMeasurable

variable {α : Type u} {source : Space α}
  {function left right : α → ENNReal}

private theorem ltAddFiniteLeftIff {factor value threshold : ENNReal}
    (factorFinite : ENNReal.Finite factor)
    (factorThreshold : ENNReal.le factor threshold) :
    ENNReal.lt threshold (ENNReal.add factor value) ↔
      ENNReal.lt (ENNReal.sub threshold factor) value := by
  constructor
  · intro less
    have differenceValue : ENNReal.le
        (ENNReal.sub threshold factor) value :=
      ENNReal.subLeIffLeAdd.mpr (by
        rw [ENNReal.addComm]
        exact less.left)
    refine ⟨differenceValue, ?_⟩
    intro valueDifference
    have shifted := ENNReal.addLeAddRight valueDifference factor
    rw [ENNReal.subAddCancel factorThreshold] at shifted
    rw [ENNReal.addComm] at shifted
    exact less.right shifted
  · intro less
    have thresholdSum : ENNReal.le threshold
        (ENNReal.add factor value) := by
      have shifted := ENNReal.addLeAddRight less.left factor
      rw [ENNReal.subAddCancel factorThreshold] at shifted
      rw [ENNReal.addComm] at shifted
      exact shifted
    refine ⟨thresholdSum, ?_⟩
    intro sumThreshold
    apply less.right
    apply (ENNReal.leSubIffAddLeOfFiniteRight
      factorFinite factorThreshold).mpr
    rw [ENNReal.addComm]
    exact sumThreshold

public theorem const_add (factor : ENNReal)
    (measurable : ENNRealMeasurable source function) :
    ENNRealMeasurable source
      (fun value => ENNReal.add factor (function value)) := by
  by_cases factorTop : factor = ENNReal.top
  · have equal : (fun value : α => ENNReal.add factor (function value)) =
        (fun _ => ENNReal.top) := by
      funext value
      rw [factorTop, ENNReal.topAdd]
    rw [equal]
    exact constant source ENNReal.top
  · have factorFinite : ENNReal.Finite factor :=
      ENNReal.finiteIffNeTop.mpr factorTop
    intro threshold
    by_cases thresholdFactor : ENNReal.lt threshold factor
    · have equal : Set.preimage
          (fun value => ENNReal.add factor (function value))
            (ennrealIoi threshold) = Set.univ := by
        apply Set.ext
        intro value
        constructor
        · intro _
          exact True.intro
        · intro _
          have factorSum : ENNReal.le factor
              (ENNReal.add factor (function value)) := by
            have shifted := ENNReal.addLeAddLeft
              (ENNReal.zeroLe (function value)) factor
            rw [ENNReal.addZero] at shifted
            exact shifted
          exact ⟨ENNReal.leTrans thresholdFactor.left factorSum,
            fun sumThreshold => thresholdFactor.right
              (ENNReal.leTrans factorSum sumThreshold)⟩
      rw [equal]
      exact source.univ
    · have factorThreshold : ENNReal.le factor threshold := by
        rcases ENNReal.leTotal factor threshold with included | reverse
        · exact included
        · apply Classical.byContradiction
          intro notIncluded
          exact thresholdFactor ⟨reverse, notIncluded⟩
      have rayMeasurable := measurable (ENNReal.sub threshold factor)
      have equal : Set.preimage
          (fun value => ENNReal.add factor (function value))
            (ennrealIoi threshold) =
          Set.preimage function
            (ennrealIoi (ENNReal.sub threshold factor)) := by
        apply Set.ext
        intro value
        exact ltAddFiniteLeftIff factorFinite factorThreshold
      rw [equal]
      exact rayMeasurable

public theorem add_const
    (measurable : ENNRealMeasurable source function) (factor : ENNReal) :
    ENNRealMeasurable source
      (fun value => ENNReal.add (function value) factor) := by
  have result := const_add factor measurable
  have equal : (fun value : α => ENNReal.add (function value) factor) =
      (fun value => ENNReal.add factor (function value)) := by
    funext value
    exact ENNReal.addComm _ _
  rw [equal]
  exact result

private theorem addApproximationLeft
    (leftMeasurable : ENNRealMeasurable source left)
    (rightMeasurable : ENNRealMeasurable source right) (index : Nat) :
    ENNRealMeasurable source (fun value =>
      ENNReal.add (ENNReal.approximation (left value) index)
        (right value)) := by
  induction index with
  | zero =>
      have equal : (fun value : α =>
          ENNReal.add (ENNReal.approximation (left value) 0)
            (right value)) = right := by
        funext value
        exact ENNReal.zeroAdd _
      rw [equal]
      exact rightMeasurable
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
      have basisBranch := const_add (ENNReal.rationalBasis index)
        rightMeasurable
      have inner := piecewise dominatesMeasurable basisBranch induction
      have outer := piecewise includedMeasurable inner induction
      have equal : (fun value : α =>
          ENNReal.add (ENNReal.approximation (left value) (index + 1))
            (right value)) =
          ennrealPiecewise included
            (ennrealPiecewise dominates
              (fun value => ENNReal.add (ENNReal.rationalBasis index)
                (right value))
              (fun value => ENNReal.add
                (ENNReal.approximation (left value) index) (right value)))
            (fun value => ENNReal.add
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

public theorem add
    (leftMeasurable : ENNRealMeasurable source left)
    (rightMeasurable : ENNRealMeasurable source right) :
    ENNRealMeasurable source
      (fun value => ENNReal.add (left value) (right value)) := by
  have approximations : ∀ index, ENNRealMeasurable source (fun value =>
      ENNReal.add (ENNReal.approximation (left value) index)
        (right value)) :=
    addApproximationLeft leftMeasurable rightMeasurable
  have supremumMeasurable := iSup approximations
  have equal : (fun value : α => ENNReal.add (left value) (right value)) =
      (fun value => ENNReal.iSup (fun index =>
        ENNReal.add (ENNReal.approximation (left value) index)
          (right value))) := by
    funext value
    calc
      ENNReal.add (left value) (right value) =
          ENNReal.add (right value) (left value) := ENNReal.addComm _ _
      _ = ENNReal.add (right value)
          (ENNReal.iSup (ENNReal.approximation (left value))) := by
        rw [ENNReal.iSupApproximation]
      _ = ENNReal.iSup (fun index => ENNReal.add (right value)
          (ENNReal.approximation (left value) index)) :=
        ENNReal.addISup _ _
      _ = ENNReal.iSup (fun index => ENNReal.add
          (ENNReal.approximation (left value) index) (right value)) := by
        apply congrArg ENNReal.iSup
        funext index
        exact ENNReal.addComm _ _
  rw [equal]
  exact supremumMeasurable

private noncomputable def divideThreshold
    (threshold : ENNReal) (factor : NNReal) : ENNReal :=
  match threshold with
  | .finite value => .finite (NNReal.div value factor)
  | .top => ENNReal.top

private theorem mulLeIffLeDivideThreshold {factor : NNReal}
    (factorPositive : NNReal.lt NNReal.zero factor)
    (value threshold : ENNReal) :
    ENNReal.le (ENNReal.mul (ENNReal.finite factor) value) threshold ↔
      ENNReal.le value (divideThreshold threshold factor) := by
  have factorNonzero := (NNReal.zeroLtIffNeZero factor).mp factorPositive
  cases threshold with
  | top => exact ⟨fun _ => ENNReal.leTop _, fun _ => ENNReal.leTop _⟩
  | finite thresholdValue =>
      cases value with
      | top =>
          unfold divideThreshold
          rw [ENNReal.finiteMulTopOfNeZero factorNonzero]
          exact ⟨False.elim, False.elim⟩
      | finite valueValue =>
          unfold divideThreshold
          rw [ENNReal.finiteMulFinite]
          constructor
          · intro included
            apply NNReal.leOfMulLeMulLeft factorPositive
            rw [NNReal.mulDivCancel thresholdValue factorNonzero]
            exact included
          · intro included
            have scaled := NNReal.mulLeMulLeft included factor
            rw [NNReal.mulDivCancel thresholdValue factorNonzero] at scaled
            exact scaled

private theorem ltFiniteMulIff {factor : NNReal}
    (factorPositive : NNReal.lt NNReal.zero factor)
    (threshold value : ENNReal) :
    ENNReal.lt threshold (ENNReal.mul (ENNReal.finite factor) value) ↔
      ENNReal.lt (divideThreshold threshold factor) value := by
  constructor
  · intro less
    have notValueDivide : ¬ENNReal.le value
        (divideThreshold threshold factor) := by
      intro included
      exact less.right ((mulLeIffLeDivideThreshold factorPositive _ _).mpr
        included)
    exact ⟨Or.resolve_left
        (ENNReal.leTotal value (divideThreshold threshold factor))
        notValueDivide,
      notValueDivide⟩
  · intro less
    have notProductThreshold : ¬ENNReal.le
        (ENNReal.mul (ENNReal.finite factor) value) threshold := by
      intro included
      exact less.right ((mulLeIffLeDivideThreshold factorPositive _ _).mp
        included)
    exact ⟨Or.resolve_left
        (ENNReal.leTotal
          (ENNReal.mul (ENNReal.finite factor) value) threshold)
        notProductThreshold,
      notProductThreshold⟩

public theorem const_mul (factor : ENNReal)
    (measurable : ENNRealMeasurable source function) :
    ENNRealMeasurable source
      (fun value => ENNReal.mul factor (function value)) := by
  cases factor with
  | top =>
      let positive : Set α := Set.preimage function
        (ennrealIoi ENNReal.zero)
      have positiveMeasurable : source.Measurable positive :=
        measurable ENNReal.zero
      have branchMeasurable := indicator positiveMeasurable
        (constant source ENNReal.top)
      have equal : (fun value : α => ENNReal.mul ENNReal.top
          (function value)) =
          ennrealIndicator positive (fun _ => ENNReal.top) := by
        classical
        funext value
        by_cases positiveValue : positive value
        · have nonzero : function value ≠ ENNReal.zero :=
            ENNReal.zeroLtIffNeZero.mp positiveValue
          rw [ENNReal.topMulOfNeZero nonzero]
          unfold ennrealIndicator ennrealPiecewise
          simp [positiveValue]
        · have zeroValue : function value = ENNReal.zero := by
            apply Classical.byContradiction
            intro nonzero
            exact positiveValue (ENNReal.zeroLtIffNeZero.mpr nonzero)
          rw [zeroValue, ENNReal.mulZero]
          unfold ennrealIndicator ennrealPiecewise
          simp [positiveValue]
      rw [equal]
      exact branchMeasurable
  | finite factor =>
      rcases NNReal.eqZeroOrZeroLt factor with factorZero | factorPositive
      · subst factor
        have equal : (fun value : α => ENNReal.mul
            (ENNReal.finite NNReal.zero) (function value)) =
            (fun _ => ENNReal.zero) := by
          funext value
          exact ENNReal.zeroMul _
        rw [equal]
        exact constant source ENNReal.zero
      · intro threshold
        have rayMeasurable := measurable
          (divideThreshold threshold factor)
        have equal : Set.preimage
            (fun value => ENNReal.mul (ENNReal.finite factor)
              (function value)) (ennrealIoi threshold) =
            Set.preimage function
              (ennrealIoi (divideThreshold threshold factor)) := by
          apply Set.ext
          intro value
          exact ltFiniteMulIff factorPositive threshold (function value)
        rw [equal]
        exact rayMeasurable

public theorem mul_const
    (measurable : ENNRealMeasurable source function) (factor : ENNReal) :
    ENNRealMeasurable source
      (fun value => ENNReal.mul (function value) factor) := by
  have result := const_mul factor measurable
  have equal : (fun value : α => ENNReal.mul (function value) factor) =
      (fun value => ENNReal.mul factor (function value)) := by
    funext value
    exact ENNReal.mulComm _ _
  rw [equal]
  exact result

end ENNRealMeasurable

end Foundations.Measure
