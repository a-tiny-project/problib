module

public import Problib.Measure.Extended.Order

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

namespace Problib.Measure

open Problib.Real

universe u

namespace ENNRealMeasurable

variable {α : Type u} {source : Space α}
  {function left right : α → ENNReal}

private theorem lt_add_finite_left_iff {factor value threshold : ENNReal}
    (factorFinite : ENNReal.Finite factor)
    (factorThreshold : ENNReal.le factor threshold) :
    ENNReal.lt threshold (ENNReal.add factor value) ↔
      ENNReal.lt (ENNReal.sub threshold factor) value := by
  constructor
  · intro less
    have differenceValue : ENNReal.le
        (ENNReal.sub threshold factor) value :=
      ENNReal.sub_le_iff_le_add.mpr (by
        rw [ENNReal.add_comm]
        exact less.left)
    refine ⟨differenceValue, ?_⟩
    intro valueDifference
    have shifted := ENNReal.add_le_add_right valueDifference factor
    rw [ENNReal.sub_add_cancel factorThreshold] at shifted
    rw [ENNReal.add_comm] at shifted
    exact less.right shifted
  · intro less
    have thresholdSum : ENNReal.le threshold
        (ENNReal.add factor value) := by
      have shifted := ENNReal.add_le_add_right less.left factor
      rw [ENNReal.sub_add_cancel factorThreshold] at shifted
      rw [ENNReal.add_comm] at shifted
      exact shifted
    refine ⟨thresholdSum, ?_⟩
    intro sumThreshold
    apply less.right
    apply (ENNReal.le_sub_iff_add_le_of_finite_right
      factorFinite factorThreshold).mpr
    rw [ENNReal.add_comm]
    exact sumThreshold

public theorem const_add (factor : ENNReal)
    (measurable : ENNRealMeasurable source function) :
    ENNRealMeasurable source
      (fun value => ENNReal.add factor (function value)) := by
  by_cases factorTop : factor = ENNReal.top
  · have equal : (fun value : α => ENNReal.add factor (function value)) =
        (fun _ => ENNReal.top) := by
      funext value
      rw [factorTop, ENNReal.top_add]
    rw [equal]
    exact constant source ENNReal.top
  · have factorFinite : ENNReal.Finite factor :=
      ENNReal.finite_iff_ne_top.mpr factorTop
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
            have shifted := ENNReal.add_le_add_left
              (ENNReal.zero_le (function value)) factor
            rw [ENNReal.add_zero] at shifted
            exact shifted
          exact ⟨ENNReal.le_trans thresholdFactor.left factorSum,
            fun sumThreshold => thresholdFactor.right
              (ENNReal.le_trans factorSum sumThreshold)⟩
      rw [equal]
      exact source.univ
    · have factorThreshold : ENNReal.le factor threshold := by
        rcases ENNReal.le_total factor threshold with included | reverse
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
        exact lt_add_finite_left_iff factorFinite factorThreshold
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
    exact ENNReal.add_comm _ _
  rw [equal]
  exact result

private theorem add_approximation_left
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
        exact ENNReal.zero_add _
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
    add_approximation_left leftMeasurable rightMeasurable
  have supremumMeasurable := iSup approximations
  have equal : (fun value : α => ENNReal.add (left value) (right value)) =
      (fun value => ENNReal.iSup (fun index =>
        ENNReal.add (ENNReal.approximation (left value) index)
          (right value))) := by
    funext value
    calc
      ENNReal.add (left value) (right value) =
          ENNReal.add (right value) (left value) := ENNReal.add_comm _ _
      _ = ENNReal.add (right value)
          (ENNReal.iSup (ENNReal.approximation (left value))) := by
        rw [ENNReal.iSup_approximation]
      _ = ENNReal.iSup (fun index => ENNReal.add (right value)
          (ENNReal.approximation (left value) index)) :=
        ENNReal.add_iSup _ _
      _ = ENNReal.iSup (fun index => ENNReal.add
          (ENNReal.approximation (left value) index) (right value)) := by
        apply congrArg ENNReal.iSup
        funext index
        exact ENNReal.add_comm _ _
  rw [equal]
  exact supremumMeasurable

private noncomputable def divideThreshold
    (threshold : ENNReal) (factor : NNReal) : ENNReal :=
  match threshold with
  | .finite value => .finite (NNReal.div value factor)
  | .top => ENNReal.top

private theorem mul_le_iff_le_divideThreshold {factor : NNReal}
    (factorPositive : NNReal.lt NNReal.zero factor)
    (value threshold : ENNReal) :
    ENNReal.le (ENNReal.mul (ENNReal.finite factor) value) threshold ↔
      ENNReal.le value (divideThreshold threshold factor) := by
  have factorNonzero := (NNReal.zero_lt_iff_ne_zero factor).mp factorPositive
  cases threshold with
  | top => exact ⟨fun _ => ENNReal.le_top _, fun _ => ENNReal.le_top _⟩
  | finite thresholdValue =>
      cases value with
      | top =>
          unfold divideThreshold
          rw [ENNReal.finite_mul_top_of_ne_zero factorNonzero]
          exact ⟨False.elim, False.elim⟩
      | finite valueValue =>
          unfold divideThreshold
          rw [ENNReal.finite_mul_finite]
          constructor
          · intro included
            apply NNReal.le_of_mul_le_mul_left factorPositive
            rw [NNReal.mul_div_cancel thresholdValue factorNonzero]
            exact included
          · intro included
            have scaled := NNReal.mul_le_mul_left included factor
            rw [NNReal.mul_div_cancel thresholdValue factorNonzero] at scaled
            exact scaled

private theorem lt_finite_mul_iff {factor : NNReal}
    (factorPositive : NNReal.lt NNReal.zero factor)
    (threshold value : ENNReal) :
    ENNReal.lt threshold (ENNReal.mul (ENNReal.finite factor) value) ↔
      ENNReal.lt (divideThreshold threshold factor) value := by
  constructor
  · intro less
    have notValueDivide : ¬ENNReal.le value
        (divideThreshold threshold factor) := by
      intro included
      exact less.right ((mul_le_iff_le_divideThreshold factorPositive _ _).mpr
        included)
    exact ⟨Or.resolve_left
        (ENNReal.le_total value (divideThreshold threshold factor))
        notValueDivide,
      notValueDivide⟩
  · intro less
    have notProductThreshold : ¬ENNReal.le
        (ENNReal.mul (ENNReal.finite factor) value) threshold := by
      intro included
      exact less.right ((mul_le_iff_le_divideThreshold factorPositive _ _).mp
        included)
    exact ⟨Or.resolve_left
        (ENNReal.le_total
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
            ENNReal.zero_lt_iff_ne_zero.mp positiveValue
          rw [ENNReal.top_mul_of_ne_zero nonzero]
          unfold ennrealIndicator ennrealPiecewise
          simp [positiveValue]
        · have zeroValue : function value = ENNReal.zero := by
            apply Classical.byContradiction
            intro nonzero
            exact positiveValue (ENNReal.zero_lt_iff_ne_zero.mpr nonzero)
          rw [zeroValue, ENNReal.mul_zero]
          unfold ennrealIndicator ennrealPiecewise
          simp [positiveValue]
      rw [equal]
      exact branchMeasurable
  | finite factor =>
      rcases NNReal.eq_zero_or_zero_lt factor with factorZero | factorPositive
      · subst factor
        have equal : (fun value : α => ENNReal.mul
            (ENNReal.finite NNReal.zero) (function value)) =
            (fun _ => ENNReal.zero) := by
          funext value
          exact ENNReal.zero_mul _
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
          exact lt_finite_mul_iff factorPositive threshold (function value)
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
    exact ENNReal.mul_comm _ _
  rw [equal]
  exact result

end ENNRealMeasurable

end Problib.Measure
