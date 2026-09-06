module

public import Foundations.Measure.Integral.Lebesgue.Convergence
public import Foundations.Measure.Additive.Restrict
import Foundations.Measure.Extended.Limit
import Foundations.Measure.Integral.Simple.Integral.Add
import Foundations.Measure.Integral.Simple.Integral.Operations

set_option autoImplicit false

/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl

Adapted from Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean and
Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny derives algebraic laws from canonical finite-range approximations and
monotone convergence.
-/

namespace Foundations.Measure

open Foundations.Real

universe u

variable {alpha : Type u} {space : Space alpha}

public theorem lintegral_const (measure : Measure space) (value : ENNReal) :
    lintegral measure (fun _ : alpha => value) =
      ENNReal.mul value (measure Set.univ) := by
  let constant := SimpleFunction.constant space value
  calc
    lintegral measure (fun _ : alpha => value) =
        lintegral measure constant := by
      apply lintegral_congr
      intro input
      exact (SimpleFunction.constant_apply space value input).symm
    _ = constant.integral measure :=
      constant.lintegral_eq_integral measure
    _ = ENNReal.mul value (measure Set.univ) :=
      SimpleFunction.constant_integral space value measure

public theorem lintegral_zero (measure : Measure space) :
    lintegral measure (fun _ : alpha => ENNReal.zero) = ENNReal.zero := by
  rw [lintegral_const, ENNReal.zeroMul]

/-- Restricting an integrand to a measurable region is the same as restricting
the measure. The integrand itself need not be measurable. -/
public theorem lintegral_indicator (measure : Measure space)
    (region : Set alpha) (regionMeasurable : space.Measurable region)
    (function : alpha → ENNReal) :
    lintegral measure (ennrealIndicator region function) =
      lintegral (measure.restrict region) function := by
  apply ENNReal.leAntisymm
  · apply lintegral_le
    intro lower lowerBound
    let restricted := lower.restrict region regionMeasurable
    have lowerRestricted : ∀ input, lower input = restricted input := by
      intro input
      classical
      by_cases member : region input
      · rw [SimpleFunction.restrict_apply_of_mem lower region
          regionMeasurable input member]
      · have lowerZero : lower input = ENNReal.zero := by
          apply ENNReal.leAntisymm
          · have bound := lowerBound input
            simp [ennrealIndicator, ennrealPiecewise, member] at bound
            exact bound
          · exact ENNReal.zeroLe _
        rw [SimpleFunction.restrict_apply_of_not_mem lower region
          regionMeasurable input member, lowerZero]
    have restrictedBound : SimpleFunction.PointwiseLe restricted function := by
      intro input
      classical
      by_cases member : region input
      · rw [SimpleFunction.restrict_apply_of_mem lower region
          regionMeasurable input member]
        have bound := lowerBound input
        simpa [ennrealIndicator, ennrealPiecewise, member] using bound
      · rw [SimpleFunction.restrict_apply_of_not_mem lower region
          regionMeasurable input member]
        exact ENNReal.zeroLe _
    have lowerFunction : SimpleFunction.PointwiseLe lower function := by
      intro input
      rw [lowerRestricted input]
      exact restrictedBound input
    rw [SimpleFunction.integral_congr lowerRestricted measure,
      lower.integral_restrict region regionMeasurable measure]
    exact lower.integral_le_lintegral
      (measure.restrict region) lowerFunction
  · apply lintegral_le
    intro lower lowerBound
    let restricted := lower.restrict region regionMeasurable
    have restrictedBound : SimpleFunction.PointwiseLe restricted
        (ennrealIndicator region function) := by
      intro input
      classical
      by_cases member : region input
      · rw [SimpleFunction.restrict_apply_of_mem lower region
          regionMeasurable input member]
        have bound := lowerBound input
        simpa [ennrealIndicator, ennrealPiecewise, member] using bound
      · rw [SimpleFunction.restrict_apply_of_not_mem lower region
          regionMeasurable input member]
        simp [ennrealIndicator, ennrealPiecewise, member,
          ENNReal.leRefl]
    rw [← lower.integral_restrict region regionMeasurable measure]
    exact restricted.integral_le_lintegral measure restrictedBound

public theorem lintegral_add (measure : Measure space)
    {left right : alpha → ENNReal}
    (leftMeasurable : ENNRealMeasurable space left)
    (rightMeasurable : ENNRealMeasurable space right) :
    lintegral measure (fun input => ENNReal.add (left input) (right input)) =
      ENNReal.add (lintegral measure left) (lintegral measure right) := by
  let leftApproximation := fun index =>
    SimpleFunction.approximation left leftMeasurable index
  let rightApproximation := fun index =>
    SimpleFunction.approximation right rightMeasurable index
  let sums := fun index => SimpleFunction.add
    (leftApproximation index) (rightApproximation index)
  have pointwise : ∀ input,
      ENNReal.add (left input) (right input) =
        ENNReal.iSup (fun index => sums index input) := by
    intro input
    calc
      ENNReal.add (left input) (right input) =
          ENNReal.add
            (ENNReal.iSup (fun index => leftApproximation index input))
            (ENNReal.iSup (fun index => rightApproximation index input)) := by
        rw [SimpleFunction.iSup_approximation left leftMeasurable input,
          SimpleFunction.iSup_approximation right rightMeasurable input]
      _ = ENNReal.iSup (fun index => ENNReal.add
          (leftApproximation index input)
          (rightApproximation index input)) :=
        (ENNReal.iSupDiagonalAdd
          (fun index => leftApproximation index input)
          (fun index => rightApproximation index input)
          (fun index => SimpleFunction.approximation_mono left
            leftMeasurable index input)
          (fun index => SimpleFunction.approximation_mono right
            rightMeasurable index input)).symm
      _ = ENNReal.iSup (fun index => sums index input) := by
        apply congrArg ENNReal.iSup
        funext index
        exact (SimpleFunction.add_apply
          (leftApproximation index) (rightApproximation index) input).symm
  have sumsMeasurable : ∀ index, ENNRealMeasurable space (sums index) :=
    fun index => (sums index).measurable
  have sumsMonotone : ∀ stage input,
      ENNReal.le (sums stage input) (sums (stage + 1) input) := by
    intro stage input
    simp only [sums, SimpleFunction.add_apply]
    exact ENNReal.addLeAdd
      (SimpleFunction.approximation_mono left leftMeasurable stage input)
      (SimpleFunction.approximation_mono right rightMeasurable stage input)
  calc
    lintegral measure (fun input => ENNReal.add (left input) (right input)) =
        lintegral measure (fun input =>
          ENNReal.iSup (fun index => sums index input)) :=
      lintegral_congr measure pointwise
    _ = ENNReal.iSup (fun index => lintegral measure (sums index)) :=
      lintegral_iSup measure (fun index input => sums index input)
        sumsMeasurable sumsMonotone
    _ = ENNReal.iSup (fun index => ENNReal.add
        ((leftApproximation index).integral measure)
        ((rightApproximation index).integral measure)) := by
      apply congrArg ENNReal.iSup
      funext index
      rw [(sums index).lintegral_eq_integral measure]
      exact SimpleFunction.add_integral
        (leftApproximation index) (rightApproximation index) measure
    _ = ENNReal.add
        (ENNReal.iSup (fun index =>
          (leftApproximation index).integral measure))
        (ENNReal.iSup (fun index =>
          (rightApproximation index).integral measure)) :=
      ENNReal.iSupDiagonalAdd
        (fun index => (leftApproximation index).integral measure)
        (fun index => (rightApproximation index).integral measure)
        (fun index => SimpleFunction.integral_mono
          (SimpleFunction.approximation_mono left leftMeasurable index)
          measure)
        (fun index => SimpleFunction.integral_mono
          (SimpleFunction.approximation_mono right rightMeasurable index)
          measure)
    _ = ENNReal.add (lintegral measure left) (lintegral measure right) := by
      rw [← lintegral_eq_iSup_canonical measure leftMeasurable,
        ← lintegral_eq_iSup_canonical measure rightMeasurable]

public theorem lintegral_smul (measure : Measure space) (factor : ENNReal)
    {function : alpha → ENNReal}
    (functionMeasurable : ENNRealMeasurable space function) :
    lintegral measure (fun input => ENNReal.mul factor (function input)) =
      ENNReal.mul factor (lintegral measure function) := by
  let approximations := fun index =>
    SimpleFunction.approximation function functionMeasurable index
  let scaled := fun index => SimpleFunction.smul factor (approximations index)
  have pointwise : ∀ input,
      ENNReal.mul factor (function input) =
        ENNReal.iSup (fun index => scaled index input) := by
    intro input
    calc
      ENNReal.mul factor (function input) = ENNReal.mul factor
          (ENNReal.iSup (fun index => approximations index input)) := by
        rw [SimpleFunction.iSup_approximation function
          functionMeasurable input]
      _ = ENNReal.iSup (fun index => ENNReal.mul factor
          (approximations index input)) :=
        ENNReal.mulISup factor (fun index => approximations index input)
      _ = ENNReal.iSup (fun index => scaled index input) := by
        apply congrArg ENNReal.iSup
        funext index
        exact (SimpleFunction.smul_apply factor
          (approximations index) input).symm
  have scaledMeasurable : ∀ index,
      ENNRealMeasurable space (scaled index) :=
    fun index => (scaled index).measurable
  have scaledMonotone : ∀ stage input,
      ENNReal.le (scaled stage input) (scaled (stage + 1) input) := by
    intro stage input
    simp only [scaled, SimpleFunction.smul_apply]
    exact ENNReal.mulLeMulLeft
      (SimpleFunction.approximation_mono function functionMeasurable
        stage input) factor
  calc
    lintegral measure (fun input => ENNReal.mul factor (function input)) =
        lintegral measure (fun input =>
          ENNReal.iSup (fun index => scaled index input)) :=
      lintegral_congr measure pointwise
    _ = ENNReal.iSup (fun index => lintegral measure (scaled index)) :=
      lintegral_iSup measure (fun index input => scaled index input)
        scaledMeasurable scaledMonotone
    _ = ENNReal.iSup (fun index => ENNReal.mul factor
        ((approximations index).integral measure)) := by
      apply congrArg ENNReal.iSup
      funext index
      rw [(scaled index).lintegral_eq_integral measure]
      exact SimpleFunction.smul_integral factor
        (approximations index) measure
    _ = ENNReal.mul factor (ENNReal.iSup (fun index =>
        (approximations index).integral measure)) :=
      (ENNReal.mulISup factor (fun index =>
        (approximations index).integral measure)).symm
    _ = ENNReal.mul factor (lintegral measure function) := by
      rw [lintegral_eq_iSup_canonical measure functionMeasurable]

/-- A nonnegative integral exchanges with a pointwise countable sum of
measurable functions. -/
public theorem lintegral_tsum (measure : Measure space)
    (functions : Nat → alpha → ENNReal)
    (measurable : ∀ index,
      ENNRealMeasurable space (functions index)) :
    lintegral measure (fun input =>
      ENNReal.tsum (fun index => functions index input)) =
      ENNReal.tsum (fun index => lintegral measure (functions index)) := by
  let sums := fun count input =>
    ENNReal.partialSum (fun index => functions index input) count
  have sumsMeasurable : ∀ count, ENNRealMeasurable space (sums count) :=
    fun count => ENNRealMeasurable.partialSum measurable count
  have sumsMonotone : ∀ count input,
      ENNReal.le (sums count input) (sums (count + 1) input) :=
    fun count input => ENNReal.partialSumStep
      (fun index => functions index input) count
  have integralPartialSum : ∀ count,
      lintegral measure (sums count) =
        ENNReal.partialSum
          (fun index => lintegral measure (functions index)) count := by
    intro count
    induction count with
    | zero =>
        change lintegral measure (fun _ : alpha => ENNReal.zero) = ENNReal.zero
        exact lintegral_zero measure
    | succ count induction =>
        change lintegral measure (fun input => ENNReal.add
          (sums count input) (functions count input)) =
          ENNReal.add
            (ENNReal.partialSum
              (fun index => lintegral measure (functions index)) count)
            (lintegral measure (functions count))
        rw [lintegral_add measure (sumsMeasurable count) (measurable count),
          induction]
  change lintegral measure (fun input => ENNReal.iSup
      (fun count => sums count input)) =
    ENNReal.iSup (ENNReal.partialSum
      (fun index => lintegral measure (functions index)))
  calc
    lintegral measure (fun input => ENNReal.iSup
        (fun count => sums count input)) =
        ENNReal.iSup (fun count => lintegral measure (sums count)) :=
      lintegral_iSup measure sums sumsMeasurable sumsMonotone
    _ = ENNReal.iSup (ENNReal.partialSum
        (fun index => lintegral measure (functions index))) := by
      apply congrArg ENNReal.iSup
      funext count
      exact integralPartialSum count

/-- Integrating a measurable piecewise function splits into the sum of integrals over the region and its complement. -/
public theorem lintegral_piecewise (measure : Measure space) {region : Set alpha}
    (measurable : space.Measurable region) {inside outside : alpha → ENNReal}
    (insideMeasurable : ENNRealMeasurable space inside)
    (outsideMeasurable : ENNRealMeasurable space outside) :
    lintegral measure (ennrealPiecewise region inside outside) =
      ENNReal.add (lintegral (measure.restrict region) inside)
        (lintegral (measure.restrict (Set.complement region)) outside) := by
  have equal : ennrealPiecewise region inside outside =
      (fun value => ENNReal.add (ennrealIndicator region inside value)
        (ennrealIndicator (Set.complement region) outside value)) := by
    funext value
    classical
    by_cases member : region value
    · simp only [ennrealIndicator, ennrealPiecewise, Set.complement, member,
        if_true, not_true_eq_false, if_false, ENNReal.addZero]
    · simp only [ennrealIndicator, ennrealPiecewise, Set.complement, member,
        if_true, not_false_eq_true, if_false, ENNReal.zeroAdd]
  rw [equal, lintegral_add measure (ENNRealMeasurable.indicator measurable insideMeasurable)
    (ENNRealMeasurable.indicator (space.complement measurable) outsideMeasurable),
    lintegral_indicator measure region measurable inside,
    lintegral_indicator measure (Set.complement region) (space.complement measurable) outside]

end Foundations.Measure
