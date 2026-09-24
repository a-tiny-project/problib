module

public import Problib.Measure.Integral.Lebesgue.Basic
public import Problib.Measure.Integral.Simple.Approximation
import Problib.Measure.Additive.Continuity
import Problib.Measure.Additive.Restrict
import Problib.Measure.Integral.Simple.Integral.Convergence
import Problib.Measure.Integral.Simple.Integral.Operations

set_option autoImplicit false

/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl

Adapted from Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny uses a strict rational approximation to one in the direct proof of
monotone convergence.
-/

namespace Problib.Measure

open Problib.Real

universe u

private noncomputable def strictUnit : Nat → ENNReal
  | 0 => ENNReal.zero
  | index + 1 => by
      classical
      exact if below : ENNReal.lt (ENNReal.rationalBasis index) ENNReal.one then
        if dominates : ENNReal.le (strictUnit index)
            (ENNReal.rationalBasis index) then
          ENNReal.rationalBasis index
        else
          strictUnit index
      else
        strictUnit index

private theorem strictUnit_finite (index : Nat) :
    ENNReal.Finite (strictUnit index) := by
  induction index with
  | zero => exact True.intro
  | succ index induction =>
      rw [strictUnit]
      split
      · split
        · exact ENNReal.rationalBasis_finite index
        · exact induction
      · exact induction

private theorem strictUnit_step (index : Nat) :
    ENNReal.le (strictUnit index) (strictUnit (index + 1)) := by
  classical
  by_cases below :
      ENNReal.lt (ENNReal.rationalBasis index) ENNReal.one
  · by_cases dominates : ENNReal.le (strictUnit index)
        (ENNReal.rationalBasis index)
    · simpa only [strictUnit, dif_pos below, dif_pos dominates]
        using dominates
    · simp only [strictUnit, dif_pos below, dif_neg dominates]
      exact ENNReal.le_refl _
  · simp only [strictUnit, dif_neg below]
    exact ENNReal.le_refl _

private theorem strictUnit_lt_one (index : Nat) :
    ENNReal.lt (strictUnit index) ENNReal.one := by
  induction index with
  | zero => exact ENNReal.one_positive
  | succ index induction =>
      rw [strictUnit]
      split
      · rename_i below
        split
        · exact below
        · exact induction
      · exact induction

private theorem rationalBasis_le_strictUnit_next {index : Nat}
    (below : ENNReal.lt (ENNReal.rationalBasis index) ENNReal.one) :
    ENNReal.le (ENNReal.rationalBasis index) (strictUnit (index + 1)) := by
  classical
  simp only [strictUnit, dif_pos below]
  by_cases dominates : ENNReal.le (strictUnit index)
      (ENNReal.rationalBasis index)
  · rw [dif_pos dominates]
    exact ENNReal.le_refl _
  · rw [dif_neg dominates]
    rcases ENNReal.le_total (strictUnit index)
        (ENNReal.rationalBasis index) with forward | reverse
    · exact False.elim (dominates forward)
    · exact reverse

private theorem iSup_strictUnit :
    ENNReal.iSup strictUnit = ENNReal.one := by
  apply ENNReal.le_antisymm
  · apply ENNReal.iSup_le
    intro index
    exact (strictUnit_lt_one index).1
  · apply Classical.byContradiction
    intro notIncluded
    have strict : ENNReal.lt (ENNReal.iSup strictUnit) ENNReal.one :=
      ⟨ENNReal.iSup_le (fun index => (strictUnit_lt_one index).1),
        notIncluded⟩
    rcases ENNReal.exists_rationalBasis_between strict with
      ⟨index, supremumBasis, basisOne⟩
    have basisSupremum : ENNReal.le (ENNReal.rationalBasis index)
        (ENNReal.iSup strictUnit) :=
      ENNReal.le_trans (rationalBasis_le_strictUnit_next basisOne)
        (ENNReal.le_iSup strictUnit (index + 1))
    exact supremumBasis.2 basisSupremum

private theorem strictUnit_mul_lt {value : ENNReal}
    (valueFinite : ENNReal.Finite value) (valueNonzero : value ≠ ENNReal.zero)
    (index : Nat) :
    ENNReal.lt (ENNReal.mul (strictUnit index) value) value := by
  rcases ENNReal.exists_finite_of_finite (strictUnit_finite index) with
    ⟨factor, factorEqual⟩
  rcases ENNReal.exists_finite_of_finite valueFinite with
    ⟨underlying, valueEqual⟩
  rw [factorEqual, valueEqual, ENNReal.finite_mul_finite]
  change NNReal.lt (NNReal.mul factor underlying) underlying
  have factorStrict : NNReal.lt factor NNReal.one := by
    have strict := strictUnit_lt_one index
    rw [factorEqual] at strict
    change NNReal.lt factor NNReal.one at strict
    exact strict
  have underlyingNonzero : underlying ≠ NNReal.zero := by
    intro equal
    apply valueNonzero
    rw [valueEqual, equal]
    rfl
  have included : NNReal.le (NNReal.mul factor underlying) underlying := by
    have scaled := NNReal.mul_le_mul_right factorStrict.1 underlying
    simpa only [NNReal.one_mul] using scaled
  refine ⟨included, ?_⟩
  intro reverse
  have productsEqualUnderlying : NNReal.mul factor underlying = underlying :=
    NNReal.le_antisymm included reverse
  have productsEqual : NNReal.mul factor underlying =
      NNReal.mul NNReal.one underlying := by
    simpa only [NNReal.one_mul] using productsEqualUnderlying
  have factorEqualOne : factor = NNReal.one :=
    NNReal.mul_right_cancel underlyingNonzero productsEqual
  apply factorStrict.2
  rw [factorEqualOne]
  exact NNReal.le_refl _

private theorem iSup_strictUnit_mul (value : ENNReal) :
    ENNReal.iSup (fun index => ENNReal.mul (strictUnit index) value) = value := by
  calc
    ENNReal.iSup (fun index => ENNReal.mul (strictUnit index) value) =
        ENNReal.iSup (fun index => ENNReal.mul value (strictUnit index)) := by
      apply congrArg ENNReal.iSup
      funext index
      exact ENNReal.mul_comm _ _
    _ = ENNReal.mul value (ENNReal.iSup strictUnit) :=
      (ENNReal.mul_iSup value strictUnit).symm
    _ = value := by rw [iSup_strictUnit, ENNReal.mul_one]

private theorem scaled_integral_le_iSup
    {alpha : Type u} {space : Space alpha}
    (measure : Measure space) (functions : Nat → alpha → ENNReal)
    (measurable : ∀ index,
      ENNRealMeasurable space (functions index))
    (monotone : ∀ stage input,
      ENNReal.le (functions stage input) (functions (stage + 1) input))
    (simple : SimpleFunction space)
    (simpleFinite : ∀ input, ENNReal.Finite (simple input))
    (simpleBound : SimpleFunction.PointwiseLe simple (fun input =>
      ENNReal.iSup (fun index => functions index input)))
    (scaleIndex : Nat) :
    ENNReal.le
      ((SimpleFunction.smul (strictUnit scaleIndex) simple).integral measure)
      (ENNReal.iSup (fun index => lintegral measure (functions index))) := by
  let scaled := SimpleFunction.smul (strictUnit scaleIndex) simple
  let regions : Nat → Set alpha := fun index input =>
    ENNReal.le (scaled input) (functions index input)
  have regionsMeasurable : ∀ index, space.Measurable (regions index) := by
    intro index
    exact scaled.comparison_measurable (measurable index)
  have regionsMonotone : Set.MonotoneFamily regions := by
    intro first second included input member
    exact ENNReal.le_trans member
      (ENNReal.sequence_le_later
        (fun stage => monotone stage input) included)
  have unionEqual : Set.iUnion regions = Set.univ := by
    apply Set.ext
    intro input
    constructor
    · exact fun _ => True.intro
    · intro _
      change ∃ index, ENNReal.le (scaled input) (functions index input)
      by_cases scaledZero : scaled input = ENNReal.zero
      · refine ⟨0, ?_⟩
        rw [scaledZero]
        exact ENNReal.zero_le _
      · have simpleNonzero : simple input ≠ ENNReal.zero := by
          intro simpleZero
          apply scaledZero
          simp only [scaled, SimpleFunction.smul_apply, simpleZero,
            ENNReal.mul_zero]
        have scaledSimple : ENNReal.lt (scaled input) (simple input) := by
          simpa only [scaled, SimpleFunction.smul_apply] using
            strictUnit_mul_lt (simpleFinite input) simpleNonzero scaleIndex
        have scaledLimit : ENNReal.lt (scaled input)
            (ENNReal.iSup (fun index => functions index input)) := by
          refine ⟨ENNReal.le_trans scaledSimple.1 (simpleBound input), ?_⟩
          intro reverse
          exact scaledSimple.2
            (ENNReal.le_trans (simpleBound input) reverse)
        rcases ENNReal.exists_index_greater_of_lt_iSup scaledLimit with
          ⟨index, strictAtIndex⟩
        exact ⟨index, strictAtIndex.1⟩
  have continuous : scaled.integral measure =
      ENNReal.iSup (fun index =>
        scaled.integral (measure.restrict (regions index))) := by
    calc
      scaled.integral measure =
          scaled.integral (measure.restrict (Set.iUnion regions)) := by
        rw [unionEqual, measure.restrict_univ]
      _ = ENNReal.iSup (fun index =>
          scaled.integral (measure.restrict (regions index))) :=
        scaled.integral_restrict_iSup measure regions
          regionsMeasurable regionsMonotone
  rw [continuous]
  apply ENNReal.iSup_le
  intro index
  let restricted := scaled.restrict (regions index)
    (regionsMeasurable index)
  have restrictedBound : SimpleFunction.PointwiseLe restricted
      (functions index) := by
    intro input
    by_cases member : regions index input
    · rw [SimpleFunction.restrict_apply_of_mem scaled
          (regions index) (regionsMeasurable index) input member]
      exact member
    · rw [SimpleFunction.restrict_apply_of_not_mem scaled
          (regions index) (regionsMeasurable index) input member]
      exact ENNReal.zero_le _
  have restrictedIntegral :
      scaled.integral (measure.restrict (regions index)) =
        restricted.integral measure :=
    (scaled.integral_restrict (regions index)
      (regionsMeasurable index) measure).symm
  rw [restrictedIntegral]
  exact ENNReal.le_trans
    (restricted.integral_le_lintegral measure restrictedBound)
    (ENNReal.le_iSup (fun current =>
      lintegral measure (functions current)) index)

/-- Monotone convergence for measurable extended-nonnegative functions.
The exact sequence premise is pointwise monotonicity at each successor. -/
public theorem lintegral_iSup {alpha : Type u} {space : Space alpha}
    (measure : Measure space) (functions : Nat → alpha → ENNReal)
    (measurable : ∀ index,
      ENNRealMeasurable space (functions index))
    (monotone : ∀ stage input,
      ENNReal.le (functions stage input) (functions (stage + 1) input)) :
    lintegral measure (fun input =>
      ENNReal.iSup (fun index => functions index input)) =
      ENNReal.iSup (fun index => lintegral measure (functions index)) := by
  apply ENNReal.le_antisymm
  · apply lintegral_le
    intro lower lowerBound
    rw [lower.integral_iSup_approximation measure]
    apply ENNReal.iSup_le
    intro approximationIndex
    let approximation := SimpleFunction.approximation lower
      lower.measurable approximationIndex
    have approximationBound : SimpleFunction.PointwiseLe approximation
        (fun input => ENNReal.iSup
          (fun index => functions index input)) :=
      SimpleFunction.pointwiseLe_trans
        (SimpleFunction.approximation_le lower lower.measurable
          approximationIndex) lowerBound
    have scaledSupremum : approximation.integral measure =
        ENNReal.iSup (fun scaleIndex =>
          (SimpleFunction.smul (strictUnit scaleIndex) approximation).integral
            measure) := by
      calc
        approximation.integral measure =
            ENNReal.iSup (fun scaleIndex =>
              ENNReal.mul (strictUnit scaleIndex)
                (approximation.integral measure)) :=
          (iSup_strictUnit_mul (approximation.integral measure)).symm
        _ = ENNReal.iSup (fun scaleIndex =>
            (SimpleFunction.smul (strictUnit scaleIndex) approximation).integral
              measure) := by
          apply congrArg ENNReal.iSup
          funext scaleIndex
          exact (SimpleFunction.smul_integral
            (strictUnit scaleIndex) approximation measure).symm
    rw [scaledSupremum]
    apply ENNReal.iSup_le
    intro scaleIndex
    exact scaled_integral_le_iSup measure functions measurable monotone
      approximation
      (SimpleFunction.approximation_finite lower lower.measurable
        approximationIndex)
      approximationBound scaleIndex
  · apply ENNReal.iSup_le
    intro index
    apply lintegral_mono
    intro input
    exact ENNReal.le_iSup (fun current => functions current input) index

/-- A measurable function is reconstructed by the integrals of its canonical
finite rational approximations. -/
public theorem lintegral_eq_iSup_canonical
    {alpha : Type u} {space : Space alpha} (measure : Measure space)
    {function : alpha → ENNReal}
    (functionMeasurable : ENNRealMeasurable space function) :
    lintegral measure function =
      ENNReal.iSup (fun index =>
        (SimpleFunction.approximation function functionMeasurable index).integral
          measure) := by
  calc
    lintegral measure function =
        lintegral measure (fun input => ENNReal.iSup (fun index =>
          SimpleFunction.approximation function functionMeasurable index
            input)) := by
      apply lintegral_congr
      intro input
      exact (SimpleFunction.iSup_approximation function functionMeasurable
        input).symm
    _ = ENNReal.iSup (fun index => lintegral measure
        (SimpleFunction.approximation function functionMeasurable index)) :=
      lintegral_iSup measure
        (fun index => SimpleFunction.approximation function
          functionMeasurable index)
        (fun index => SimpleFunction.approximation_measurable function
          functionMeasurable index)
        (fun stage input => SimpleFunction.approximation_mono function
          functionMeasurable stage input)
    _ = ENNReal.iSup (fun index =>
        (SimpleFunction.approximation function functionMeasurable index).integral
          measure) := by
      apply congrArg ENNReal.iSup
      funext index
      exact SimpleFunction.lintegral_eq_integral
        (SimpleFunction.approximation function functionMeasurable index) measure

end Problib.Measure
