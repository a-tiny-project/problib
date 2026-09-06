module

public import Foundations.Measure.Integral.Density.Basic
import Foundations.Measure.Integral.Lebesgue.Algebra
import Foundations.Measure.Integral.Simple.Induction
import Foundations.Measure.Extended.Algebra.Binary

set_option autoImplicit false

/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl

Adapted from Mathlib/MeasureTheory/Measure/WithDensity.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.
-/

namespace Foundations.Measure

open Foundations.Real

universe u

variable {alpha : Type u} {space : Space alpha}

/-- Integration against a density is multiplication of the integrand by that
density before integration against the base measure. -/
public theorem lintegral_withDensity
    (measure : Measure space)
    {density integrand : alpha → ENNReal}
    (densityMeasurable : ENNRealMeasurable space density)
    (integrandMeasurable : ENNRealMeasurable space integrand) :
    lintegral (measure.withDensity density) integrand =
      lintegral measure
        (fun input => ENNReal.mul (density input) (integrand input)) := by
  refine ENNRealMeasurable.induction
    (motive := fun current =>
      lintegral (measure.withDensity density) current =
        lintegral measure
          (fun input => ENNReal.mul (density input) (current input)))
    ?_ ?_ ?_ ?_ integrandMeasurable
  · have productZero :
        (fun input : alpha => ENNReal.mul (density input) ENNReal.zero) =
          (fun _ => ENNReal.zero) := by
      funext input
      exact ENNReal.mulZero (density input)
    rw [productZero, lintegral_const, lintegral_const,
      ENNReal.zeroMul, ENNReal.zeroMul]
  · intro region regionMeasurable value
    let constant : alpha → ENNReal := fun _ => value
    calc
      lintegral (measure.withDensity density)
          (ennrealIndicator region constant) =
          lintegral
            ((measure.withDensity density).restrict region) constant :=
        lintegral_indicator (measure.withDensity density) region
          regionMeasurable constant
      _ = ENNReal.mul value ((measure.withDensity density) region) := by
        rw [lintegral_const, Measure.restrict_apply_univ]
      _ = ENNReal.mul value
          (lintegral (measure.restrict region) density) := by
        rw [measure.withDensity_apply density regionMeasurable]
      _ = lintegral (measure.restrict region)
          (fun input => ENNReal.mul value (density input)) :=
        (lintegral_smul (measure.restrict region) value
          densityMeasurable).symm
      _ = lintegral measure
          (ennrealIndicator region
            (fun input => ENNReal.mul value (density input))) :=
        (lintegral_indicator measure region regionMeasurable
          (fun input => ENNReal.mul value (density input))).symm
      _ = lintegral measure
          (fun input => ENNReal.mul (density input)
            (ennrealIndicator region constant input)) := by
        apply lintegral_congr
        intro input
        classical
        by_cases member : region input
        · simp only [ennrealIndicator, ennrealPiecewise, if_pos member]
          exact ENNReal.mulComm value (density input)
        · simp only [ennrealIndicator, ennrealPiecewise, if_neg member,
            ENNReal.mulZero]
  · intro left right leftMeasurable rightMeasurable
      leftChange rightChange
    calc
      lintegral (measure.withDensity density)
          (fun input => ENNReal.add (left input) (right input)) =
          ENNReal.add
            (lintegral (measure.withDensity density) left)
            (lintegral (measure.withDensity density) right) :=
        lintegral_add (measure.withDensity density)
          leftMeasurable rightMeasurable
      _ = ENNReal.add
          (lintegral measure
            (fun input => ENNReal.mul (density input) (left input)))
          (lintegral measure
            (fun input => ENNReal.mul (density input) (right input))) := by
        rw [leftChange, rightChange]
      _ = lintegral measure
          (fun input => ENNReal.add
            (ENNReal.mul (density input) (left input))
            (ENNReal.mul (density input) (right input))) :=
        (lintegral_add measure
          (densityMeasurable.mul leftMeasurable)
          (densityMeasurable.mul rightMeasurable)).symm
      _ = lintegral measure
          (fun input => ENNReal.mul (density input)
            (ENNReal.add (left input) (right input))) := by
        apply lintegral_congr
        intro input
        exact (ENNReal.mulAdd (density input) (left input) (right input)).symm
  · intro functions functionsMeasurable functionsMonotone changes
    calc
      lintegral (measure.withDensity density)
          (fun input => ENNReal.iSup
            (fun index => functions index input)) =
          ENNReal.iSup (fun index =>
            lintegral (measure.withDensity density) (functions index)) :=
        lintegral_iSup (measure.withDensity density) functions
          functionsMeasurable
          (fun stage input => functionsMonotone input stage)
      _ = ENNReal.iSup (fun index => lintegral measure
          (fun input => ENNReal.mul (density input)
            (functions index input))) := by
        apply congrArg ENNReal.iSup
        funext index
        exact changes index
      _ = lintegral measure (fun input => ENNReal.iSup
          (fun index => ENNReal.mul (density input)
            (functions index input))) :=
        (lintegral_iSup measure
          (fun index input => ENNReal.mul (density input)
            (functions index input))
          (fun index => densityMeasurable.mul
            (functionsMeasurable index))
          (fun stage input => ENNReal.mulLeMulLeft
            (functionsMonotone input stage) (density input))).symm
      _ = lintegral measure
          (fun input => ENNReal.mul (density input)
            (ENNReal.iSup (fun index => functions index input))) := by
        apply lintegral_congr
        intro input
        exact (ENNReal.mulISup (density input)
          (fun index => functions index input)).symm

end Foundations.Measure
