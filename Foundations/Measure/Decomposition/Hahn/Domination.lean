module

public import Foundations.Measure.Decomposition.Hahn.Existence
public import Foundations.Measure.Additive.AbsoluteContinuity

set_option autoImplicit false

/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying

Adapted from Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny adapts the positive domination passage from
exists_positive_of_not_mutuallySingular to construct a positive finite scaling
factor and a measurable region of positive reference measure for finite
absolutely continuous measures with positive target total mass.
-/

namespace Foundations.Measure.Measure

open Foundations.Real

universe u

variable {alpha : Type u} {space : Space alpha}

/-- Extracts a positive dominated region for finite absolutely continuous
measures with positive target total mass.
The result provides a finite positive factor and a measurable region of
positive reference measure.
On measurable subsets of this region, the scaled reference measure is bounded
above by the target measure. -/
public theorem exists_positive_dominated_region {target reference : Measure space}
    (targetFinite : IsFinite target) (referenceFinite : IsFinite reference)
    (absolutelyContinuous : AbsolutelyContinuous target reference)
    (positive : ENNReal.lt ENNReal.zero (target Set.univ)) :
    ∃ factor : ENNReal, ENNReal.Finite factor ∧ ENNReal.lt ENNReal.zero factor ∧
      ∃ region, space.Measurable region ∧ ENNReal.lt ENNReal.zero (reference region) ∧
        ∀ {set}, space.Measurable set → Set.Subset set region →
          ENNReal.le (ENNReal.mul factor (reference set)) (target set) := by
  classical
  apply Classical.byContradiction
  intro missing
  rcases ENNReal.existsPositiveSummableError ENNReal.one True.intro
    ENNReal.onePositive with ⟨errors, errorsPositive, summable⟩
  have errorsFinite : ENNReal.Finite (ENNReal.tsum errors) :=
    ENNReal.finiteOfLe summable True.intro
  have factorFinite := fun index => ENNReal.finiteOfLe
    (ENNReal.termLeTsum errors index) errorsFinite
  have comparisons : ∀ index, ENNReal.le (target Set.univ)
      (ENNReal.mul (errors index) (reference Set.univ)) := by
    intro index
    let decomposition := HahnDecomposition.ofFinite targetFinite
      (IsFinite.smul (errors index) (factorFinite index) referenceFinite)
    have referenceNull : reference decomposition.region = ENNReal.zero := by
      apply Classical.byContradiction
      intro nonzero
      apply missing
      refine ⟨errors index, factorFinite index, errorsPositive index,
        decomposition.region, decomposition.measurable,
        ENNReal.zeroLtIffNeZero.mpr nonzero, ?_⟩
      intro set setMeasurable included
      have bound := decomposition.positive setMeasurable included
      rw [Measure.smul_apply_measurable _ _ setMeasurable] at bound
      exact bound
    have targetNull := absolutelyContinuous decomposition.measurable referenceNull
    have partition := target.add_complement decomposition.measurable
    rw [targetNull, ENNReal.zeroAdd] at partition
    have bound := decomposition.negative (space.complement decomposition.measurable)
      (Set.subset_refl (Set.complement decomposition.region))
    rw [partition, Measure.smul_apply_measurable _ _
      (space.complement decomposition.measurable)] at bound
    exact ENNReal.leTrans bound
      (ENNReal.mulLeMulLeft (reference.mono (Set.subset_univ _)) (errors index))
  have seriesBound := ENNReal.tsumLeTsum comparisons
  rw [ENNReal.tsumConstOfNeZero (ENNReal.zeroLtIffNeZero.mp positive)] at seriesBound
  have equality :
      ENNReal.tsum (fun index => ENNReal.mul (errors index) (reference Set.univ)) =
        ENNReal.mul (reference Set.univ) (ENNReal.tsum errors) := by
    rw [ENNReal.tsumCongr (fun index => ENNReal.mulComm (errors index) (reference Set.univ)),
      ENNReal.tsumMulLeft]
  rw [equality] at seriesBound
  exact ENNReal.finiteOfLe seriesBound (ENNReal.mulFinite referenceFinite.univFinite errorsFinite)

end Foundations.Measure.Measure
