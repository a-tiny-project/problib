module

public import Problib.Measure.Integral.Lebesgue.Algebra
public import Problib.Measure.AlmostEverywhere.Basic

set_option autoImplicit false

/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl

Adapted from Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.
-/

namespace Problib.Measure

open Problib.Real

universe u

variable {alpha : Type u} {space : Space alpha}

/-- The measurable event on which a nonnegative function reaches a threshold. -/
@[expose] public def upperLevel (function : alpha → ENNReal)
    (threshold : ENNReal) : Set alpha :=
  Set.preimage function (ennrealIci threshold)

public theorem upperLevel_measurable {function : alpha → ENNReal}
    (functionMeasurable : ENNRealMeasurable space function)
    (threshold : ENNReal) :
    space.Measurable (upperLevel function threshold) :=
  functionMeasurable.ici threshold

/-- Markov's inequality in multiplicative form. This statement remains valid
at zero and top thresholds, so it needs no division side conditions. -/
public theorem markov (measure : Measure space)
    {function : alpha → ENNReal}
    (functionMeasurable : ENNRealMeasurable space function)
    (threshold : ENNReal) :
    ENNReal.le
      (ENNReal.mul threshold (measure (upperLevel function threshold)))
      (lintegral measure function) := by
  let constant : alpha → ENNReal := fun _ => threshold
  have eventMeasurable := upperLevel_measurable functionMeasurable threshold
  have indicatorBound : ∀ value,
      ENNReal.le
        (ennrealIndicator (upperLevel function threshold) constant value)
        (function value) := by
    intro value
    classical
    by_cases member : upperLevel function threshold value
    · unfold ennrealIndicator ennrealPiecewise
      rw [ite_eq_left member]
      exact member
    · unfold ennrealIndicator ennrealPiecewise
      rw [ite_eq_right member]
      exact ENNReal.zero_le _
  have indicatorIntegral :
      ENNReal.mul threshold (measure (upperLevel function threshold)) =
        lintegral measure
          (ennrealIndicator (upperLevel function threshold) constant) := by
    calc
      ENNReal.mul threshold (measure (upperLevel function threshold)) =
          lintegral (measure.restrict (upperLevel function threshold))
            constant := by
        rw [lintegral_const,
          measure.restrict_apply_univ (upperLevel function threshold)]
      _ = lintegral measure
          (ennrealIndicator (upperLevel function threshold) constant) := by
        rw [lintegral_indicator measure (upperLevel function threshold)
          eventMeasurable constant]
  rw [indicatorIntegral]
  exact lintegral_mono measure indicatorBound

/-- A measurable function with finite integral is finite almost everywhere.
Markov's inequality at `⊤` bounds `⊤ · measure {function = ⊤}` by the finite
integral, and a finite product with `⊤` forces the set to be null. -/
public theorem ae_finite_of_lintegral_finite (measure : Measure space)
    {function : alpha → ENNReal} (functionMeasurable : ENNRealMeasurable space function)
    (finite : ENNReal.Finite (lintegral measure function)) :
    measure.AE (fun value => ENNReal.Finite (function value)) := by
  have bound := markov measure functionMeasurable ENNReal.top
  have null : measure.NullSet (upperLevel function ENNReal.top) := by
    apply Classical.byContradiction
    intro nonzero
    rw [ENNReal.top_mul_of_ne_zero nonzero] at bound
    exact ENNReal.finite_of_le bound finite
  apply null.mono
  intro value infinite
  exact ENNReal.top_le_iff.mpr (Classical.not_not.mp
    fun notTop => infinite (ENNReal.finite_iff_ne_top.mpr notTop))

end Problib.Measure
