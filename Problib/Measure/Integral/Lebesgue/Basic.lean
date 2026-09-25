module

public import Problib.Measure.Integral.Simple.Integral.Basic
import Problib.Measure.Integral.Simple.Integral.Algebra

set_option autoImplicit false

/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl

Adapted from Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny takes the supremum over explicit measurable finite-range lower bounds.
-/

namespace Problib.Measure

open Problib.Real

universe u

variable {alpha : Type u} {space : Space alpha}

/-- The lower Lebesgue integral is the supremum of the integrals of all
measurable simple functions below the integrand. -/
@[expose] public noncomputable def lintegral
    (measure : Measure space) (function : alpha → ENNReal) : ENNReal :=
  ENNReal.supremum (fun value =>
    ∃ lower : SimpleFunction space,
      SimpleFunction.PointwiseLe lower function ∧
      value = lower.integral measure)

namespace SimpleFunction

public theorem integral_le_lintegral (function : SimpleFunction space)
    (measure : Measure space) {upper : alpha → ENNReal}
    (included : PointwiseLe function upper) :
    ENNReal.le (function.integral measure) (lintegral measure upper) := by
  unfold lintegral
  exact ENNReal.le_supremum ⟨function, included, rfl⟩

end SimpleFunction

/-- Eliminate a lower integral by checking every simple lower bound. -/
public theorem lintegral_le (measure : Measure space)
    (function : alpha → ENNReal) {upper : ENNReal}
    (bounds : ∀ lower : SimpleFunction space,
      SimpleFunction.PointwiseLe lower function →
      ENNReal.le (lower.integral measure) upper) :
    ENNReal.le (lintegral measure function) upper := by
  unfold lintegral
  apply ENNReal.supremum_le
  rintro value ⟨lower, included, rfl⟩
  exact bounds lower included

public theorem SimpleFunction.lintegral_eq_integral
    (function : SimpleFunction space) (measure : Measure space) :
    lintegral measure function = function.integral measure := by
  apply ENNReal.le_antisymm
  · apply lintegral_le
    intro lower included
    exact SimpleFunction.integral_mono included measure
  · exact function.integral_le_lintegral measure
      function.pointwiseLe_refl

public theorem SimpleFunction.integral_eq_lintegral
    (function : SimpleFunction space) (measure : Measure space) :
    function.integral measure = lintegral measure function :=
  (function.lintegral_eq_integral measure).symm

public theorem lintegral_mono (measure : Measure space)
    {lower upper : alpha → ENNReal}
    (included : ∀ input, ENNReal.le (lower input) (upper input)) :
    ENNReal.le (lintegral measure lower) (lintegral measure upper) := by
  apply lintegral_le
  intro simple simpleLower
  apply simple.integral_le_lintegral
  intro input
  exact ENNReal.le_trans (simpleLower input) (included input)

public theorem lintegral_congr (measure : Measure space)
    {left right : alpha → ENNReal}
    (equal : ∀ input, left input = right input) :
    lintegral measure left = lintegral measure right := by
  apply ENNReal.le_antisymm
  · apply lintegral_mono
    intro input
    rw [equal input]
    exact ENNReal.le_refl _
  · apply lintegral_mono
    intro input
    rw [equal input]
    exact ENNReal.le_refl _

end Problib.Measure
