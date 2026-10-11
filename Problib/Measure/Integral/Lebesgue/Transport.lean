module

public import Problib.Measure.Integral.Lebesgue.Convergence
public import Problib.Measure.Additive.Dirac
import Problib.Measure.Integral.Simple.Approximation
import Problib.Measure.Integral.Simple.Integral.Transport

set_option autoImplicit false

/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl

Adapted from Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean and
Mathlib/MeasureTheory/Integral/Lebesgue/Countable.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.
-/

namespace Problib.Measure

open Problib.Real

universe u v

variable {alpha : Type u} {beta : Type v}
  {source : Space alpha} {target : Space beta}

public theorem lintegral_map
    (measure : Measure source)
    (before : alpha → beta)
    (beforeMeasurable : MeasurableMap source target before)
    {integrand : beta → ENNReal}
    (integrandMeasurable : ENNRealMeasurable target integrand) :
    lintegral (measure.map before beforeMeasurable) integrand =
      lintegral measure (fun input => integrand (before input)) := by
  have composedMeasurable :
      ENNRealMeasurable source (fun input => integrand (before input)) :=
    ENNRealMeasurable.comp integrandMeasurable beforeMeasurable
  rw [lintegral_eq_iSup_canonical
      (measure.map before beforeMeasurable) integrandMeasurable,
    lintegral_eq_iSup_canonical measure composedMeasurable]
  apply congrArg ENNReal.iSup
  funext index
  calc
    (SimpleFunction.approximation integrand integrandMeasurable index).integral
        (measure.map before beforeMeasurable) =
      (SimpleFunction.comp
          (SimpleFunction.approximation
            integrand integrandMeasurable index)
          before beforeMeasurable).integral measure :=
      SimpleFunction.integral_map
        (SimpleFunction.approximation integrand integrandMeasurable index)
        measure before beforeMeasurable
    _ = (SimpleFunction.approximation
          (fun input => integrand (before input))
          composedMeasurable index).integral measure := by
      apply SimpleFunction.integral_congr (measure := measure)
      intro input
      simp only [SimpleFunction.comp_apply,
        SimpleFunction.approximation_apply]

public theorem lintegral_dirac
    (space : Space alpha) (point : alpha)
    {integrand : alpha → ENNReal}
    (integrandMeasurable : ENNRealMeasurable space integrand) :
    lintegral (Measure.dirac space point) integrand = integrand point := by
  rw [lintegral_eq_iSup_canonical
    (Measure.dirac space point) integrandMeasurable]
  calc
    ENNReal.iSup (fun index =>
        (SimpleFunction.approximation
          integrand integrandMeasurable index).integral
            (Measure.dirac space point)) =
      ENNReal.iSup (fun index =>
        SimpleFunction.approximation
          integrand integrandMeasurable index point) := by
      apply congrArg ENNReal.iSup
      funext index
      exact SimpleFunction.integral_dirac
        (SimpleFunction.approximation
          integrand integrandMeasurable index) point
    _ = integrand point :=
      SimpleFunction.iSup_approximation
        integrand integrandMeasurable point

/-- A Dirac measure at a measurable point integrates every integrand, measurable
or not, to its value at the point. Every simple lower bound is at most the value
there, and the indicator of the point attains it. -/
public theorem lintegral_dirac_of_measurable_singleton
    (space : Space alpha) (point : alpha) (integrand : alpha → ENNReal)
    (singleton : space.Measurable (Set.singleton point)) :
    lintegral (Measure.dirac space point) integrand = integrand point := by
  apply ENNReal.le_antisymm
  · apply lintegral_le
    intro lower included
    rw [SimpleFunction.integral_dirac]
    exact included point
  · let bump := SimpleFunction.indicator (Set.singleton point) singleton (integrand point)
    have below : SimpleFunction.PointwiseLe bump integrand := by
      intro input
      by_cases member : Set.singleton point input
      · rw [SimpleFunction.indicator_apply_of_mem _ _ _ _ member]
        cases member
        exact ENNReal.le_refl _
      · rw [SimpleFunction.indicator_apply_of_not_mem _ _ _ _ member]
        exact ENNReal.zero_le _
    have attained := bump.integral_le_lintegral (Measure.dirac space point) below
    have peak : bump point = integrand point :=
      SimpleFunction.indicator_apply_of_mem _ _ _ _ rfl
    rw [SimpleFunction.integral_dirac, peak] at attained
    exact attained

end Problib.Measure
