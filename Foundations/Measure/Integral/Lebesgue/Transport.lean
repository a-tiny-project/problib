module

public import Foundations.Measure.Integral.Lebesgue.Convergence
public import Foundations.Measure.Additive.Dirac
import Foundations.Measure.Integral.Simple.Approximation
import Foundations.Measure.Integral.Simple.Integral.Transport

set_option autoImplicit false

/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl

Adapted from Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean and
Mathlib/MeasureTheory/Integral/Lebesgue/Countable.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.
-/

namespace Foundations.Measure

open Foundations.Real

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

end Foundations.Measure
