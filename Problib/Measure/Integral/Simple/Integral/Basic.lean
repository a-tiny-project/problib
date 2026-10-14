module

public import Problib.Algebra.Sum
public import Problib.Measure.Additive.Core
public import Problib.Measure.Integral.Simple.Decomposition

set_option autoImplicit false

/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl

Adapted from Mathlib/MeasureTheory/Function/SimpleFunc.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.
-/

namespace Problib.Measure

open Problib.Real

universe u v

namespace SimpleFunction

variable {alpha : Type u} {source : Space alpha}

/-- The integral of a simple function is the finite weighted sum of the
measures of its level sets. -/
@[expose] public noncomputable def integral
    (function : SimpleFunction source) (measure : Measure source) : ENNReal :=
  ENNReal.additiveLaws.listSum (function.values.map fun value =>
    ENNReal.mul value (measure (function.fiber value)))

public theorem integral_eq_listSum
    (function : SimpleFunction source) (measure : Measure source) :
    integral function measure =
      ENNReal.additiveLaws.listSum (function.values.map fun value =>
        ENNReal.mul value (measure (function.fiber value))) :=
  rfl

public theorem integral_congr {left right : SimpleFunction source}
    (equal : ∀ input, left input = right input)
    (measure : Measure source) :
    integral left measure = integral right measure := by
  have functionsEqual : left = right := SimpleFunction.ext equal
  rw [functionsEqual]

end SimpleFunction

end Problib.Measure
