module

public import Problib.Measure.Extended.Algebra
public import Problib.Real.Series.Core
public import Problib.Real.Series.Maximum

set_option autoImplicit false

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov

Adapted from Mathlib/MeasureTheory/Constructions/BorelSpace/Real.lean at
commit 15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny defines a series as the supremum of its finite partial sums, so series
measurability is a direct consequence of countable-supremum measurability.
-/

namespace Problib.Measure

open Problib.Real

universe u

namespace ENNRealMeasurable

variable {α : Type u} {source : Space α}

/-- Prefix maxima of a sequence of measurable extended nonnegative real
functions are measurable at every finite stage. -/
public theorem prefixMax {functions : Nat → α → ENNReal}
    (measurable : ∀ index, ENNRealMeasurable source (functions index)) (stage : Nat) :
    ENNRealMeasurable source
      (fun value => ENNReal.prefixMax (fun index => functions index value) stage) := by
  induction stage with
  | zero => exact measurable 0
  | succ stage induction => exact max induction (measurable (stage + 1))

public theorem partialSum {functions : Nat → α → ENNReal}
    (measurable : ∀ index,
      ENNRealMeasurable source (functions index)) (count : Nat) :
    ENNRealMeasurable source (fun value =>
      ENNReal.partialSum (fun index => functions index value) count) := by
  induction count with
  | zero =>
      have equal : (fun value : α =>
          ENNReal.partialSum (fun index => functions index value) 0) =
          (fun _ => ENNReal.zero) := by
        funext value
        rfl
      rw [equal]
      exact constant source ENNReal.zero
  | succ count induction =>
      have sumMeasurable := add induction (measurable count)
      have equal : (fun value : α =>
          ENNReal.partialSum (fun index => functions index value)
            (count + 1)) =
          (fun value => ENNReal.add
            (ENNReal.partialSum
              (fun index => functions index value) count)
            (functions count value)) := by
        funext value
        rfl
      rw [equal]
      exact sumMeasurable

public theorem tsum {functions : Nat → α → ENNReal}
    (measurable : ∀ index,
      ENNRealMeasurable source (functions index)) :
    ENNRealMeasurable source (fun value =>
      ENNReal.tsum (fun index => functions index value)) := by
  have sumsMeasurable : ∀ count, ENNRealMeasurable source (fun value =>
      ENNReal.partialSum (fun index => functions index value) count) :=
    partialSum measurable
  have supremumMeasurable := iSup sumsMeasurable
  have equal : (fun value : α =>
      ENNReal.tsum (fun index => functions index value)) =
      (fun value => ENNReal.iSup (fun count =>
        ENNReal.partialSum (fun index => functions index value) count)) := by
    funext value
    rfl
  rw [equal]
  exact supremumMeasurable

end ENNRealMeasurable

end Problib.Measure
