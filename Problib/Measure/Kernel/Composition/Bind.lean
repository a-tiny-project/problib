module

public import Problib.Measure.Kernel.Composition.Bind.Core
import Problib.Measure.Integral.Lebesgue.Algebra
import Problib.Measure.Integral.Lebesgue.Measure
import Problib.Measure.Integral.Lebesgue.Transport

set_option autoImplicit false

/-
Copyright (c) 2017 Johannes Hölzl, Mario Carneiro.
Copyright (c) 2025 Rémy Degenne, Lorenzo Luccioli.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Rémy Degenne, Lorenzo Luccioli

Adapted from Mathlib/MeasureTheory/Measure/GiryMonad.lean and
Mathlib/Probability/Kernel/Composition/MeasureComp.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.
-/

namespace Problib.Measure

open Problib.Real

universe u v

namespace Measure

variable {alpha : Type u} {beta : Type v}
  {source : Space alpha} {target : Space beta}

/-- Binding the zero measure against any measurable kernel produces the zero measure. -/
@[simp] public theorem zero_bind (kernel : Kernel source target) :
    (Measure.zero source).bind kernel = Measure.zero target := by
  apply Measure.ext
  intro set measurable
  rw [bind_apply _ _ measurable, lintegral_zero_measure, Measure.zero_apply]

/-- Binding any measure against the zero kernel produces the zero measure. -/
@[simp] public theorem bind_zero (measure : Measure source) :
    measure.bind (Kernel.zero source target) = Measure.zero target := by
  apply Measure.ext
  intro region measurable
  rw [bind_apply _ _ measurable, Measure.zero_apply]
  have equal : (fun input => Kernel.zero source target input region) =
      (fun _ => ENNReal.zero) := funext (fun _ => Measure.zero_apply region)
  rw [equal, lintegral_zero]

/-- Bind distributes over measure addition in its first argument. -/
public theorem add_bind (left right : Measure source) (kernel : Kernel source target) :
    (Measure.add left right).bind kernel = Measure.add (left.bind kernel) (right.bind kernel) := by
  apply Measure.ext
  intro set measurable
  rw [bind_apply _ _ measurable, Measure.add_apply_measurable _ _ measurable,
    bind_apply _ _ measurable, bind_apply _ _ measurable, lintegral_add_measure]

/-- Bind commutes with scalar multiplication in its first argument. -/
public theorem smul_bind (factor : ENNReal) (measure : Measure source) (kernel : Kernel source target) :
    (Measure.smul factor measure).bind kernel = Measure.smul factor (measure.bind kernel) := by
  apply Measure.ext
  intro set measurable
  rw [bind_apply _ _ measurable, Measure.smul_apply_measurable _ _ measurable,
    bind_apply _ _ measurable, lintegral_smul_measure]

/-- Binding a probability measure against a kernel whose fibers are all
probability measures produces a probability measure. -/
public theorem IsProbability.bind {measure : Measure source} (probability : IsProbability measure)
    (kernel : Kernel source target) (normalized : ∀ input, IsProbability (kernel input)) :
    IsProbability (measure.bind kernel) := by
  constructor
  rw [bind_apply _ _ target.univ]
  have equal : (fun input => kernel input Set.univ) = (fun _ => ENNReal.one) :=
    funext (fun input => (normalized input).univ_eq_one)
  rw [equal, lintegral_const, probability.univ_eq_one, ENNReal.one_mul]

/-- Binding against a constant kernel equals scalar multiplication by the source total mass. -/
@[simp] public theorem bind_const (measure : Measure source)
    (other : Measure target) :
    measure.bind (Kernel.const source other) =
      Measure.smul (measure Set.univ) other := by
  apply Measure.ext
  intro set setMeasurable
  rw [bind_apply measure (Kernel.const source other) setMeasurable,
    Measure.smul_apply_measurable (measure Set.univ) other setMeasurable]
  calc
    lintegral measure
        (fun input => Kernel.const source other input set) =
        lintegral measure (fun _ => other set) := by
      apply lintegral_congr
      intro input
      rfl
    _ = ENNReal.mul (other set) (measure Set.univ) :=
      lintegral_const measure (other set)
    _ = ENNReal.mul (measure Set.univ) (other set) :=
      ENNReal.mul_comm _ _

/-- Binding a Dirac measure evaluates the kernel at that point. -/
@[simp] public theorem dirac_bind (point : alpha)
    (kernel : Kernel source target) :
    (Measure.dirac source point).bind kernel = kernel point := by
  apply Measure.ext
  intro set setMeasurable
  rw [bind_apply (Measure.dirac source point) kernel setMeasurable,
    lintegral_dirac source point
    (kernel.measurable setMeasurable)]

/-- Binding against a deterministic kernel equals pushforward along the measurable map. -/
@[simp] public theorem bind_deterministic (measure : Measure source)
    (function : alpha → beta)
    (functionMeasurable : MeasurableMap source target function) :
    measure.bind (Kernel.deterministic function functionMeasurable) =
      measure.map function functionMeasurable := by
  apply Measure.ext
  intro set setMeasurable
  rw [bind_apply measure
      (Kernel.deterministic function functionMeasurable) setMeasurable,
    Measure.map_apply measure function functionMeasurable setMeasurable]
  calc
    lintegral measure (fun input =>
        Kernel.deterministic function functionMeasurable input set) =
        lintegral measure (ennrealIndicator
          (Set.preimage function set) (fun _ => ENNReal.one)) := by
      apply lintegral_congr
      intro input
      rw [Kernel.deterministic_apply,
        Measure.dirac_apply target (function input) setMeasurable]
      rfl
    _ = lintegral (measure.restrict (Set.preimage function set))
        (fun _ => ENNReal.one) :=
      lintegral_indicator measure _ (functionMeasurable setMeasurable) _
    _ = measure (Set.preimage function set) := by
      rw [lintegral_const, measure.restrict_apply_univ,
        ENNReal.one_mul]

/-- Countable sums of measures distribute over bind on the left. -/
public theorem bind_sum_left (measures : Nat → Measure source)
    (kernel : Kernel source target) :
    (Measure.sum measures).bind kernel =
      Measure.sum (fun index => (measures index).bind kernel) := by
  apply Measure.ext
  intro set setMeasurable
  rw [bind_apply (Measure.sum measures) kernel setMeasurable,
    Measure.sum_apply
      (fun index => (measures index).bind kernel) setMeasurable,
    lintegral_sum measures]
  apply ENNReal.tsum_congr
  intro index
  rw [bind_apply (measures index) kernel setMeasurable]

/-- Countable sums of kernels distribute over bind on the right. -/
public theorem bind_sum_right (measure : Measure source)
    (kernels : Nat → Kernel source target) :
    measure.bind (Kernel.sum kernels) =
      Measure.sum (fun index => measure.bind (kernels index)) := by
  apply Measure.ext
  intro set setMeasurable
  rw [bind_apply measure (Kernel.sum kernels) setMeasurable,
    Measure.sum_apply
      (fun index => measure.bind (kernels index)) setMeasurable]
  calc
    lintegral measure (fun input => Kernel.sum kernels input set) =
        lintegral measure (fun input => ENNReal.tsum
          (fun index => kernels index input set)) := by
      apply lintegral_congr
      intro input
      rw [Kernel.sum_apply, Measure.sum_apply _ setMeasurable]
    _ = ENNReal.tsum (fun index =>
        lintegral measure (fun input => kernels index input set)) :=
      lintegral_tsum measure
        (fun index input => kernels index input set)
        (fun index => (kernels index).measurable setMeasurable)
    _ = ENNReal.tsum (fun index => measure.bind (kernels index) set) := by
      apply ENNReal.tsum_congr
      intro index
      rw [bind_apply measure (kernels index) setMeasurable]

namespace IsFinite

/-- Binding a finite measure with a uniformly finite kernel stays finite. -/
public theorem bind {measure : Measure source} (measureFinite : IsFinite measure)
    {kernel : Kernel source target} (kernelFinite : Kernel.IsFinite kernel) :
    IsFinite (measure.bind kernel) := by
  rcases kernelFinite.exists_bound with
    ⟨bound, boundFinite, bounded⟩
  constructor
  rw [Measure.bind_apply measure kernel target.univ]
  apply ENNReal.finite_of_le
    (lintegral_mono measure (fun input => bounded input))
  rw [lintegral_const]
  exact ENNReal.mul_finite boundFinite measureFinite.univ_finite

end IsFinite

namespace SFinite

/-- Bind preserves constructive s-finiteness in both arguments. -/
public noncomputable def bind {measure : Measure source}
    (measureFinite : SFinite measure) {kernel : Kernel source target}
    (kernelFinite : Kernel.IsSFinite kernel) :
    SFinite (measure.bind kernel) where
  components := Measure.flatten (fun row column =>
    (measureFinite.components row).bind
      (kernelFinite.components column))
  finite := by
    intro index
    exact IsFinite.bind
      (measureFinite.finite (Countable.Pair.decode index).1)
      (kernelFinite.finite (Countable.Pair.decode index).2)
  sum_eq := by
    rw [Measure.sum_double]
    calc
      Measure.sum (fun row => Measure.sum (fun column =>
          (measureFinite.components row).bind
            (kernelFinite.components column))) =
          Measure.sum (fun row =>
            (measureFinite.components row).bind
              (Kernel.sum kernelFinite.components)) := by
        apply congrArg Measure.sum
        funext row
        exact (Measure.bind_sum_right
          (measureFinite.components row) kernelFinite.components).symm
      _ = (Measure.sum measureFinite.components).bind
          (Kernel.sum kernelFinite.components) :=
        (Measure.bind_sum_left measureFinite.components
          (Kernel.sum kernelFinite.components)).symm
      _ = measure.bind kernel := by
        rw [measureFinite.sum_eq, kernelFinite.sum_eq]

end SFinite

end Measure

end Problib.Measure
