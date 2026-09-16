module

public import Foundations.Measure.Kernel.Composition.Bind
public import Foundations.Measure.Kernel.Measurable

set_option autoImplicit false

/-
Copyright (c) 2023 Rémy Degenne, Etienne Marion.
Copyright (c) 2025 Rémy Degenne, Lorenzo Luccioli.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Etienne Marion, Lorenzo Luccioli

Adapted from Mathlib/Probability/Kernel/Composition/Comp.lean and
Mathlib/Probability/Kernel/Composition/MeasureComp.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.
-/

namespace Foundations.Measure

open Foundations.Real

universe u v w x

namespace Kernel

variable {alpha : Type u} {beta : Type v} {gamma : Type w}
  {source : Space alpha} {middle : Space beta} {target : Space gamma}

/-- Compose kernels in execution order. -/
@[expose] public noncomputable def comp (first : Kernel source middle)
    (second : Kernel middle target) : Kernel source target where
  toFun := fun input => (first input).bind second
  measurable := by
    intro set setMeasurable
    have integralMeasurable := first.lintegral_measurable
      (second.measurable setMeasurable)
    have equal : (fun input => (first input).bind second set) =
        (fun input => lintegral (first input)
          (fun value => second value set)) := by
      funext input
      exact Measure.bind_apply (first input) second setMeasurable
    rw [equal]
    exact integralMeasurable

@[simp] public theorem comp_apply (first : Kernel source middle)
    (second : Kernel middle target) (input : alpha) :
    first.comp second input = (first input).bind second := rfl

public theorem comp_apply_measurable (first : Kernel source middle)
    (second : Kernel middle target) (input : alpha)
    {set : Set gamma} (setMeasurable : target.Measurable set) :
    first.comp second input set =
      lintegral (first input) (fun value => second value set) := by
  rw [comp_apply, Measure.bind_apply _ _ setMeasurable]

public theorem lintegral_comp (first : Kernel source middle)
    (second : Kernel middle target) (input : alpha)
    {function : gamma → ENNReal}
    (functionMeasurable : ENNRealMeasurable target function) :
    lintegral (first.comp second input) function =
      lintegral (first input)
        (fun value => lintegral (second value) function) := by
  rw [comp_apply, Measure.lintegral_bind _ _ functionMeasurable]

end Kernel

namespace Measure

variable {alpha : Type u} {beta : Type v} {gamma : Type w}
  {source : Space alpha} {middle : Space beta} {target : Space gamma}

/-- Bind is associative for genuinely measurable kernels. -/
public theorem bind_assoc (measure : Measure source)
    (first : Kernel source middle) (second : Kernel middle target) :
    (measure.bind first).bind second =
      measure.bind (Kernel.comp first second) := by
  apply Measure.ext
  intro set setMeasurable
  rw [bind_apply (measure.bind first) second setMeasurable,
    lintegral_bind measure first (second.measurable setMeasurable),
    bind_apply measure (Kernel.comp first second) setMeasurable]
  apply lintegral_congr
  intro input
  rw [Kernel.comp_apply,
    bind_apply (first input) second setMeasurable]

end Measure

namespace Kernel

variable {alpha : Type u} {beta : Type v} {gamma : Type w}
  {delta : Type x} {source : Space alpha} {middle : Space beta}
  {target : Space gamma} {result : Space delta}

/-- Kernel composition is associative. -/
public theorem comp_assoc (first : Kernel source middle)
    (second : Kernel middle target) (third : Kernel target result) :
    (first.comp second).comp third = first.comp (second.comp third) := by
  apply Kernel.ext
  intro input
  rw [comp_apply, comp_apply, comp_apply]
  exact Measure.bind_assoc (first input) second third

@[simp] public theorem const_comp (source : Space alpha)
    (measure : Measure middle) (kernel : Kernel middle target) :
    (Kernel.const source measure).comp kernel =
      Kernel.const source (measure.bind kernel) := by
  apply Kernel.ext
  intro input
  rw [comp_apply, const_apply, const_apply]

@[simp] public theorem deterministic_comp_apply (function : alpha → beta)
    (functionMeasurable : MeasurableMap source middle function)
    (kernel : Kernel middle target) (input : alpha) :
    (Kernel.deterministic function functionMeasurable).comp kernel input =
      kernel (function input) := by
  rw [comp_apply, deterministic_apply, Measure.dirac_bind]

@[simp] public theorem comp_deterministic (kernel : Kernel source middle)
    (function : beta → gamma)
    (functionMeasurable : MeasurableMap middle target function) :
    kernel.comp (Kernel.deterministic function functionMeasurable) =
      kernel.map function functionMeasurable := by
  apply Kernel.ext
  intro input
  rw [comp_apply, map_apply, Measure.bind_deterministic]

namespace IsFinite

/-- Uniformly finite kernels are closed under composition. -/
public theorem comp {first : Kernel source middle} (firstFinite : IsFinite first)
    {second : Kernel middle target} (secondFinite : IsFinite second) :
    IsFinite (first.comp second) := by
  rcases firstFinite.exists_bound with
    ⟨firstBound, firstBoundFinite, firstBounded⟩
  rcases secondFinite.exists_bound with
    ⟨secondBound, secondBoundFinite, secondBounded⟩
  refine ⟨⟨ENNReal.mul secondBound firstBound,
    ENNReal.mulFinite secondBoundFinite firstBoundFinite, ?_⟩⟩
  intro input
  rw [Kernel.comp_apply, Measure.bind_apply _ _ target.univ]
  exact ENNReal.leTrans
    (lintegral_mono (first input) (fun value => secondBounded value))
    (by
      rw [lintegral_const]
      exact ENNReal.mulLeMulLeft (firstBounded input) secondBound)

end IsFinite

namespace IsSFinite

/-- Constructively s-finite kernels are closed under composition. -/
public noncomputable def comp {first : Kernel source middle}
    (firstFinite : IsSFinite first) {second : Kernel middle target}
    (secondFinite : IsSFinite second) :
    IsSFinite (first.comp second) where
  components := Kernel.flatten (fun row column =>
    (firstFinite.components row).comp (secondFinite.components column))
  finite := by
    intro index
    exact IsFinite.comp
      (firstFinite.finite (Countable.Pair.decode index).1)
      (secondFinite.finite (Countable.Pair.decode index).2)
  sum_eq := by
    apply Kernel.ext
    intro input
    change Measure.sum (Measure.flatten (fun row column =>
      (firstFinite.components row input).bind
        (secondFinite.components column))) =
      (first input).bind second
    rw [Measure.sum_double]
    calc
      Measure.sum (fun row => Measure.sum (fun column =>
          (firstFinite.components row input).bind
            (secondFinite.components column))) =
          Measure.sum (fun row =>
            (firstFinite.components row input).bind
              (Kernel.sum secondFinite.components)) := by
        apply congrArg Measure.sum
        funext row
        exact (Measure.bind_sum_right
          (firstFinite.components row input)
          secondFinite.components).symm
      _ = (Measure.sum (fun row => firstFinite.components row input)).bind
          (Kernel.sum secondFinite.components) :=
        (Measure.bind_sum_left
          (fun row => firstFinite.components row input)
          (Kernel.sum secondFinite.components)).symm
      _ = (Kernel.sum firstFinite.components input).bind
          (Kernel.sum secondFinite.components) := by
        rw [Kernel.sum_apply]
      _ = (first input).bind second := by
        rw [firstFinite.sum_eq, secondFinite.sum_eq]

end IsSFinite

end Kernel

end Foundations.Measure
