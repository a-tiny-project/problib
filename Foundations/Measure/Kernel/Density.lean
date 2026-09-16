module

public import Foundations.Measure.Kernel.Density.Basic
public import Foundations.Measure.Integral.Density.Change
import Foundations.Measure.Integral.Simple.Approximation

set_option autoImplicit false

/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne

Adapted from Mathlib/Probability/Kernel/WithDensity.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny passes certificates explicitly. Its canonical rational increments
reconstruct every density, including the value top.
-/

namespace Foundations.Measure

open Foundations.Real

universe u v

namespace Kernel

variable {alpha : Type u} {beta : Type v}
  {source : Space alpha} {target : Space beta}

/-- Integrating against a reweighted kernel multiplies the integrand by its
density before integrating against the original kernel. -/
public theorem lintegral_withDensity
    (kernel : Kernel source target) (kernelFinite : IsSFinite kernel)
    {density : alpha → beta → ENNReal}
    (densityMeasurable : ENNRealMeasurable (Space.product source target)
      (fun pair => density pair.1 pair.2))
    (input : alpha) {integrand : beta → ENNReal}
    (integrandMeasurable : ENNRealMeasurable target integrand) :
    lintegral
        (kernel.withDensity kernelFinite density densityMeasurable input)
        integrand =
      lintegral (kernel input) (fun output =>
        ENNReal.mul (density input output) (integrand output)) := by
  rw [withDensity_apply]
  exact Foundations.Measure.lintegral_withDensity (kernel input)
    (jointlyMeasurable_slice densityMeasurable input) integrandMeasurable

/-- Reweighting depends only on the kernel and density, not on the chosen
s-finiteness or measurability certificates. -/
public theorem withDensity_congr
    {left right : Kernel source target}
    (leftFinite : IsSFinite left) (rightFinite : IsSFinite right)
    {leftDensity rightDensity : alpha → beta → ENNReal}
    (leftMeasurable : ENNRealMeasurable (Space.product source target)
      (fun pair => leftDensity pair.1 pair.2))
    (rightMeasurable : ENNRealMeasurable (Space.product source target)
      (fun pair => rightDensity pair.1 pair.2))
    (kernelEqual : left = right)
    (densityEqual : ∀ input output,
      leftDensity input output = rightDensity input output) :
    left.withDensity leftFinite leftDensity leftMeasurable =
      right.withDensity rightFinite rightDensity rightMeasurable := by
  subst right
  apply Kernel.ext
  intro input
  change (left input).withDensity (leftDensity input) =
    (left input).withDensity (rightDensity input)
  apply congrArg (Measure.withDensity (left input))
  funext output
  exact densityEqual input output

/-- Reweighting commutes with a countable sum in the kernel argument. -/
public theorem withDensity_sum
    (kernels : Nat → Kernel source target)
    (kernelsFinite : ∀ index, IsSFinite (kernels index))
    (density : alpha → beta → ENNReal)
    (densityMeasurable : ENNRealMeasurable (Space.product source target)
      (fun pair => density pair.1 pair.2)) :
    (Kernel.sum kernels).withDensity
        (IsSFinite.sum kernels kernelsFinite) density densityMeasurable =
      Kernel.sum (fun index =>
        (kernels index).withDensity (kernelsFinite index)
          density densityMeasurable) := by
  apply Kernel.ext_measurable
  intro input set setMeasurable
  calc
    (Kernel.sum kernels).withDensity
          (IsSFinite.sum kernels kernelsFinite) density densityMeasurable
          input set =
        lintegral
          ((Measure.sum (fun index => kernels index input)).restrict set)
          (density input) := by
      simpa only [Kernel.sum_apply] using
        withDensity_apply_set (Kernel.sum kernels)
          (IsSFinite.sum kernels kernelsFinite) density densityMeasurable
          input setMeasurable
    _ = lintegral
          (Measure.sum (fun index =>
            (kernels index input).restrict set))
          (density input) := by
      rw [Measure.restrict_sum
        (fun index => kernels index input) setMeasurable]
    _ = ENNReal.tsum (fun index =>
          lintegral ((kernels index input).restrict set)
            (density input)) :=
      lintegral_sum
        (fun index => (kernels index input).restrict set) (density input)
    _ = ENNReal.tsum (fun index =>
          (kernels index).withDensity (kernelsFinite index)
            density densityMeasurable input set) := by
      apply ENNReal.tsumCongr
      intro index
      exact (withDensity_apply_set (kernels index)
        (kernelsFinite index) density densityMeasurable input
        setMeasurable).symm
    _ = Kernel.sum (fun index =>
          (kernels index).withDensity (kernelsFinite index)
            density densityMeasurable) input set := by
      rw [Kernel.sum_apply, Measure.sum_apply _ setMeasurable]

/-- Reweighting commutes with a pointwise countable sum in the density
argument. -/
public theorem withDensity_tsum
    (kernel : Kernel source target) (kernelFinite : IsSFinite kernel)
    (densities : Nat → alpha → beta → ENNReal)
    (densitiesMeasurable : ∀ index,
      ENNRealMeasurable (Space.product source target)
        (fun pair => densities index pair.1 pair.2)) :
    kernel.withDensity kernelFinite
        (fun input output => ENNReal.tsum
          (fun index => densities index input output))
        (ENNRealMeasurable.tsum densitiesMeasurable) =
      Kernel.sum (fun index => kernel.withDensity kernelFinite
        (densities index) (densitiesMeasurable index)) := by
  apply Kernel.ext_measurable
  intro input set setMeasurable
  calc
    kernel.withDensity kernelFinite
          (fun current output => ENNReal.tsum
            (fun index => densities index current output))
          (ENNRealMeasurable.tsum densitiesMeasurable) input set =
        lintegral ((kernel input).restrict set)
          (fun output => ENNReal.tsum
            (fun index => densities index input output)) :=
      withDensity_apply_set kernel kernelFinite _ _ input setMeasurable
    _ = ENNReal.tsum (fun index =>
          lintegral ((kernel input).restrict set)
            (densities index input)) :=
      lintegral_tsum ((kernel input).restrict set)
        (fun index => densities index input)
        (fun index => jointlyMeasurable_slice
          (densitiesMeasurable index) input)
    _ = ENNReal.tsum (fun index =>
          kernel.withDensity kernelFinite (densities index)
            (densitiesMeasurable index) input set) := by
      apply ENNReal.tsumCongr
      intro index
      exact (withDensity_apply_set kernel kernelFinite
        (densities index) (densitiesMeasurable index) input
        setMeasurable).symm
    _ = Kernel.sum (fun index => kernel.withDensity kernelFinite
          (densities index) (densitiesMeasurable index)) input set := by
      rw [Kernel.sum_apply, Measure.sum_apply _ setMeasurable]

namespace IsFinite

/-- A uniformly bounded density preserves finiteness of a finite kernel. -/
public theorem withDensity_of_bounded {kernel : Kernel source target}
    (kernelFinite : IsFinite kernel)
    {density : alpha → beta → ENNReal}
    (densityMeasurable : ENNRealMeasurable (Space.product source target)
      (fun pair => density pair.1 pair.2))
    {bound : ENNReal} (boundFinite : ENNReal.Finite bound)
    (bounded : ∀ input output,
      ENNReal.le (density input output) bound) :
    IsFinite (kernel.withDensity kernelFinite.toSFinite
      density densityMeasurable) := by
  rcases kernelFinite.exists_bound with
    ⟨kernelBound, kernelBoundFinite, kernelBounded⟩
  refine ⟨⟨ENNReal.mul bound kernelBound,
    ENNReal.mulFinite boundFinite kernelBoundFinite, ?_⟩⟩
  intro input
  rw [Kernel.withDensity_apply,
    (kernel input).withDensity_apply (density input) target.univ,
    (kernel input).restrict_univ]
  exact ENNReal.leTrans
    (lintegral_mono (kernel input) (bounded input)) (by
      rw [lintegral_const]
      exact ENNReal.mulLeMulLeft (kernelBounded input) bound)

end IsFinite

private noncomputable def densityIncrement
    (density : alpha → beta → ENNReal)
    (densityMeasurable : ENNRealMeasurable (Space.product source target)
      (fun pair => density pair.1 pair.2))
    (index : Nat) : alpha → beta → ENNReal :=
  fun input output =>
    SimpleFunction.increment (fun pair => density pair.1 pair.2)
      densityMeasurable index (input, output)

private theorem densityIncrement_measurable
    (density : alpha → beta → ENNReal)
    (densityMeasurable : ENNRealMeasurable (Space.product source target)
      (fun pair => density pair.1 pair.2))
    (index : Nat) :
    ENNRealMeasurable (Space.product source target)
      (fun pair => densityIncrement density densityMeasurable index
        pair.1 pair.2) := by
  simpa only [densityIncrement] using
    SimpleFunction.increment_measurable
      (fun pair : alpha × beta => density pair.1 pair.2)
      densityMeasurable index

private theorem densityIncrement_bounded
    (density : alpha → beta → ENNReal)
    (densityMeasurable : ENNRealMeasurable (Space.product source target)
      (fun pair => density pair.1 pair.2))
    (index : Nat) :
    ∃ bound, ENNReal.Finite bound ∧ ∀ input output,
      ENNReal.le
        (densityIncrement density densityMeasurable index input output)
        bound := by
  rcases SimpleFunction.increment_uniformly_bounded
      (fun pair : alpha × beta => density pair.1 pair.2)
      densityMeasurable index with
    ⟨bound, boundFinite, bounded⟩
  refine ⟨bound, boundFinite, ?_⟩
  intro input output
  simpa only [densityIncrement] using bounded (input, output)

private theorem tsum_densityIncrement
    (density : alpha → beta → ENNReal)
    (densityMeasurable : ENNRealMeasurable (Space.product source target)
      (fun pair => density pair.1 pair.2))
    (input : alpha) (output : beta) :
    ENNReal.tsum (fun index =>
      densityIncrement density densityMeasurable index input output) =
        density input output := by
  simpa only [densityIncrement] using SimpleFunction.tsum_increments
    (fun pair => density pair.1 pair.2) densityMeasurable (input, output)

namespace IsFinite

/-- Reweighting a finite kernel by any jointly measurable density is
s-finite, even when the density attains top. -/
public noncomputable def withDensity {kernel : Kernel source target}
    (kernelFinite : IsFinite kernel)
    (density : alpha → beta → ENNReal)
    (densityMeasurable : ENNRealMeasurable (Space.product source target)
      (fun pair => density pair.1 pair.2)) :
    IsSFinite (kernel.withDensity kernelFinite.toSFinite
      density densityMeasurable) := by
  let increments : Nat → alpha → beta → ENNReal :=
    fun index => densityIncrement density densityMeasurable index
  have incrementsMeasurable : ∀ index,
      ENNRealMeasurable (Space.product source target)
        (fun pair => increments index pair.1 pair.2) :=
    fun index => densityIncrement_measurable
      density densityMeasurable index
  let weighted : Nat → Kernel source target := fun index =>
    kernel.withDensity kernelFinite.toSFinite
      (increments index) (incrementsMeasurable index)
  have weightedFinite : ∀ index, IsFinite (weighted index) := by
    intro index
    rcases densityIncrement_bounded density densityMeasurable index with
      ⟨bound, boundFinite, bounded⟩
    exact withDensity_of_bounded kernelFinite
      (incrementsMeasurable index) boundFinite bounded
  let sumFinite : IsSFinite (Kernel.sum weighted) :=
    IsSFinite.sum weighted
      (fun index => (weightedFinite index).toSFinite)
  refine {
    components := sumFinite.components
    finite := sumFinite.finite
    sum_eq := sumFinite.sum_eq.trans ?_
  }
  calc
    Kernel.sum weighted =
        kernel.withDensity kernelFinite.toSFinite
          (fun input output => ENNReal.tsum
            (fun index => increments index input output))
          (ENNRealMeasurable.tsum incrementsMeasurable) := by
      simpa only [weighted] using
        (withDensity_tsum kernel kernelFinite.toSFinite increments
          incrementsMeasurable).symm
    _ = kernel.withDensity kernelFinite.toSFinite
          density densityMeasurable :=
      withDensity_congr kernelFinite.toSFinite kernelFinite.toSFinite
        (ENNRealMeasurable.tsum incrementsMeasurable) densityMeasurable rfl
        (fun input output =>
          tsum_densityIncrement density densityMeasurable input output)

end IsFinite

namespace IsSFinite

/-- S-finite kernels are closed under arbitrary jointly measurable
extended-nonnegative densities. -/
public noncomputable def withDensity {kernel : Kernel source target}
    (kernelFinite : IsSFinite kernel)
    (density : alpha → beta → ENNReal)
    (densityMeasurable : ENNRealMeasurable (Space.product source target)
      (fun pair => density pair.1 pair.2)) :
    IsSFinite (kernel.withDensity kernelFinite density densityMeasurable) := by
  let componentFinite : ∀ index,
      IsSFinite ((kernelFinite.components index).withDensity
        (kernelFinite.finite index).toSFinite density densityMeasurable) :=
    fun index => IsFinite.withDensity (kernelFinite.finite index)
      density densityMeasurable
  let weighted : Nat → Kernel source target := fun index =>
    (kernelFinite.components index).withDensity
      (kernelFinite.finite index).toSFinite density densityMeasurable
  let sumFinite : IsSFinite (Kernel.sum weighted) :=
    IsSFinite.sum weighted componentFinite
  let componentsFinite : ∀ index,
      IsSFinite (kernelFinite.components index) :=
    fun index => (kernelFinite.finite index).toSFinite
  let baseSumFinite : IsSFinite (Kernel.sum kernelFinite.components) :=
    IsSFinite.sum kernelFinite.components componentsFinite
  refine {
    components := sumFinite.components
    finite := sumFinite.finite
    sum_eq := sumFinite.sum_eq.trans ?_
  }
  calc
    Kernel.sum weighted =
        (Kernel.sum kernelFinite.components).withDensity
          baseSumFinite density densityMeasurable := by
      simpa only [weighted, baseSumFinite, componentsFinite] using
        (withDensity_sum kernelFinite.components componentsFinite
          density densityMeasurable).symm
    _ = kernel.withDensity kernelFinite density densityMeasurable :=
      withDensity_congr baseSumFinite kernelFinite densityMeasurable
        densityMeasurable kernelFinite.sum_eq (fun _ _ => rfl)

end IsSFinite

end Kernel

end Foundations.Measure
