module

public import Foundations.Measure.Kernel.Measurable
public import Foundations.Measure.Integral.Density.Basic

set_option autoImplicit false

/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne

Adapted from Mathlib/Probability/Kernel/WithDensity.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny passes measurability and s-finiteness as explicit certificates.
-/

namespace Foundations.Measure

open Foundations.Real

universe u v

namespace Kernel

variable {alpha : Type u} {beta : Type v}
  {source : Space alpha} {target : Space beta}

private theorem constantMeasurableMap (value : alpha) :
    MeasurableMap target source (fun _ => value) := by
  intro set _
  classical
  by_cases member : set value
  · have equal : Set.preimage (fun _ : beta => value) set = Set.univ := by
      apply Set.ext
      intro input
      exact ⟨fun _ => True.intro, fun _ => member⟩
    rw [equal]
    exact target.univ
  · have equal : Set.preimage (fun _ : beta => value) set = Set.empty := by
      apply Set.ext
      intro input
      exact ⟨fun present => False.elim (member present), False.elim⟩
    rw [equal]
    exact target.empty

public theorem jointlyMeasurable_slice
    {density : alpha → beta → ENNReal}
    (densityMeasurable : ENNRealMeasurable (Space.product source target)
      (fun pair => density pair.1 pair.2))
    (input : alpha) :
    ENNRealMeasurable target (density input) := by
  have sectionMeasurable : MeasurableMap target
      (Space.product source target) (fun output => (input, output)) :=
    Space.pair_measurable (constantMeasurableMap input)
      (MeasurableMap.identity target)
  simpa only using densityMeasurable.comp sectionMeasurable

/-- Reweight every measure in an s-finite kernel by a jointly measurable
extended-nonnegative density. -/
@[expose] public noncomputable def withDensity
    (kernel : Kernel source target) (kernelFinite : IsSFinite kernel)
    (density : alpha → beta → ENNReal)
    (densityMeasurable : ENNRealMeasurable (Space.product source target)
      (fun pair => density pair.1 pair.2)) :
    Kernel source target where
  toFun := fun input => (kernel input).withDensity (density input)
  measurable := by
    intro set setMeasurable
    let region : Set (alpha × beta) := Set.preimage Prod.snd set
    have regionMeasurable : (Space.product source target).Measurable region :=
      Space.second_measurable source target setMeasurable
    have indicatorMeasurable :
        ENNRealMeasurable (Space.product source target)
          (ennrealIndicator region
            (fun pair => density pair.1 pair.2)) :=
      densityMeasurable.indicator regionMeasurable
    have jointMeasurable :
        ENNRealMeasurable (Space.product source target)
          (fun pair => ennrealIndicator set
            (density pair.1) pair.2) := by
      have equal :
          (fun pair => ennrealIndicator set
            (density pair.1) pair.2) =
            ennrealIndicator region
              (fun pair => density pair.1 pair.2) := by
        classical
        funext pair
        unfold ennrealIndicator ennrealPiecewise region Set.preimage
        rfl
      rw [equal]
      exact indicatorMeasurable
    have integralMeasurable := kernel.lintegral_measurable_joint kernelFinite
      (function := fun input output =>
        ennrealIndicator set (density input) output) jointMeasurable
    have equal :
        (fun input => (kernel input).withDensity (density input) set) =
          (fun input => lintegral (kernel input)
            (fun output => ennrealIndicator set (density input) output)) := by
      funext input
      rw [(kernel input).withDensity_apply (density input) setMeasurable,
        lintegral_indicator (kernel input) set setMeasurable]
    rw [equal]
    exact integralMeasurable

@[simp] public theorem withDensity_apply
    (kernel : Kernel source target) (kernelFinite : IsSFinite kernel)
    (density : alpha → beta → ENNReal)
    (densityMeasurable : ENNRealMeasurable (Space.product source target)
      (fun pair => density pair.1 pair.2))
    (input : alpha) :
    kernel.withDensity kernelFinite density densityMeasurable input =
      (kernel input).withDensity (density input) :=
  rfl

public theorem withDensity_apply_set
    (kernel : Kernel source target) (kernelFinite : IsSFinite kernel)
    (density : alpha → beta → ENNReal)
    (densityMeasurable : ENNRealMeasurable (Space.product source target)
      (fun pair => density pair.1 pair.2))
    (input : alpha) {set : Set beta}
    (setMeasurable : target.Measurable set) :
    kernel.withDensity kernelFinite density densityMeasurable input set =
      lintegral ((kernel input).restrict set) (density input) := by
  rw [withDensity_apply, (kernel input).withDensity_apply
    (density input) setMeasurable]

end Kernel

end Foundations.Measure
