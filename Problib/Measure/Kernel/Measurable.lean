module

public import Problib.Measure.Kernel.Measurable.Section
public import Problib.Measure.Kernel.Composition.Bind.Core
public import Problib.Measure.Integral.Lebesgue.Algebra
import Problib.Measure.Integral.Simple.Induction

set_option autoImplicit false

/-
Copyright (c) 2017 Johannes Hölzl, Mario Carneiro.
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Copyright (c) 2025 Rémy Degenne, Lorenzo Luccioli.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Rémy Degenne, Lorenzo Luccioli

Adapted from Mathlib/Probability/Kernel/MeasurableLIntegral.lean,
Mathlib/MeasureTheory/Measure/GiryMonad.lean, and
Mathlib/Probability/Kernel/Composition/MeasureComp.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny uses explicit measurable spaces and constructive s-finite witnesses.
-/

namespace Problib.Measure

open Problib.Real

universe u v

namespace Kernel

variable {alpha : Type u} {beta : Type v}
  {source : Space alpha} {target : Space beta}

/-- Integrating a fixed measurable function against any kernel gives a
measurable function on the kernel source. -/
public theorem lintegral_measurable (kernel : Kernel source target)
    {function : beta → ENNReal}
    (functionMeasurable : ENNRealMeasurable target function) :
    ENNRealMeasurable source
      (fun input => lintegral (kernel input) function) := by
  refine ENNRealMeasurable.induction
    (motive := fun current => ENNRealMeasurable source
      (fun input => lintegral (kernel input) current)) ?_ ?_ ?_ ?_
    functionMeasurable
  · have equal : (fun input => lintegral (kernel input)
        (fun _ => ENNReal.zero)) = (fun _ => ENNReal.zero) := by
      funext input
      exact lintegral_zero (kernel input)
    rw [equal]
    exact ENNRealMeasurable.constant source ENNReal.zero
  · intro region regionMeasurable value
    have scaled := ENNRealMeasurable.const_mul value
      (kernel.measurable regionMeasurable)
    have equal : (fun input => lintegral (kernel input)
        (ennrealIndicator region (fun _ => value))) =
        (fun input => ENNReal.mul value (kernel input region)) := by
      funext input
      rw [lintegral_indicator (kernel input) region regionMeasurable,
        lintegral_const, Measure.restrict_apply_univ]
    rw [equal]
    exact scaled
  · intro left right leftMeasurable rightMeasurable
      leftIntegralMeasurable rightIntegralMeasurable
    have sumMeasurable := ENNRealMeasurable.add
      leftIntegralMeasurable rightIntegralMeasurable
    have equal : (fun input => lintegral (kernel input)
        (fun value => ENNReal.add (left value) (right value))) =
        (fun input => ENNReal.add
          (lintegral (kernel input) left)
          (lintegral (kernel input) right)) := by
      funext input
      exact lintegral_add (kernel input) leftMeasurable rightMeasurable
    rw [equal]
    exact sumMeasurable
  · intro functions functionsMeasurable functionsMonotone
      integralMeasurable
    have supremumMeasurable := ENNRealMeasurable.iSup integralMeasurable
    have equal : (fun input => lintegral (kernel input)
        (fun value => ENNReal.iSup
          (fun index => functions index value))) =
        (fun input => ENNReal.iSup (fun index =>
          lintegral (kernel input) (functions index))) := by
      funext input
      exact lintegral_iSup (kernel input) functions functionsMeasurable
        (fun stage value => functionsMonotone value stage)
    rw [equal]
    exact supremumMeasurable

/-- Integrating a jointly measurable function against an s-finite kernel is
measurable in the source parameter. -/
public theorem lintegral_measurable_joint
    (kernel : Kernel source target) (kernelFinite : IsSFinite kernel)
    {function : alpha → beta → ENNReal}
    (functionMeasurable : ENNRealMeasurable (Space.product source target)
      (fun value => function value.1 value.2)) :
    ENNRealMeasurable source
      (fun input => lintegral (kernel input) (function input)) := by
  refine ENNRealMeasurable.induction
    (motive := fun current => ENNRealMeasurable source
      (fun input => lintegral (kernel input)
        (fun value => current (input, value)))) ?_ ?_ ?_ ?_
    functionMeasurable
  · have equal : (fun input => lintegral (kernel input)
        (fun _ => ENNReal.zero)) = (fun _ => ENNReal.zero) := by
      funext input
      exact lintegral_zero (kernel input)
    rw [equal]
    exact ENNRealMeasurable.constant source ENNReal.zero
  · intro region regionMeasurable value
    have sectionMeasurable := section_apply_measurable kernel kernelFinite
      regionMeasurable
    have scaled := ENNRealMeasurable.const_mul value sectionMeasurable
    have equal : (fun input => lintegral (kernel input)
        (fun targetValue => ennrealIndicator region
          (fun _ => value) (input, targetValue))) =
        (fun input => ENNReal.mul value
          (kernel input (verticalSection region input))) := by
      funext input
      change lintegral (kernel input)
          (ennrealIndicator (verticalSection region input)
            (fun _ => value)) = _
      rw [lintegral_indicator (kernel input)
        (verticalSection region input)
        (verticalSection_measurable regionMeasurable input),
        lintegral_const, Measure.restrict_apply_univ]
    rw [equal]
    exact scaled
  · intro left right leftMeasurable rightMeasurable
      leftIntegralMeasurable rightIntegralMeasurable
    have sumMeasurable := ENNRealMeasurable.add
      leftIntegralMeasurable rightIntegralMeasurable
    have equal : (fun input => lintegral (kernel input)
        (fun value => ENNReal.add (left (input, value))
          (right (input, value)))) =
        (fun input => ENNReal.add
          (lintegral (kernel input) (fun value => left (input, value)))
          (lintegral (kernel input) (fun value => right (input, value)))) := by
      funext input
      exact lintegral_add (kernel input)
        (ENNRealMeasurable.comp leftMeasurable
          (Space.pair_measurable (vertical_map_measurable input)
            (MeasurableMap.identity target)))
        (ENNRealMeasurable.comp rightMeasurable
          (Space.pair_measurable (vertical_map_measurable input)
            (MeasurableMap.identity target)))
    rw [equal]
    exact sumMeasurable
  · intro functions functionsMeasurable functionsMonotone
      integralMeasurable
    have supremumMeasurable := ENNRealMeasurable.iSup integralMeasurable
    have equal : (fun input => lintegral (kernel input)
        (fun value => ENNReal.iSup
          (fun index => functions index (input, value)))) =
        (fun input => ENNReal.iSup (fun index =>
          lintegral (kernel input)
            (fun value => functions index (input, value)))) := by
      funext input
      exact lintegral_iSup (kernel input)
        (fun index value => functions index (input, value))
        (fun index => ENNRealMeasurable.comp (functionsMeasurable index)
          (Space.pair_measurable (vertical_map_measurable input)
            (MeasurableMap.identity target)))
        (fun stage value => functionsMonotone (input, value) stage)
    rw [equal]
    exact supremumMeasurable

end Kernel

namespace Measure

variable {alpha : Type u} {beta : Type v}
  {source : Space alpha} {target : Space beta}

/-- Iterated integration computes integration against bind. -/
public theorem lintegral_bind (measure : Measure source)
    (kernel : Kernel source target) {function : beta → ENNReal}
    (functionMeasurable : ENNRealMeasurable target function) :
    lintegral (measure.bind kernel) function =
      lintegral measure (fun input => lintegral (kernel input) function) := by
  refine ENNRealMeasurable.induction
    (motive := fun current =>
      lintegral (measure.bind kernel) current =
        lintegral measure (fun input => lintegral (kernel input) current))
    ?_ ?_ ?_ ?_ functionMeasurable
  · calc
      lintegral (measure.bind kernel) (fun _ => ENNReal.zero) =
          ENNReal.zero := lintegral_zero _
      _ = lintegral measure (fun _ => ENNReal.zero) :=
        (lintegral_zero measure).symm
      _ = lintegral measure (fun input =>
          lintegral (kernel input) (fun _ => ENNReal.zero)) := by
        apply lintegral_congr
        intro input
        exact (lintegral_zero (kernel input)).symm
  · intro region regionMeasurable value
    calc
      lintegral (measure.bind kernel)
          (ennrealIndicator region (fun _ => value)) =
          lintegral ((measure.bind kernel).restrict region)
            (fun _ => value) :=
        lintegral_indicator _ region regionMeasurable _
      _ = ENNReal.mul value ((measure.bind kernel).restrict region Set.univ) :=
        lintegral_const _ value
      _ = ENNReal.mul value (measure.bind kernel region) := by
        rw [(measure.bind kernel).restrict_apply_univ]
      _ = ENNReal.mul value
          (lintegral measure (fun input => kernel input region)) := by
        rw [bind_apply measure kernel regionMeasurable]
      _ = lintegral measure
          (fun input => ENNReal.mul value (kernel input region)) :=
        (lintegral_smul measure value
          (kernel.measurable regionMeasurable)).symm
      _ = lintegral measure (fun input => lintegral (kernel input)
          (ennrealIndicator region (fun _ => value))) := by
        apply lintegral_congr
        intro input
        symm
        calc
          lintegral (kernel input)
              (ennrealIndicator region (fun _ => value)) =
              lintegral ((kernel input).restrict region)
                (fun _ => value) :=
            lintegral_indicator _ region regionMeasurable _
          _ = ENNReal.mul value
              ((kernel input).restrict region Set.univ) :=
            lintegral_const _ value
          _ = ENNReal.mul value (kernel input region) := by
            rw [(kernel input).restrict_apply_univ]
  · intro left right leftMeasurable rightMeasurable
      leftInduction rightInduction
    calc
      lintegral (measure.bind kernel)
          (fun input => ENNReal.add (left input) (right input)) =
          ENNReal.add
            (lintegral (measure.bind kernel) left)
            (lintegral (measure.bind kernel) right) :=
        lintegral_add _ leftMeasurable rightMeasurable
      _ = ENNReal.add
          (lintegral measure (fun input => lintegral (kernel input) left))
          (lintegral measure (fun input => lintegral (kernel input) right)) := by
        rw [leftInduction, rightInduction]
      _ = lintegral measure (fun input => ENNReal.add
          (lintegral (kernel input) left)
          (lintegral (kernel input) right)) :=
        (lintegral_add measure
          (kernel.lintegral_measurable leftMeasurable)
          (kernel.lintegral_measurable rightMeasurable)).symm
      _ = lintegral measure (fun input =>
          lintegral (kernel input)
            (fun output => ENNReal.add (left output) (right output))) := by
        apply lintegral_congr
        intro input
        exact (lintegral_add (kernel input)
          leftMeasurable rightMeasurable).symm
  · intro functions functionsMeasurable functionsMonotone induction
    let iterated := fun index input =>
      lintegral (kernel input) (functions index)
    have iteratedMeasurable : ∀ index,
        ENNRealMeasurable source (iterated index) :=
      fun index => kernel.lintegral_measurable
        (functionsMeasurable index)
    have iteratedMonotone : ∀ stage input,
        ENNReal.le (iterated stage input) (iterated (stage + 1) input) := by
      intro stage input
      exact lintegral_mono (kernel input)
        (fun output => functionsMonotone output stage)
    calc
      lintegral (measure.bind kernel) (fun input =>
          ENNReal.iSup (fun index => functions index input)) =
          ENNReal.iSup (fun index =>
            lintegral (measure.bind kernel) (functions index)) :=
        lintegral_iSup _ functions functionsMeasurable
          (fun stage input => functionsMonotone input stage)
      _ = ENNReal.iSup (fun index => lintegral measure
          (fun input => lintegral (kernel input) (functions index))) := by
        apply congrArg ENNReal.iSup
        funext index
        exact induction index
      _ = lintegral measure (fun input =>
          ENNReal.iSup (fun index => iterated index input)) :=
        (lintegral_iSup measure iterated iteratedMeasurable
          iteratedMonotone).symm
      _ = lintegral measure (fun input => lintegral (kernel input)
          (fun output => ENNReal.iSup
            (fun index => functions index output))) := by
        apply lintegral_congr
        intro input
        exact (lintegral_iSup (kernel input) functions
          functionsMeasurable
          (fun stage output => functionsMonotone output stage)).symm

end Measure

end Problib.Measure
