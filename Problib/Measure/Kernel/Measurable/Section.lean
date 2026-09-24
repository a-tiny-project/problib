module

public import Problib.Measure.Kernel.Basic
public import Problib.Measure.Product.Generator
import Problib.Measure.Additive.Partition
import Problib.Measure.Dynkin.PiLambda
import Problib.Measure.Extended.Algebra.Binary
import Problib.Measure.Extended.Limit

set_option autoImplicit false

/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne

Adapted from Mathlib/Probability/Kernel/MeasurableLIntegral.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny proves measurable vertical sections through its explicit pi-lambda
theorem and passes s-finite decompositions as constructive data.
-/

namespace Problib.Measure

open Problib.Real

universe u v

namespace Kernel

variable {alpha : Type u} {beta : Type v}
  {source : Space alpha} {target : Space beta}

@[expose] public def verticalSection (set : Set (alpha × beta))
    (input : alpha) : Set beta :=
  Set.preimage (fun value => (input, value)) set

public theorem vertical_map_measurable (input : alpha) :
    MeasurableMap target source (fun _ => input) := by
  intro set setMeasurable
  classical
  by_cases member : set input
  · have equal : Set.preimage (fun _ : beta => input) set = Set.univ := by
      apply Set.ext
      intro value
      exact ⟨fun _ => True.intro, fun _ => member⟩
    rw [equal]
    exact target.univ
  · have equal : Set.preimage (fun _ : beta => input) set = Set.empty := by
      apply Set.ext
      intro value
      exact ⟨fun present => False.elim (member present), False.elim⟩
    rw [equal]
    exact target.empty

public theorem verticalSection_measurable {set : Set (alpha × beta)}
    (setMeasurable : (Space.product source target).Measurable set)
    (input : alpha) : target.Measurable (verticalSection set input) := by
  exact Space.pair_measurable (vertical_map_measurable input)
    (MeasurableMap.identity target) setMeasurable

private theorem verticalSection_complement_apply
    (kernel : Kernel source target) (kernelFinite : ∀ input, Measure.IsFinite (kernel input))
    {set : Set (alpha × beta)}
    (setMeasurable : (Space.product source target).Measurable set)
    (input : alpha) :
    kernel input (verticalSection (Set.complement set) input) =
      ENNReal.sub (kernel input Set.univ)
        (kernel input (verticalSection set input)) := by
  change kernel input (Set.complement (verticalSection set input)) = _
  rw [← (kernel input).add_complement
    (verticalSection_measurable setMeasurable input)]
  exact (ENNReal.add_sub_cancel_left
    ((kernelFinite input).apply (verticalSection set input))).symm

/-- For a kernel with finite fibers, evaluating measurable vertical sections is
a measurable function of the first coordinate. -/
public theorem section_apply_measurable_of_finite_fibers
    (kernel : Kernel source target) (kernelFinite : ∀ input, Measure.IsFinite (kernel input))
    {set : Set (alpha × beta)}
    (setMeasurable : (Space.product source target).Measurable set) :
    ENNRealMeasurable source
      (fun input => kernel input (verticalSection set input)) := by
  let property : DynkinSystem (alpha × beta) := {
    Contains current :=
      (Space.product source target).Measurable current ∧
        ENNRealMeasurable source
          (fun input => kernel input (verticalSection current input))
    empty := by
      constructor
      · exact (Space.product source target).empty
      · have equal : (fun input =>
            kernel input (verticalSection Set.empty input)) =
            (fun _ => ENNReal.zero) := by
          funext input
          exact (kernel input).empty_apply
        rw [equal]
        exact ENNRealMeasurable.constant source ENNReal.zero
    complement := by
      rintro current ⟨currentMeasurable, currentApplyMeasurable⟩
      constructor
      · exact (Space.product source target).complement currentMeasurable
      · have totalMeasurable := kernel.measurable target.univ
        have differenceMeasurable :=
          ENNRealMeasurable.sub totalMeasurable currentApplyMeasurable
        have equal : (fun input => kernel input
            (verticalSection (Set.complement current) input)) =
            (fun input => ENNReal.sub (kernel input Set.univ)
              (kernel input (verticalSection current input))) := by
          funext input
          exact verticalSection_complement_apply kernel kernelFinite
            currentMeasurable input
        rw [equal]
        exact differenceMeasurable
    iUnion := by
      intro sets disjoint contains
      have setsMeasurable : ∀ index,
          (Space.product source target).Measurable (sets index) :=
        fun index => (contains index).1
      constructor
      · exact (Space.product source target).iUnion setsMeasurable
      · have termsMeasurable : ∀ index, ENNRealMeasurable source
            (fun input => kernel input
              (verticalSection (sets index) input)) :=
          fun index => (contains index).2
        have seriesMeasurable := ENNRealMeasurable.tsum termsMeasurable
        have equal : (fun input => kernel input
            (verticalSection (Set.iUnion sets) input)) =
            (fun input => ENNReal.tsum (fun index =>
              kernel input (verticalSection (sets index) input))) := by
          funext input
          apply (kernel input).iUnion_disjoint
          · intro index
            exact verticalSection_measurable (setsMeasurable index) input
          · intro first second different value firstMember secondMember
            exact disjoint first second different firstMember secondMember
        rw [equal]
        exact seriesMeasurable
  }
  have generated :
      (DynkinSystem.generated (Space.Rectangle source target)).Contains set :=
    (DynkinSystem.pi_lambda (Space.rectangle_piSystem source target)).mp (by
      rw [← Space.product_eq_generated_rectangles source target]
      exact setMeasurable)
  have contained : property.Contains set :=
    DynkinSystem.generated_minimal property (by
      intro rectangle rectangleMember
      rcases rectangleMember with
        ⟨leftSet, rightSet, leftMeasurable, rightMeasurable, rfl⟩
      constructor
      · exact Space.product_set_measurable source target
          leftMeasurable rightMeasurable
      · have selected := ENNRealMeasurable.piecewise leftMeasurable
          (kernel.measurable rightMeasurable)
          (ENNRealMeasurable.constant source ENNReal.zero)
        have equal : (fun input => kernel input
            (verticalSection (Set.product leftSet rightSet) input)) =
            ennrealPiecewise leftSet (fun input => kernel input rightSet)
              (fun _ => ENNReal.zero) := by
          classical
          funext input
          by_cases member : leftSet input
          · have sectionEqual :
                verticalSection (Set.product leftSet rightSet) input =
                  rightSet := by
              apply Set.ext
              intro value
              exact ⟨fun present => present.2,
                fun present => ⟨member, present⟩⟩
            rw [sectionEqual]
            simp [ennrealPiecewise, member]
          · have sectionEqual :
                verticalSection (Set.product leftSet rightSet) input =
                  Set.empty := by
              apply Set.ext
              intro value
              exact ⟨fun present => False.elim (member present.1),
                False.elim⟩
            rw [sectionEqual, (kernel input).empty_apply]
            simp [ennrealPiecewise, member]
        rw [equal]
        exact selected) generated
  exact contained.2

/-- S-finite kernels retain measurable evaluation on measurable vertical
sections by summing their finite components. -/
public theorem section_apply_measurable
    (kernel : Kernel source target) (kernelFinite : IsSFinite kernel)
    {set : Set (alpha × beta)}
    (setMeasurable : (Space.product source target).Measurable set) :
    ENNRealMeasurable source
      (fun input => kernel input (verticalSection set input)) := by
  have termsMeasurable : ∀ index, ENNRealMeasurable source
      (fun input => kernelFinite.components index input
        (verticalSection set input)) :=
    fun index => section_apply_measurable_of_finite_fibers
      (kernelFinite.components index)
      (fun input => (kernelFinite.finite index).measure input) setMeasurable
  have seriesMeasurable := ENNRealMeasurable.tsum termsMeasurable
  have equal : (fun input => kernel input (verticalSection set input)) =
      (fun input => ENNReal.tsum (fun index =>
        kernelFinite.components index input
          (verticalSection set input))) := by
    funext input
    calc
      kernel input (verticalSection set input) =
          Kernel.sum kernelFinite.components input
            (verticalSection set input) := by
        exact congrArg
          (fun current => current input (verticalSection set input))
          kernelFinite.sum_eq.symm
      _ = ENNReal.tsum (fun index =>
          kernelFinite.components index input
            (verticalSection set input)) := by
        rw [Kernel.sum_apply, Measure.sum_apply]
        exact verticalSection_measurable setMeasurable input
  rw [equal]
  exact seriesMeasurable

end Kernel

end Problib.Measure
