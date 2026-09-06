module

public import Foundations.Measure.Kernel.Composition.Bind.Core
public import Foundations.Measure.Product
import Foundations.Measure.Kernel.Measurable.Section
import Foundations.Measure.Integral.Lebesgue.Algebra

set_option autoImplicit false

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Adapted from Mathlib/MeasureTheory/Measure/Prod.lean and
Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny keeps the s-finite certificate explicit. The first measure in a
semiproduct is unrestricted.
-/

namespace Foundations.Measure

open Foundations.Real

universe u v

namespace Kernel

variable {alpha : Type u} {beta : Type v}
  {source : Space alpha} {target : Space beta}

private theorem constant_measurable (value : alpha) :
    MeasurableMap target source (fun _ => value) := by
  intro set setMeasurable
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

public theorem pair_left_measurable (input : alpha) :
    MeasurableMap target (Space.product source target)
      (fun value => (input, value)) :=
  Space.pair_measurable (constant_measurable input)
    (MeasurableMap.identity target)

/-- Attach each kernel output to the input that selected it. -/
@[expose] public noncomputable def attach (kernel : Kernel source target)
    (kernelFinite : IsSFinite kernel) :
    Kernel source (Space.product source target) where
  toFun := fun input =>
    (kernel input).map (fun value => (input, value))
      (pair_left_measurable (source := source) (target := target) input)
  measurable := by
    intro set setMeasurable
    have sections := section_apply_measurable kernel kernelFinite setMeasurable
    have equal : (fun input =>
        ((kernel input).map (fun value => (input, value))
          (pair_left_measurable (source := source)
            (target := target) input)) set) =
        (fun input => kernel input
          (Set.preimage (fun value => (input, value)) set)) := by
      funext input
      exact (kernel input).map_apply (fun value => (input, value))
        (pair_left_measurable (source := source)
          (target := target) input) setMeasurable
    rw [equal]
    exact sections

@[simp] public theorem attach_apply (kernel : Kernel source target)
    (kernelFinite : IsSFinite kernel) (input : alpha) :
    attach kernel kernelFinite input =
      (kernel input).map (fun value => (input, value))
        (pair_left_measurable (source := source)
          (target := target) input) :=
  rfl

namespace IsFinite

/-- Attaching the source coordinate preserves a uniform finite bound. -/
public theorem attach {kernel : Kernel source target}
    (finite : IsFinite kernel) :
    IsFinite (Kernel.attach kernel finite.toSFinite) := by
  rcases finite.exists_bound with ⟨bound, boundFinite, bounded⟩
  refine ⟨⟨bound, boundFinite, ?_⟩⟩
  intro input
  rw [Kernel.attach_apply,
    (kernel input).map_apply (fun value => (input, value))
      (pair_left_measurable (source := source)
        (target := target) input)
      (Space.product source target).univ,
    Set.preimage_univ]
  exact bounded input

end IsFinite

namespace IsSFinite

/-- Attaching the source coordinate preserves s-finiteness. -/
public noncomputable def attach {kernel : Kernel source target}
    (finite : IsSFinite kernel) :
    IsSFinite (Kernel.attach kernel finite) where
  components := fun index => Kernel.attach (finite.components index)
    (finite.finite index).toSFinite
  finite := fun index => (finite.finite index).attach
  sum_eq := by
    apply Kernel.ext
    intro input
    rw [Kernel.sum_apply]
    have componentEqual : (fun index =>
        Kernel.attach (finite.components index)
          (finite.finite index).toSFinite input) =
        (fun index => (finite.components index input).map
          (fun value => (input, value))
          (pair_left_measurable (source := source)
            (target := target) input)) := by
      funext index
      exact Kernel.attach_apply (finite.components index)
        (finite.finite index).toSFinite input
    rw [componentEqual,
      ← Measure.map_sum
        (fun index => finite.components index input)
        (fun value => (input, value))
        (pair_left_measurable (source := source)
          (target := target) input)]
    have equal := congrArg (fun current => current input) finite.sum_eq
    simpa only [Kernel.sum_apply, Kernel.attach_apply] using
      congrArg (fun measure => measure.map
        (fun value => (input, value))
        (pair_left_measurable (source := source)
          (target := target) input)) equal

end IsSFinite

end Kernel

namespace Measure

variable {alpha : Type u} {beta : Type v}
  {source : Space alpha} {target : Space beta}

/-- The semiproduct samples the first measure and then its s-finite kernel. -/
@[expose] public noncomputable def semiproduct
    (measure : Measure source) (kernel : Kernel source target)
    (kernelFinite : Kernel.IsSFinite kernel) :
    Measure (Space.product source target) :=
  measure.bind (Kernel.attach kernel kernelFinite)

public theorem semiproduct_apply (measure : Measure source)
    (kernel : Kernel source target) (kernelFinite : Kernel.IsSFinite kernel)
    {set : Set (alpha × beta)}
    (setMeasurable : (Space.product source target).Measurable set) :
    semiproduct measure kernel kernelFinite set =
      lintegral measure (fun input => kernel input
        (Set.preimage (fun value => (input, value)) set)) := by
  rw [semiproduct, bind_apply measure (Kernel.attach kernel kernelFinite)
      setMeasurable]
  apply lintegral_congr
  intro input
  rw [Kernel.attach_apply,
    (kernel input).map_apply (fun value => (input, value))
      (Kernel.pair_left_measurable (source := source)
        (target := target) input) setMeasurable]

public theorem semiproduct_apply_product (measure : Measure source)
    (kernel : Kernel source target) (kernelFinite : Kernel.IsSFinite kernel)
    {left : Set alpha} {right : Set beta}
    (leftMeasurable : source.Measurable left)
    (rightMeasurable : target.Measurable right) :
    semiproduct measure kernel kernelFinite (Set.product left right) =
      lintegral (measure.restrict left) (fun input => kernel input right) := by
  rw [semiproduct_apply measure kernel kernelFinite
      (Space.product_set_measurable source target
        leftMeasurable rightMeasurable),
    ← lintegral_indicator measure left leftMeasurable]
  apply lintegral_congr
  intro input
  classical
  by_cases member : left input
  · have sectionEqual :
        Set.preimage (fun value => (input, value))
          (Set.product left right) = right := by
      apply Set.ext
      intro value
      exact ⟨fun present => present.2,
        fun present => ⟨member, present⟩⟩
    rw [sectionEqual]
    simp [ennrealIndicator, ennrealPiecewise, member]
  · have sectionEqual :
        Set.preimage (fun value => (input, value))
          (Set.product left right) = Set.empty := by
      apply Set.ext
      intro value
      exact ⟨fun present => False.elim (member present.1), False.elim⟩
    rw [sectionEqual, (kernel input).empty_apply]
    simp [ennrealIndicator, ennrealPiecewise, member]

/-- A reverse semiproduct samples the second coordinate and returns the
coordinates in their original order. -/
@[expose] public noncomputable def reverseSemiproduct
    (measure : Measure target) (kernel : Kernel target source)
    (kernelFinite : Kernel.IsSFinite kernel) :
    Measure (Space.product source target) :=
  (semiproduct measure kernel kernelFinite).map
    (fun value => (value.2, value.1))
    (Space.swap_measurable target source)

public theorem reverseSemiproduct_apply (measure : Measure target)
    (kernel : Kernel target source) (kernelFinite : Kernel.IsSFinite kernel)
    {set : Set (alpha × beta)}
    (setMeasurable : (Space.product source target).Measurable set) :
    reverseSemiproduct measure kernel kernelFinite set =
      lintegral measure (fun second => kernel second
        (Set.preimage (fun first => (first, second)) set)) := by
  have swapMeasurable : MeasurableMap
      (Space.product target source) (Space.product source target)
      (fun value : beta × alpha => (value.2, value.1)) :=
    Space.swap_measurable target source
  have swappedSetMeasurable := swapMeasurable setMeasurable
  calc
    reverseSemiproduct measure kernel kernelFinite set =
        semiproduct measure kernel kernelFinite
          (Set.preimage (fun value => (value.2, value.1)) set) := by
      unfold reverseSemiproduct
      exact Measure.map_apply _
        (fun value : beta × alpha => (value.2, value.1))
        swapMeasurable setMeasurable
    _ = lintegral measure (fun second => kernel second
          (Set.preimage (fun first => (first, second)) set)) := by
      rw [semiproduct_apply measure kernel kernelFinite
        swappedSetMeasurable]
      apply lintegral_congr
      intro second
      rfl

/-- The reverse semiproduct evaluates on measurable rectangles as the integral
of the kernel over the marginal slice. -/
public theorem reverseSemiproduct_apply_product (measure : Measure target)
    (kernel : Kernel target source) (kernelFinite : Kernel.IsSFinite kernel)
    {left : Set alpha} {right : Set beta}
    (leftMeasurable : source.Measurable left) (rightMeasurable : target.Measurable right) :
    reverseSemiproduct measure kernel kernelFinite (Set.product left right) =
      lintegral (measure.restrict right) (fun input => kernel input left) := by
  rw [reverseSemiproduct, Measure.map_apply _ _ (Space.swap_measurable target source)
    (Space.product_set_measurable source target leftMeasurable rightMeasurable)]
  have swapped : Set.preimage (fun value : beta × alpha => (value.2, value.1))
      (Set.product left right) = Set.product right left := by
    apply Set.ext
    intro value
    exact ⟨fun member => ⟨member.2, member.1⟩, fun member => ⟨member.2, member.1⟩⟩
  rw [swapped, semiproduct_apply_product measure kernel kernelFinite rightMeasurable leftMeasurable]

/-- The product measure is the semiproduct with a constant right kernel. -/
@[expose] public noncomputable def prod (left : Measure source)
    (right : Measure target) (rightFinite : SFinite right) :
    Measure (Space.product source target) :=
  semiproduct left (Kernel.const source right)
    (Kernel.IsSFinite.const source rightFinite)

@[simp] public theorem prod_apply_product (left : Measure source)
    (right : Measure target) (rightFinite : SFinite right)
    {leftSet : Set alpha} {rightSet : Set beta}
    (leftMeasurable : source.Measurable leftSet)
    (rightMeasurable : target.Measurable rightSet) :
    prod left right rightFinite (Set.product leftSet rightSet) =
      ENNReal.mul (left leftSet) (right rightSet) := by
  rw [prod, semiproduct_apply_product left
      (Kernel.const source right)
      (Kernel.IsSFinite.const source rightFinite)
      leftMeasurable rightMeasurable]
  simp only [Kernel.const_apply]
  rw [
    lintegral_const, Measure.restrict_apply_univ,
    ENNReal.mulComm]

public theorem prod_apply (left : Measure source)
    (right : Measure target) (rightFinite : SFinite right)
    {set : Set (alpha × beta)}
    (setMeasurable : (Space.product source target).Measurable set) :
    prod left right rightFinite set =
      lintegral left (fun input => right
        (Set.preimage (fun value => (input, value)) set)) := by
  exact semiproduct_apply left (Kernel.const source right)
    (Kernel.IsSFinite.const source rightFinite) setMeasurable

/-- The product measure is independent of the chosen s-finite presentation. -/
public theorem prod_certificate_irrelevant (left : Measure source)
    (right : Measure target) (first second : SFinite right) :
    prod left right first = prod left right second := by
  apply Measure.ext
  intro set setMeasurable
  rw [prod_apply left right first setMeasurable,
    prod_apply left right second setMeasurable]

namespace IsFinite

/-- A product of finite measures is finite. -/
public theorem prod {left : Measure source} {right : Measure target}
    (leftFinite : IsFinite left) (rightFinite : IsFinite right) :
    IsFinite (Measure.prod left right
      (SFinite.ofFinite rightFinite)) := by
  have productUniv : Set.product (Set.univ : Set alpha)
      (Set.univ : Set beta) = Set.univ := by
    apply Set.ext
    intro value
    exact ⟨fun _ => True.intro, fun _ => ⟨True.intro, True.intro⟩⟩
  constructor
  rw [← productUniv, Measure.prod_apply_product
    left right (SFinite.ofFinite rightFinite) source.univ target.univ]
  rcases ENNReal.existsFiniteOfFinite leftFinite.univFinite with
    ⟨leftValue, leftEqual⟩
  rcases ENNReal.existsFiniteOfFinite rightFinite.univFinite with
    ⟨rightValue, rightEqual⟩
  rw [leftEqual, rightEqual]
  exact True.intro

end IsFinite

end Measure

end Foundations.Measure
