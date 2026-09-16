module

public import Foundations.Measure.Kernel.Product.Basic
public import Foundations.Measure.Kernel.Composition.Bind
public import Foundations.Measure.Integral.Lebesgue.Measure
import Foundations.Measure.Kernel.Measurable.Section
import Foundations.Measure.Integral.Lebesgue.Algebra

set_option autoImplicit false

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Rémy Degenne

Adapted from Mathlib/MeasureTheory/Measure/Prod.lean and
Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.
-/

namespace Foundations.Measure

open Foundations.Real

universe u v

namespace Measure

variable {alpha : Type u} {beta : Type v}
  {source : Space alpha} {target : Space beta}

/-- Product distributes over a countable sum in the first measure. -/
public theorem prod_sum_left (measures : Nat → Measure source)
    (right : Measure target) (rightFinite : SFinite right) :
    prod (Measure.sum measures) right rightFinite =
      Measure.sum (fun index => prod (measures index) right rightFinite) := by
  apply Measure.ext
  intro set setMeasurable
  rw [prod_apply (Measure.sum measures) right rightFinite setMeasurable,
    lintegral_sum measures,
    Measure.sum_apply
      (fun index => prod (measures index) right rightFinite) setMeasurable]
  apply ENNReal.tsumCongr
  intro index
  exact (prod_apply (measures index) right rightFinite setMeasurable).symm

/-- Product distributes over a countable sum of s-finite right measures. -/
public theorem prod_sum_right (left : Measure source)
    (measures : Nat → Measure target)
    (finite : ∀ index, SFinite (measures index)) :
    prod left (Measure.sum measures) (SFinite.sum measures finite) =
      Measure.sum (fun index => prod left (measures index) (finite index)) := by
  apply Measure.ext
  intro set setMeasurable
  have sectionsMeasurable : ∀ input,
      target.Measurable
        (Set.preimage (fun value => (input, value)) set) :=
    fun input => Kernel.pair_left_measurable input setMeasurable
  have termsMeasurable : ∀ index, ENNRealMeasurable source
      (fun input => measures index
        (Set.preimage (fun value => (input, value)) set)) := by
    intro index
    exact Kernel.section_apply_measurable
      (Kernel.const source (measures index))
      (Kernel.IsSFinite.const source (finite index)) setMeasurable
  rw [prod_apply left (Measure.sum measures)
      (SFinite.sum measures finite) setMeasurable]
  calc
    lintegral left (fun input => Measure.sum measures
        (Set.preimage (fun value => (input, value)) set)) =
        lintegral left (fun input => ENNReal.tsum (fun index =>
          measures index
            (Set.preimage (fun value => (input, value)) set))) := by
      apply lintegral_congr
      intro input
      exact Measure.sum_apply measures (sectionsMeasurable input)
    _ = ENNReal.tsum (fun index => lintegral left (fun input =>
          measures index
            (Set.preimage (fun value => (input, value)) set))) :=
      lintegral_tsum left _ termsMeasurable
    _ = Measure.sum
        (fun index => prod left (measures index) (finite index)) set := by
      rw [Measure.sum_apply
        (fun index => prod left (measures index) (finite index))
        setMeasurable]
      apply ENNReal.tsumCongr
      intro index
      exact (prod_apply left (measures index) (finite index)
        setMeasurable).symm

/-- Two countable s-finite presentations expand a product as a double sum. -/
public theorem prod_sum_both (left : Nat → Measure source)
    (right : Nat → Measure target)
    (rightFinite : ∀ index, SFinite (right index)) :
    prod (Measure.sum left) (Measure.sum right)
        (SFinite.sum right rightFinite) =
      Measure.sum (fun first => Measure.sum (fun second =>
        prod (left first) (right second) (rightFinite second))) := by
  rw [prod_sum_left]
  apply congrArg Measure.sum
  funext first
  exact prod_sum_right (left first) right rightFinite


/-- Scaling the base measure by an extended scalar scales the semiproduct measure by that factor. -/
public theorem semiproduct_smul (measure : Measure source) (factor : ENNReal)
    (kernel : Kernel source target) (finite : Kernel.IsSFinite kernel) :
    Measure.semiproduct (Measure.smul factor measure) kernel finite =
      Measure.smul factor (Measure.semiproduct measure kernel finite) := by
  apply Measure.ext
  intro set measurable
  rw [Measure.semiproduct_apply _ _ _ measurable,
    Measure.smul_apply_measurable _ _ measurable,
    Measure.semiproduct_apply _ _ _ measurable]
  exact lintegral_smul_measure _ factor measure

/-- Scaling the base measure by an extended scalar scales the reverse semiproduct measure by that factor. -/
public theorem reverseSemiproduct_smul (measure : Measure target) (factor : ENNReal)
    (kernel : Kernel target source) (finite : Kernel.IsSFinite kernel) :
    Measure.reverseSemiproduct (Measure.smul factor measure) kernel finite =
      Measure.smul factor (Measure.reverseSemiproduct measure kernel finite) := by
  rw [Measure.reverseSemiproduct, semiproduct_smul, Measure.map_smul]
  rfl

end Measure

namespace Measure.SFinite

variable {alpha : Type u} {beta : Type v}
  {source : Space alpha} {target : Space beta}

/-- Semiproduct preserves s-finiteness when both inputs are s-finite. -/
public noncomputable def semiproduct {measure : Measure source}
    (measureFinite : Measure.SFinite measure)
    {kernel : Kernel source target}
    (kernelFinite : Kernel.IsSFinite kernel) :
    Measure.SFinite
      (Measure.semiproduct measure kernel kernelFinite) := by
  unfold Measure.semiproduct
  exact measureFinite.bind kernelFinite.attach

/-- The product of two s-finite measures is s-finite. -/
public noncomputable def prod {left : Measure source}
    (leftFinite : Measure.SFinite left) {right : Measure target}
    (rightFinite : Measure.SFinite right) :
    Measure.SFinite (Measure.prod left right rightFinite) :=
  leftFinite.semiproduct (Kernel.IsSFinite.const source rightFinite)

end Measure.SFinite

end Foundations.Measure
