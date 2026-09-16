module

public import Foundations.Measure.Kernel.Product.Algebra
public import Foundations.Measure.Kernel.Product.AlmostEverywhere
public import Foundations.Measure.Kernel.Product.Piecewise
public import Foundations.Measure.Kernel.Product.Uniqueness
import Foundations.Measure.Integral.Lebesgue.Transport
import Foundations.Measure.Kernel.Measurable

set_option autoImplicit false

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

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

private theorem preimage_swap_product (left : Set alpha)
    (right : Set beta) :
    Set.preimage (fun value : alpha × beta => (value.2, value.1))
        (Set.product right left) =
      Set.product left right := by
  apply Set.ext
  intro value
  exact ⟨fun member => ⟨member.2, member.1⟩,
    fun member => ⟨member.2, member.1⟩⟩

private theorem prod_congr {firstLeft secondLeft : Measure source}
    {firstRight secondRight : Measure target}
    (leftEqual : firstLeft = secondLeft)
    (rightEqual : firstRight = secondRight)
    (firstFinite : SFinite firstRight)
    (secondFinite : SFinite secondRight) :
    Measure.prod firstLeft firstRight firstFinite =
      Measure.prod secondLeft secondRight secondFinite := by
  cases leftEqual
  cases rightEqual
  exact Measure.prod_certificate_irrelevant
    firstLeft firstRight firstFinite secondFinite

/-- Swapping a product of finite measures reverses its factors. -/
public theorem prod_swap_of_finite {left : Measure source}
    {right : Measure target} (leftFinite : IsFinite left)
    (rightFinite : IsFinite right) :
    (Measure.prod left right (SFinite.ofFinite rightFinite)).map
        (fun value : alpha × beta => (value.2, value.1))
        (Space.swap_measurable source target) =
      Measure.prod right left (SFinite.ofFinite leftFinite) := by
  apply Measure.prod_unique
    (SigmaFinite.ofFinite rightFinite) (SigmaFinite.ofFinite leftFinite)
  intro rightSet leftSet rightMeasurable leftMeasurable
  rw [Measure.map_apply _
      (fun value : alpha × beta => (value.2, value.1))
      (Space.swap_measurable source target)
      (Space.product_set_measurable target source
        rightMeasurable leftMeasurable),
    preimage_swap_product leftSet rightSet,
    Measure.prod_apply_product left right
      (SFinite.ofFinite rightFinite) leftMeasurable rightMeasurable,
    ENNReal.mulComm]

/-- Swapping a product of s-finite measures reverses its factors. -/
public theorem prod_swap {left : Measure source} {right : Measure target}
    (leftFinite : SFinite left) (rightFinite : SFinite right) :
    (Measure.prod left right rightFinite).map
        (fun value : alpha × beta => (value.2, value.1))
        (Space.swap_measurable source target) =
      Measure.prod right left leftFinite := by
  let leftTerms := leftFinite.components
  let rightTerms := rightFinite.components
  let leftTermFinite : ∀ index, SFinite (leftTerms index) :=
    fun index => SFinite.ofFinite (leftFinite.finite index)
  let rightTermFinite : ∀ index, SFinite (rightTerms index) :=
    fun index => SFinite.ofFinite (rightFinite.finite index)
  let products := fun first second =>
    Measure.prod (leftTerms first) (rightTerms second)
      (rightTermFinite second)
  let swappedProducts := fun first second =>
    Measure.prod (rightTerms second) (leftTerms first)
      (leftTermFinite first)
  have leftSumEq : Measure.sum leftTerms = left := by
    simpa only [leftTerms] using leftFinite.sum_eq
  have rightSumEq : Measure.sum rightTerms = right := by
    simpa only [rightTerms] using rightFinite.sum_eq
  have leftExpansion : Measure.prod left right rightFinite =
      Measure.sum (fun first => Measure.sum (products first)) := by
    calc
      Measure.prod left right rightFinite =
          Measure.prod (Measure.sum leftTerms) (Measure.sum rightTerms)
            (SFinite.sum rightTerms rightTermFinite) :=
        prod_congr leftSumEq.symm rightSumEq.symm _ _
      _ = Measure.sum (fun first => Measure.sum (products first)) :=
        Measure.prod_sum_both leftTerms rightTerms rightTermFinite
  have rightExpansion : Measure.prod right left leftFinite =
      Measure.sum (fun second => Measure.sum (fun first =>
        swappedProducts first second)) := by
    calc
      Measure.prod right left leftFinite =
          Measure.prod (Measure.sum rightTerms) (Measure.sum leftTerms)
            (SFinite.sum leftTerms leftTermFinite) :=
        prod_congr rightSumEq.symm leftSumEq.symm _ _
      _ = Measure.sum (fun second => Measure.sum (fun first =>
          Measure.prod (rightTerms second) (leftTerms first)
            (leftTermFinite first))) :=
        Measure.prod_sum_both rightTerms leftTerms leftTermFinite
      _ = Measure.sum (fun second => Measure.sum (fun first =>
          swappedProducts first second)) := rfl
  calc
    (Measure.prod left right rightFinite).map
        (fun value : alpha × beta => (value.2, value.1))
        (Space.swap_measurable source target) =
        (Measure.sum (fun first => Measure.sum (products first))).map
          (fun value : alpha × beta => (value.2, value.1))
          (Space.swap_measurable source target) := by rw [leftExpansion]
    _ = Measure.sum (fun first => Measure.sum (fun second =>
          (products first second).map
            (fun value : alpha × beta => (value.2, value.1))
            (Space.swap_measurable source target))) := by
      rw [Measure.map_sum]
      apply congrArg Measure.sum
      funext first
      exact Measure.map_sum (products first)
        (fun value : alpha × beta => (value.2, value.1))
        (Space.swap_measurable source target)
    _ = Measure.sum (fun first => Measure.sum (swappedProducts first)) := by
      apply congrArg Measure.sum
      funext first
      apply congrArg Measure.sum
      funext second
      exact prod_swap_of_finite
        (leftFinite.finite first) (rightFinite.finite second)
    _ = Measure.sum (fun second => Measure.sum (fun first =>
          swappedProducts first second)) :=
      Measure.sum_comm swappedProducts
    _ = Measure.prod right left leftFinite := rightExpansion.symm

end Measure

variable {alpha : Type u} {beta : Type v}
  {source : Space alpha} {target : Space beta}

/-- Integration against a semiproduct is iterated integration. -/
public theorem lintegral_semiproduct (measure : Measure source)
    (kernel : Kernel source target) (kernelFinite : Kernel.IsSFinite kernel)
    {function : alpha × beta → ENNReal}
    (functionMeasurable :
      ENNRealMeasurable (Space.product source target) function) :
    lintegral (Measure.semiproduct measure kernel kernelFinite) function =
      lintegral measure (fun input =>
        lintegral (kernel input) (fun value => function (input, value))) := by
  rw [Measure.semiproduct,
    Measure.lintegral_bind measure (Kernel.attach kernel kernelFinite)
      functionMeasurable]
  apply lintegral_congr
  intro input
  rw [Kernel.attach_apply,
    lintegral_map (kernel input) (fun value => (input, value))
      (Kernel.pair_left_measurable input) functionMeasurable]

/-- Integration against a reverse semiproduct follows its sampling order. -/
public theorem lintegral_reverseSemiproduct (measure : Measure target)
    (kernel : Kernel target source) (kernelFinite : Kernel.IsSFinite kernel)
    {function : alpha × beta → ENNReal}
    (functionMeasurable :
      ENNRealMeasurable (Space.product source target) function) :
    lintegral (Measure.reverseSemiproduct measure kernel kernelFinite)
        function =
      lintegral measure (fun second =>
        lintegral (kernel second) (fun first => function (first, second))) := by
  have swappedMeasurable : ENNRealMeasurable
      (Space.product target source)
      (fun value => function (value.2, value.1)) :=
    ENNRealMeasurable.comp functionMeasurable
      (Space.swap_measurable target source)
  rw [Measure.reverseSemiproduct,
    lintegral_map (Measure.semiproduct measure kernel kernelFinite)
      (fun value => (value.2, value.1))
      (Space.swap_measurable target source) functionMeasurable,
    lintegral_semiproduct measure kernel kernelFinite swappedMeasurable]

/-- Tonelli's theorem in the construction order. Only the right factor needs
an s-finite presentation. -/
public theorem lintegral_prod (left : Measure source)
    (right : Measure target) (rightFinite : Measure.SFinite right)
    {function : alpha × beta → ENNReal}
    (functionMeasurable :
      ENNRealMeasurable (Space.product source target) function) :
    lintegral (Measure.prod left right rightFinite) function =
      lintegral left (fun input =>
        lintegral right (fun value => function (input, value))) := by
  exact lintegral_semiproduct left (Kernel.const source right)
    (Kernel.IsSFinite.const source rightFinite) functionMeasurable

/-- Swapping variables and factors does not change a product integral. -/
public theorem lintegral_prod_swap (left : Measure source)
    (right : Measure target) (leftFinite : Measure.SFinite left)
    (rightFinite : Measure.SFinite right)
    {function : alpha × beta → ENNReal}
    (functionMeasurable :
      ENNRealMeasurable (Space.product source target) function) :
    lintegral (Measure.prod right left leftFinite)
        (fun value => function (value.2, value.1)) =
      lintegral (Measure.prod left right rightFinite) function := by
  have swappedMeasurable : ENNRealMeasurable
      (Space.product target source)
      (fun value => function (value.2, value.1)) :=
    ENNRealMeasurable.comp functionMeasurable
      (Space.swap_measurable target source)
  calc
    lintegral (Measure.prod right left leftFinite)
        (fun value => function (value.2, value.1)) =
        lintegral ((Measure.prod right left leftFinite).map
          (fun value => (value.2, value.1))
          (Space.swap_measurable target source)) function := by
      symm
      exact lintegral_map (Measure.prod right left leftFinite)
        (fun value => (value.2, value.1))
        (Space.swap_measurable target source) functionMeasurable
    _ = lintegral (Measure.prod left right rightFinite) function := by
      rw [Measure.prod_swap rightFinite leftFinite]

/-- Symmetric Tonelli for two s-finite factors. -/
public theorem lintegral_prod_symm (left : Measure source)
    (right : Measure target) (leftFinite : Measure.SFinite left)
    (rightFinite : Measure.SFinite right)
    {function : alpha × beta → ENNReal}
    (functionMeasurable :
      ENNRealMeasurable (Space.product source target) function) :
    lintegral (Measure.prod left right rightFinite) function =
      lintegral right (fun value =>
        lintegral left (fun input => function (input, value))) := by
  have swappedMeasurable : ENNRealMeasurable
      (Space.product target source)
      (fun value => function (value.2, value.1)) :=
    ENNRealMeasurable.comp functionMeasurable
      (Space.swap_measurable target source)
  calc
    lintegral (Measure.prod left right rightFinite) function =
        lintegral (Measure.prod right left leftFinite)
          (fun value => function (value.2, value.1)) :=
      (lintegral_prod_swap left right leftFinite rightFinite
        functionMeasurable).symm
    _ = lintegral right (fun value =>
        lintegral left (fun input => function (input, value))) :=
      lintegral_prod right left leftFinite swappedMeasurable

end Foundations.Measure
