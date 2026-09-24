module

public import Problib.Measure.Kernel.Product.Basic
public import Problib.Measure.Dynkin.Uniqueness
public import Problib.Measure.Additive.Continuity
public import Problib.Measure.Product.Generator

set_option autoImplicit false

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Adapted from Mathlib/MeasureTheory/Measure/Prod.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny proves sigma-finite uniqueness by restricting both measures to diagonal
finite rectangles and then applying finite pi-lambda uniqueness.
-/

namespace Problib.Measure

open Problib.Real

universe u v


namespace Measure

variable {alpha : Type u} {beta : Type v}
  {source : Space alpha} {target : Space beta}

private def diagonalSpan {left : Measure source} {right : Measure target}
    (leftFinite : SigmaFinite left) (rightFinite : SigmaFinite right)
    (index : Nat) : Set (alpha × beta) :=
  Set.product (leftFinite.sets index) (rightFinite.sets index)

private theorem diagonalSpan_measurable
    {left : Measure source} {right : Measure target}
    (leftFinite : SigmaFinite left) (rightFinite : SigmaFinite right)
    (index : Nat) :
    (Space.product source target).Measurable
      (diagonalSpan leftFinite rightFinite index) :=
  Space.product_set_measurable source target
    (leftFinite.measurable index) (rightFinite.measurable index)

private theorem diagonalSpan_monotone
    {left : Measure source} {right : Measure target}
    (leftFinite : SigmaFinite left) (rightFinite : SigmaFinite right) :
    Set.MonotoneFamily (diagonalSpan leftFinite rightFinite) := by
  intro first second included value member
  exact ⟨leftFinite.monotone included member.1,
    rightFinite.monotone included member.2⟩

private theorem iUnion_diagonalSpan
    {left : Measure source} {right : Measure target}
    (leftFinite : SigmaFinite left) (rightFinite : SigmaFinite right) :
    Set.iUnion (diagonalSpan leftFinite rightFinite) = Set.univ := by
  apply Set.ext
  intro value
  constructor
  · intro _
    exact True.intro
  · intro _
    have leftMember : Set.iUnion leftFinite.sets value.1 := by
      rw [leftFinite.cover]
      exact True.intro
    have rightMember : Set.iUnion rightFinite.sets value.2 := by
      rw [rightFinite.cover]
      exact True.intro
    rcases leftMember with ⟨leftIndex, leftAtIndex⟩
    rcases rightMember with ⟨rightIndex, rightAtIndex⟩
    refine ⟨leftIndex + rightIndex,
      leftFinite.monotone (by omega) leftAtIndex,
      rightFinite.monotone (by omega) rightAtIndex⟩

namespace SigmaFinite

/-- Products of sigma-finite measures have diagonal finite spanning sets. -/
public noncomputable def prod {left : Measure source}
    (leftFinite : SigmaFinite left) {right : Measure target}
    (rightFinite : SigmaFinite right) :
    SigmaFinite (Measure.prod left right rightFinite.toSFinite) where
  sets := diagonalSpan leftFinite rightFinite
  measurable := diagonalSpan_measurable leftFinite rightFinite
  monotone := diagonalSpan_monotone leftFinite rightFinite
  finite := by
    intro index
    rw [diagonalSpan, Measure.prod_apply_product left right
      rightFinite.toSFinite (leftFinite.measurable index)
      (rightFinite.measurable index)]
    exact ENNReal.mul_finite (leftFinite.finite index) (rightFinite.finite index)
  cover := iUnion_diagonalSpan leftFinite rightFinite

end SigmaFinite

private theorem inter_product (left first : Set alpha)
    (right second : Set beta) :
    Set.inter (Set.product left right) (Set.product first second) =
      Set.product (Set.inter left first) (Set.inter right second) := by
  apply Set.ext
  intro value
  exact ⟨
    fun member => ⟨⟨member.1.1, member.2.1⟩,
      ⟨member.1.2, member.2.2⟩⟩,
    fun member => ⟨⟨member.1.1, member.2.1⟩,
      ⟨member.1.2, member.2.2⟩⟩⟩

/-- A measure with the expected rectangle values is the product of
sigma-finite factors. -/
public theorem prod_unique {left : Measure source} {right : Measure target}
    (leftFinite : SigmaFinite left) (rightFinite : SigmaFinite right)
    {candidate : Measure (Space.product source target)}
    (rectangles : ∀ leftSet rightSet,
      source.Measurable leftSet → target.Measurable rightSet →
      candidate (Set.product leftSet rightSet) =
        ENNReal.mul (left leftSet) (right rightSet)) :
    candidate = Measure.prod left right rightFinite.toSFinite := by
  let expected := Measure.prod left right rightFinite.toSFinite
  have restrictedEqual : ∀ index,
      candidate.restrict (diagonalSpan leftFinite rightFinite index) =
        expected.restrict (diagonalSpan leftFinite rightFinite index) := by
    intro index
    let span := diagonalSpan leftFinite rightFinite index
    have spanMeasurable : (Space.product source target).Measurable span :=
      diagonalSpan_measurable leftFinite rightFinite index
    have candidateFinite : IsFinite (candidate.restrict span) := by
      constructor
      rw [candidate.restrict_apply_univ]
      change ENNReal.Finite (candidate (Set.product
        (leftFinite.sets index) (rightFinite.sets index)))
      rw [rectangles (leftFinite.sets index) (rightFinite.sets index)
          (leftFinite.measurable index) (rightFinite.measurable index)]
      exact ENNReal.mul_finite (leftFinite.finite index) (rightFinite.finite index)
    have expectedFinite : IsFinite (expected.restrict span) := by
      constructor
      rw [expected.restrict_apply_univ]
      change ENNReal.Finite ((Measure.prod left right
        rightFinite.toSFinite) (Set.product
          (leftFinite.sets index) (rightFinite.sets index)))
      rw [Measure.prod_apply_product left right rightFinite.toSFinite
          (leftFinite.measurable index) (rightFinite.measurable index)]
      exact ENNReal.mul_finite (leftFinite.finite index) (rightFinite.finite index)
    apply Measure.ext_of_generate (Space.Rectangle source target)
      (Space.product_eq_generated_rectangles source target)
      (Space.rectangle_piSystem source target)
      (Space.rectangle_contains_univ source target)
      candidateFinite expectedFinite
    intro set rectangle
    rcases rectangle with
      ⟨leftSet, rightSet, leftMeasurable, rightMeasurable, rfl⟩
    have rectangleMeasurable := Space.product_set_measurable source target
      leftMeasurable rightMeasurable
    have leftInterMeasurable := source.inter leftMeasurable
      (leftFinite.measurable index)
    have rightInterMeasurable := target.inter rightMeasurable
      (rightFinite.measurable index)
    rw [candidate.restrict_apply span rectangleMeasurable,
      expected.restrict_apply span rectangleMeasurable]
    change candidate (Set.inter (Set.product leftSet rightSet)
        (Set.product (leftFinite.sets index) (rightFinite.sets index))) =
      Measure.prod left right rightFinite.toSFinite
        (Set.inter (Set.product leftSet rightSet)
          (Set.product (leftFinite.sets index) (rightFinite.sets index)))
    rw [
      inter_product leftSet (leftFinite.sets index)
        rightSet (rightFinite.sets index),
      rectangles _ _ leftInterMeasurable rightInterMeasurable,
      Measure.prod_apply_product left right
        rightFinite.toSFinite leftInterMeasurable rightInterMeasurable]
  apply Measure.ext
  intro set setMeasurable
  let slices := fun index =>
    Set.inter set (diagonalSpan leftFinite rightFinite index)
  have slicesMeasurable : ∀ index,
      (Space.product source target).Measurable (slices index) :=
    fun index => (Space.product source target).inter setMeasurable
      (diagonalSpan_measurable leftFinite rightFinite index)
  have slicesMonotone : Set.MonotoneFamily slices := by
    intro first second included value member
    exact ⟨member.1,
      diagonalSpan_monotone leftFinite rightFinite included member.2⟩
  have slicesUnion : Set.iUnion slices = set := by
    change Set.iUnion (fun index => Set.inter set
      (diagonalSpan leftFinite rightFinite index)) = set
    rw [← Set.inter_iUnion,
      iUnion_diagonalSpan leftFinite rightFinite,
      Set.inter_univ_right]
  have sliceEqual : ∀ index,
      candidate (slices index) = expected (slices index) := by
    intro index
    have equal := congrArg (fun measure => measure set)
      (restrictedEqual index)
    simpa only [Measure.restrict_apply _ _ setMeasurable, slices] using equal
  calc
    candidate set = ENNReal.iSup (fun index => candidate (slices index)) := by
      rw [← candidate.continuity_from_below slices
        slicesMeasurable slicesMonotone, slicesUnion]
    _ = ENNReal.iSup (fun index => expected (slices index)) := by
      apply congrArg ENNReal.iSup
      funext index
      exact sliceEqual index
    _ = expected set := by
      rw [← expected.continuity_from_below slices
        slicesMeasurable slicesMonotone, slicesUnion]

end Measure

end Problib.Measure
