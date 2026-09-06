module

public import Foundations.Measure.Real.Cover.Interval

set_option autoImplicit false

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Adapted from Mathlib/MeasureTheory/OuterMeasure/OfFunction.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny recovers ordered interval representatives from every finite-cost cover.
-/

namespace Foundations.Measure.Real

open Foundations.Real
open Foundations.Real.Construction

public section

private noncomputable def representationOfFiniteCost
    (set : Set Carrier) (finiteCost : ENNReal.Finite (intervalCost set)) :
    HalfOpenRepresentation set := by
  classical
  by_cases represented : Nonempty (HalfOpenRepresentation set)
  · exact Classical.choice represented
  · have impossible := finiteCost
    unfold intervalCost at impossible
    simp only [dif_neg represented] at impossible
    exact False.elim impossible

private noncomputable def representationsOfFiniteCover
    {set : Set Carrier} (cover : CountableCover set)
    (finiteCost : ENNReal.Finite (coverCost intervalCost cover))
    (index : Nat) : HalfOpenRepresentation (cover.sets index) :=
  representationOfFiniteCost (cover.sets index)
    (ENNReal.finiteOfLe (rightFinite := finiteCost) (by
      unfold coverCost
      exact ENNReal.termLeTsum
        (fun current => intervalCost (cover.sets current)) index))

private noncomputable def intervalCoverOfFiniteCost
    {set : Set Carrier} (cover : CountableCover set)
    (finiteCost : ENNReal.Finite (coverCost intervalCost cover)) :
    IntervalCover set := by
  let representation := representationsOfFiniteCover cover finiteCost
  exact
    { lower := fun index => (representation index).lower
      upper := fun index => (representation index).upper
      ordered := fun index => (representation index).ordered
      covers := by
        intro value member
        rcases cover.covers member with ⟨index, indexMember⟩
        refine ⟨index, ?_⟩
        change Ioc (representation index).lower
          (representation index).upper value
        rw [← (representation index).set_eq]
        exact indexMember }

private theorem intervalCoverOfFiniteCost_cost
    {set : Set Carrier} (cover : CountableCover set)
    (finiteCost : ENNReal.Finite (coverCost intervalCost cover)) :
    (intervalCoverOfFiniteCost cover finiteCost).cost =
      coverCost intervalCost cover := by
  unfold IntervalCover.cost coverCost
  apply ENNReal.tsumCongr
  intro index
  change
    (representationsOfFiniteCover cover finiteCost index).length =
      intervalCost (cover.sets index)
  exact (intervalCost_of_representation _).symm

public theorem intervalLength_le_coverCost {lower upper : Carrier}
    (cover : CountableCover (Ioc lower upper)) :
    ENNReal.le (intervalLength lower upper)
      (coverCost intervalCost cover) := by
  cases totalEquation : coverCost intervalCost cover with
  | top => exact ENNReal.leTop _
  | finite total =>
      have finiteCost : ENNReal.Finite (coverCost intervalCost cover) := by
        rw [totalEquation]
        exact True.intro
      let intervalCover := intervalCoverOfFiniteCost cover finiteCost
      exact ENNReal.leTrans
        (intervalLength_le_intervalCover intervalCover)
        (by
          rw [intervalCoverOfFiniteCost_cost cover finiteCost,
            totalEquation]
          exact ENNReal.leRefl _)

public theorem ofFunction_apply_intervalCost (set : Set Carrier) :
    OuterMeasure.ofFunction intervalCost intervalCost_empty set =
      ENNReal.infimum (fun value =>
        ∃ cover : IntervalCover set, value = cover.cost) := by
  rw [OuterMeasure.ofFunction_apply]
  apply ENNReal.leAntisymm
  · apply ENNReal.leInfimum
    intro value member
    rcases member with ⟨cover, rfl⟩
    exact ENNReal.infimumLe
      ⟨cover.toCountableCover, cover.coverCost_toCountableCover.symm⟩
  · apply ENNReal.leInfimum
    intro value member
    rcases member with ⟨cover, rfl⟩
    cases totalEquation : coverCost intervalCost cover with
    | top => exact ENNReal.leTop _
    | finite total =>
        have finiteCost : ENNReal.Finite (coverCost intervalCost cover) := by
          rw [totalEquation]
          exact True.intro
        have included := ENNReal.infimumLe
          (set := fun value =>
            ∃ intervalCover : IntervalCover set,
              value = intervalCover.cost)
          ⟨intervalCoverOfFiniteCost cover finiteCost, rfl⟩
        rw [intervalCoverOfFiniteCost_cost cover finiteCost] at included
        rw [totalEquation] at included
        exact included

end

end Foundations.Measure.Real
