module

public import Problib.Measure.Outer.Basic

set_option autoImplicit false

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Adapted from Mathlib/MeasureTheory/OuterMeasure/OfFunction.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny represents the cover infimum directly and uses its local countable-series
and natural-product reindexing results.
-/

namespace Problib.Measure

open Problib.Real

universe u

public section

/-- A natural-number-indexed family whose union contains a specified set. -/
structure CountableCover {α : Type u} (set : Set α) where
  sets : Nat → Set α
  covers : Set.Subset set (Set.iUnion sets)

/-- The sum of a set cost over a countable cover. -/
@[expose] noncomputable def coverCost {α : Type u}
    (cost : Set α → ENNReal) {set : Set α} (cover : CountableCover set) :
    ENNReal :=
  ENNReal.tsum (fun index => cost (cover.sets index))

namespace OuterMeasure

private def singleCover {α : Type u} (set : Set α) :
    CountableCover set where
  sets
    | 0 => set
    | _ + 1 => Set.empty
  covers := by
    intro value member
    exact ⟨0, member⟩

private theorem coverCost_single {α : Type u} (cost : Set α → ENNReal)
    (emptyCost : cost Set.empty = ENNReal.zero) (set : Set α) :
    coverCost cost (singleCover set) = cost set := by
  have equal :
      (fun index => cost ((singleCover set).sets index)) =
        ENNReal.single 0 (cost set) := by
    funext index
    cases index with
    | zero => simp [singleCover, ENNReal.single]
    | succ index => simp [singleCover, ENNReal.single, emptyCost]
  unfold coverCost
  rw [equal, ENNReal.tsum_single]

private def coverCosts {α : Type u} (cost : Set α → ENNReal)
    (set : Set α) : ENNReal → Prop :=
  fun value => ∃ cover : CountableCover set, value = coverCost cost cover

private noncomputable def ofFunctionValue {α : Type u}
    (cost : Set α → ENNReal) (set : Set α) : ENNReal :=
  ENNReal.infimum (coverCosts cost set)

private theorem ofFunctionValue_empty {α : Type u}
    (cost : Set α → ENNReal)
    (emptyCost : cost Set.empty = ENNReal.zero) :
    ofFunctionValue cost Set.empty = ENNReal.zero := by
  apply ENNReal.le_antisymm
  · have included : ENNReal.le (ofFunctionValue cost Set.empty)
        (coverCost cost (singleCover Set.empty)) := by
      unfold ofFunctionValue
      exact ENNReal.infimum_le ⟨singleCover Set.empty, rfl⟩
    rw [coverCost_single cost emptyCost Set.empty, emptyCost] at included
    exact included
  · exact ENNReal.zero_le _

private theorem ofFunctionValue_mono {α : Type u}
    (cost : Set α → ENNReal) {left right : Set α}
    (included : Set.Subset left right) :
    ENNReal.le (ofFunctionValue cost left) (ofFunctionValue cost right) := by
  unfold ofFunctionValue
  apply ENNReal.le_infimum
  intro value member
  rcases member with ⟨cover, rfl⟩
  let restricted : CountableCover left :=
    { sets := cover.sets
      covers := fun element elementMember =>
        cover.covers (included elementMember) }
  exact ENNReal.infimum_le ⟨restricted, rfl⟩

private def flattenCover {α : Type u} (sets : Nat → Set α)
    (covers : ∀ index, CountableCover (sets index)) :
    CountableCover (Set.iUnion sets) where
  sets := fun flatIndex =>
    let pair := Countable.Pair.decode flatIndex
    (covers pair.1).sets pair.2
  covers := by
    intro value member
    rcases member with ⟨row, rowMember⟩
    rcases (covers row).covers rowMember with ⟨column, columnMember⟩
    refine ⟨Countable.Pair.encode (row, column), ?_⟩
    have decoded :
        Countable.Pair.decode
            (Countable.Pair.encode (row, column)) =
          (row, column) :=
      Countable.Pair.decode_encode (row, column)
    change
      (covers (Countable.Pair.decode
          (Countable.Pair.encode (row, column))).1).sets
        (Countable.Pair.decode
          (Countable.Pair.encode (row, column))).2 value
    rw [decoded]
    exact columnMember

private theorem coverCost_flatten {α : Type u} (cost : Set α → ENNReal)
    (sets : Nat → Set α)
    (covers : ∀ index, CountableCover (sets index)) :
    coverCost cost (flattenCover sets covers) =
      ENNReal.tsum (ENNReal.flatten
        (fun row column => cost ((covers row).sets column))) :=
  rfl

private theorem ofFunctionValue_iUnion {α : Type u}
    (cost : Set α → ENNReal) (sets : Nat → Set α) :
    ENNReal.le (ofFunctionValue cost (Set.iUnion sets))
      (ENNReal.tsum (fun index => ofFunctionValue cost (sets index))) := by
  classical
  let values : Nat → ENNReal :=
    fun index => ofFunctionValue cost (sets index)
  let total : ENNReal := ENNReal.tsum values
  change ENNReal.le (ofFunctionValue cost (Set.iUnion sets)) total
  cases totalEquation : total with
  | top => exact ENNReal.le_top _
  | finite totalValue =>
      apply ENNReal.le_of_forall_positive_le_add
      intro error errorPositive
      cases error with
      | top =>
          rw [ENNReal.add_top]
          exact ENNReal.le_top _
      | finite errorValue =>
          have valueFinite (index : Nat) : ENNReal.Finite (values index) := by
            apply ENNReal.finite_of_le (right := ENNReal.finite totalValue) (rightFinite := True.intro)
            have included := ENNReal.term_le_tsum values index
            change ENNReal.le (values index) total at included
            rw [totalEquation] at included
            exact included
          rcases ENNReal.exists_positive_summable_error
              (ENNReal.finite errorValue) True.intro errorPositive with
            ⟨errors, errorsPositive, errorsTotal⟩
          have coverExists (index : Nat) :
              ∃ cover : CountableCover (sets index),
                ENNReal.lt (coverCost cost cover)
                  (ENNReal.add (values index) (errors index)) := by
            have approximate := ENNReal.exists_less_than_infimum_add
              (set := coverCosts cost (sets index))
              (valueFinite index) (errorsPositive index)
            rcases approximate with
              ⟨value, ⟨cover, valueEquation⟩, less⟩
            rw [valueEquation] at less
            exact ⟨cover, less⟩
          let covers : ∀ index, CountableCover (sets index) :=
            fun index => Classical.choose (coverExists index)
          have coversLess (index : Nat) :
              ENNReal.lt (coverCost cost (covers index))
                (ENNReal.add (values index) (errors index)) :=
            Classical.choose_spec (coverExists index)
          have envelopeLeCover :
              ENNReal.le (ofFunctionValue cost (Set.iUnion sets))
                (coverCost cost (flattenCover sets covers)) := by
            unfold ofFunctionValue
            exact ENNReal.infimum_le ⟨flattenCover sets covers, rfl⟩
          have coverLeApproximation :
              ENNReal.le (coverCost cost (flattenCover sets covers))
                (ENNReal.tsum (fun index =>
                  ENNReal.add (values index) (errors index))) := by
            rw [coverCost_flatten, ENNReal.tsum_flatten]
            apply ENNReal.tsum_le_tsum
            intro index
            exact (coversLess index).1
          have approximationLe :
              ENNReal.le
                (ENNReal.tsum (fun index =>
                  ENNReal.add (values index) (errors index)))
                (ENNReal.add (ENNReal.finite totalValue)
                  (ENNReal.finite errorValue)) := by
            rw [ENNReal.tsum_add]
            apply ENNReal.add_le_add
            · change ENNReal.le total (ENNReal.finite totalValue)
              rw [totalEquation]
              exact ENNReal.le_refl _
            · exact errorsTotal
          exact ENNReal.le_trans envelopeLeCover
            (ENNReal.le_trans coverLeApproximation approximationLe)

/-- The greatest outer measure bounded above by a set cost. -/
noncomputable def ofFunction {α : Type u}
    (cost : Set α → ENNReal)
    (emptyCost : cost Set.empty = ENNReal.zero) : OuterMeasure α where
  measure := ofFunctionValue cost
  empty := ofFunctionValue_empty cost emptyCost
  mono := ofFunctionValue_mono cost
  iUnion_le := ofFunctionValue_iUnion cost

private theorem ofFunction_apply_definition {α : Type u}
    (cost : Set α → ENNReal)
    (emptyCost : cost Set.empty = ENNReal.zero) (set : Set α) :
    ofFunction cost emptyCost set =
      ENNReal.infimum (fun value =>
        ∃ cover : CountableCover set, value = coverCost cost cover) :=
  rfl

theorem ofFunction_apply {α : Type u} (cost : Set α → ENNReal)
    (emptyCost : cost Set.empty = ENNReal.zero) (set : Set α) :
    ofFunction cost emptyCost set =
      ENNReal.infimum (fun value =>
        ∃ cover : CountableCover set, value = coverCost cost cover) :=
  ofFunction_apply_definition cost emptyCost set

theorem ofFunction_le {α : Type u} (cost : Set α → ENNReal)
    (emptyCost : cost Set.empty = ENNReal.zero) (set : Set α) :
    ENNReal.le (ofFunction cost emptyCost set) (cost set) := by
  change ENNReal.le (ofFunctionValue cost set) (cost set)
  have included := ENNReal.infimum_le
    (set := coverCosts cost set)
    (value := coverCost cost (singleCover set))
    ⟨singleCover set, rfl⟩
  rw [coverCost_single cost emptyCost set] at included
  exact included

theorem le_ofFunction_apply {α : Type u}
    (cost : Set α → ENNReal)
    (emptyCost : cost Set.empty = ENNReal.zero) (set : Set α)
    {lower : ENNReal}
    (allCovers : ∀ cover : CountableCover set,
      ENNReal.le lower (coverCost cost cover)) :
    ENNReal.le lower (ofFunction cost emptyCost set) := by
  change ENNReal.le lower (ENNReal.infimum (coverCosts cost set))
  apply ENNReal.le_infimum
  intro value member
  rcases member with ⟨cover, rfl⟩
  exact allCovers cover

theorem le_ofFunction {α : Type u} (outer : OuterMeasure α)
    (cost : Set α → ENNReal)
    (emptyCost : cost Set.empty = ENNReal.zero)
    (dominated : ∀ set, ENNReal.le (outer set) (cost set))
    (set : Set α) :
    ENNReal.le (outer set) (ofFunction cost emptyCost set) := by
  apply le_ofFunction_apply cost emptyCost set
  intro cover
  exact ENNReal.le_trans (outer.mono cover.covers)
    (ENNReal.le_trans (outer.iUnion_le cover.sets)
      (ENNReal.tsum_le_tsum (fun index => dominated (cover.sets index))))

theorem ofFunction_eq {α : Type u} (cost : Set α → ENNReal)
    (emptyCost : cost Set.empty = ENNReal.zero) (set : Set α)
    (monoAt : ∀ {superset : Set α}, Set.Subset set superset →
      ENNReal.le (cost set) (cost superset))
    (subadd : ∀ sets : Nat → Set α,
      ENNReal.le (cost (Set.iUnion sets))
        (ENNReal.tsum (fun index => cost (sets index)))) :
    ofFunction cost emptyCost set = cost set := by
  apply ENNReal.le_antisymm (ofFunction_le cost emptyCost set)
  apply le_ofFunction_apply cost emptyCost set
  intro cover
  exact ENNReal.le_trans (monoAt cover.covers) (subadd cover.sets)

end OuterMeasure

end

end Problib.Measure
