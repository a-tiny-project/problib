module

public import Problib.Measure.Set
public import Problib.Real.Series

set_option autoImplicit false

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov

Adapted from Mathlib/MeasureTheory/OuterMeasure/Defs.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny uses explicit set operations and its local extended nonnegative reals.
-/

namespace Problib.Measure

open Problib.Real

universe u

public section

/-- A monotone, countably subadditive set function that vanishes on the empty
set. -/
structure OuterMeasure (α : Type u) where
  measure : Set α → ENNReal
  empty : measure Set.empty = ENNReal.zero
  mono : ∀ {left right : Set α}, Set.Subset left right →
    ENNReal.le (measure left) (measure right)
  iUnion_le : ∀ sets : Nat → Set α,
    ENNReal.le (measure (Set.iUnion sets))
      (ENNReal.tsum (fun index => measure (sets index)))

namespace OuterMeasure

instance {α : Type u} : CoeFun (OuterMeasure α)
    (fun _ => Set α → ENNReal) where
  coe outer := outer.measure

@[ext] theorem ext {α : Type u} {left right : OuterMeasure α}
    (equal : ∀ set, left set = right set) : left = right := by
  cases left with
  | mk leftMeasure leftEmpty leftMono leftUnion =>
      cases right with
      | mk rightMeasure rightEmpty rightMono rightUnion =>
          have measureEqual : leftMeasure = rightMeasure := funext equal
          subst rightMeasure
          rfl

@[simp] theorem empty_apply {α : Type u}
    (outer : OuterMeasure α) : outer Set.empty = ENNReal.zero :=
  outer.empty

theorem mono_apply {α : Type u} (outer : OuterMeasure α)
    {left right : Set α} (included : Set.Subset left right) :
    ENNReal.le (outer left) (outer right) :=
  outer.mono included

theorem iUnion_apply_le {α : Type u} (outer : OuterMeasure α)
    (sets : Nat → Set α) :
    ENNReal.le (outer (Set.iUnion sets))
      (ENNReal.tsum (fun index => outer (sets index))) :=
  outer.iUnion_le sets

private def pairSets {α : Type u} (left right : Set α) : Nat → Set α
  | 0 => left
  | 1 => right
  | _ + 2 => Set.empty

private theorem iUnion_pairSets {α : Type u} (left right : Set α) :
    Set.iUnion (pairSets left right) = Set.union left right := by
  apply Set.ext
  intro value
  constructor
  · rintro ⟨index, member⟩
    cases index with
    | zero => exact Or.inl member
    | succ index =>
        cases index with
        | zero => exact Or.inr member
        | succ index => exact False.elim member
  · intro member
    cases member with
    | inl leftMember => exact ⟨0, leftMember⟩
    | inr rightMember => exact ⟨1, rightMember⟩

private def pairValues (left right : ENNReal) : Nat → ENNReal
  | 0 => left
  | 1 => right
  | _ + 2 => ENNReal.zero

private theorem pairValues_eq_add_singles (left right : ENNReal) :
    pairValues left right = fun index =>
      ENNReal.add (ENNReal.single 0 left index)
        (ENNReal.single 1 right index) := by
  funext index
  cases index with
  | zero => simp [pairValues, ENNReal.single, ENNReal.add_zero]
  | succ index =>
      cases index with
      | zero => simp [pairValues, ENNReal.single, ENNReal.zero_add]
      | succ index => simp [pairValues, ENNReal.single, ENNReal.zero_add]

private theorem tsum_pairValues (left right : ENNReal) :
    ENNReal.tsum (pairValues left right) = ENNReal.add left right := by
  rw [pairValues_eq_add_singles, ENNReal.tsum_add,
    ENNReal.tsum_single, ENNReal.tsum_single]

theorem union_apply_le {α : Type u} (outer : OuterMeasure α)
    (left right : Set α) :
    ENNReal.le (outer (Set.union left right))
      (ENNReal.add (outer left) (outer right)) := by
  have valuesEqual :
      (fun index => outer (pairSets left right index)) =
        pairValues (outer left) (outer right) := by
    funext index
    cases index with
    | zero => rfl
    | succ index =>
        cases index with
        | zero => rfl
        | succ index => exact empty_apply outer
  have included := outer.iUnion_le (pairSets left right)
  rw [iUnion_pairSets, valuesEqual, tsum_pairValues] at included
  exact included

theorem partition_apply_le {α : Type u} (outer : OuterMeasure α)
    (set region : Set α) :
    ENNReal.le (outer set)
      (ENNReal.add (outer (Set.inter set region))
        (outer (Set.difference set region))) := by
  classical
  have partition :
      Set.union (Set.inter set region) (Set.difference set region) = set := by
    apply Set.ext
    intro value
    constructor
    · intro member
      cases member with
      | inl inside => exact inside.1
      | inr outside => exact outside.1
    · intro member
      by_cases inside : region value
      · exact Or.inl ⟨member, inside⟩
      · exact Or.inr ⟨member, inside⟩
  have included := union_apply_le outer
    (Set.inter set region) (Set.difference set region)
  rw [partition] at included
  exact included

end OuterMeasure

end

end Problib.Measure
