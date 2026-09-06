module

public import Foundations.Measure.Outer
public import Foundations.Measure.Set.Family

set_option autoImplicit false

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Adapted from Mathlib/MeasureTheory/OuterMeasure/Caratheodory.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny uses explicit set operations, an explicit extended-nonnegative-real order,
and natural-number indexed families. The proof is independent of Mathlib.
-/

namespace Foundations.Measure

open Foundations.Real

universe u

namespace OuterMeasure

variable {α : Type u}

@[expose] public def IsCaratheodory (outer : OuterMeasure α)
    (region : Set α) : Prop :=
  ∀ set, outer set = ENNReal.add
    (outer (Set.inter set region))
    (outer (Set.difference set region))

private theorem interEmpty (set : Set α) :
    Set.inter set Set.empty = Set.empty := by
  apply Set.ext
  intro value
  exact ⟨fun member => member.2, False.elim⟩

private theorem differenceEmpty (set : Set α) :
    Set.difference set Set.empty = set := by
  apply Set.ext
  intro value
  constructor
  · exact fun member => member.1
  · exact fun member => ⟨member, fun absent => absent⟩

private theorem differenceComplement (set region : Set α) :
    Set.difference set (Set.complement region) = Set.inter set region := by
  classical
  apply Set.ext
  intro value
  constructor
  · intro member
    exact ⟨member.1, Classical.byContradiction fun absent => member.2 absent⟩
  · intro member
    exact ⟨member.1, fun absent => absent member.2⟩

private theorem interUnionSplit (set left right : Set α) :
    Set.inter set (Set.union left right) =
      Set.union (Set.inter set left)
        (Set.inter (Set.difference set left) right) := by
  classical
  apply Set.ext
  intro value
  constructor
  · rintro ⟨setMember, leftMember | rightMember⟩
    · exact Or.inl ⟨setMember, leftMember⟩
    · by_cases inLeft : left value
      · exact Or.inl ⟨setMember, inLeft⟩
      · exact Or.inr ⟨⟨setMember, inLeft⟩, rightMember⟩
  · intro member
    cases member with
    | inl member => exact ⟨member.1, Or.inl member.2⟩
    | inr member => exact ⟨member.1.1, Or.inr member.2⟩

private theorem differenceUnion (set left right : Set α) :
    Set.difference set (Set.union left right) =
      Set.difference (Set.difference set left) right := by
  apply Set.ext
  intro value
  constructor
  · intro member
    exact ⟨⟨member.1, fun inLeft => member.2 (Or.inl inLeft)⟩,
      fun inRight => member.2 (Or.inr inRight)⟩
  · intro member
    exact ⟨member.1.1, fun unionMember => unionMember.elim member.1.2 member.2⟩

public theorem isCaratheodory_iff_reverse
    (outer : OuterMeasure α) (region : Set α) :
    outer.IsCaratheodory region ↔
      ∀ set, ENNReal.le
        (ENNReal.add (outer (Set.inter set region))
          (outer (Set.difference set region)))
        (outer set) := by
  constructor
  · intro measurable set
    rw [← measurable set]
    exact ENNReal.leRefl _
  · intro reverse set
    exact ENNReal.leAntisymm
      (outer.partition_apply_le set region)
      (reverse set)

public theorem isCaratheodory_empty (outer : OuterMeasure α) :
    outer.IsCaratheodory Set.empty := by
  apply (isCaratheodory_iff_reverse outer Set.empty).mpr
  intro set
  rw [interEmpty, differenceEmpty, outer.empty_apply, ENNReal.zeroAdd]
  exact ENNReal.leRefl _

public theorem isCaratheodory_complement (outer : OuterMeasure α)
    {region : Set α} (measurable : outer.IsCaratheodory region) :
    outer.IsCaratheodory (Set.complement region) := by
  intro set
  calc
    outer set = ENNReal.add
        (outer (Set.inter set region))
        (outer (Set.difference set region)) := measurable set
    _ = ENNReal.add
        (outer (Set.difference set region))
        (outer (Set.inter set region)) := ENNReal.addComm _ _
    _ = ENNReal.add
        (outer (Set.inter set (Set.complement region)))
        (outer (Set.difference set (Set.complement region))) := by
      rw [differenceComplement]
      rfl

public theorem isCaratheodory_union (outer : OuterMeasure α)
    {left right : Set α}
    (leftMeasurable : outer.IsCaratheodory left)
    (rightMeasurable : outer.IsCaratheodory right) :
    outer.IsCaratheodory (Set.union left right) := by
  apply (isCaratheodory_iff_reverse outer (Set.union left right)).mpr
  intro set
  have unionBound : ENNReal.le
      (outer (Set.inter set (Set.union left right)))
      (ENNReal.add (outer (Set.inter set left))
        (outer (Set.inter (Set.difference set left) right))) := by
    rw [interUnionSplit]
    exact outer.union_apply_le _ _
  have rightSplit := rightMeasurable (Set.difference set left)
  have bound := ENNReal.addLeAddRight unionBound
    (outer (Set.difference set (Set.union left right)))
  rw [differenceUnion, ENNReal.addAssoc, ← rightSplit,
    ← leftMeasurable set] at bound
  rw [differenceUnion]
  exact bound

public theorem isCaratheodory_inter (outer : OuterMeasure α)
    {left right : Set α}
    (leftMeasurable : outer.IsCaratheodory left)
    (rightMeasurable : outer.IsCaratheodory right) :
    outer.IsCaratheodory (Set.inter left right) := by
  have unionMeasurable := outer.isCaratheodory_union
    (outer.isCaratheodory_complement leftMeasurable)
    (outer.isCaratheodory_complement rightMeasurable)
  have complementMeasurable := outer.isCaratheodory_complement unionMeasurable
  have equal :
      Set.complement
        (Set.union (Set.complement left) (Set.complement right)) =
      Set.inter left right := by
    classical
    apply Set.ext
    intro value
    constructor
    · intro neither
      exact ⟨Classical.byContradiction fun absent => neither (Or.inl absent),
        Classical.byContradiction fun absent => neither (Or.inr absent)⟩
    · rintro ⟨inLeft, inRight⟩ (absentLeft | absentRight)
      · exact absentLeft inLeft
      · exact absentRight inRight
  rw [← equal]
  exact complementMeasurable

public theorem isCaratheodory_difference (outer : OuterMeasure α)
    {left right : Set α}
    (leftMeasurable : outer.IsCaratheodory left)
    (rightMeasurable : outer.IsCaratheodory right) :
    outer.IsCaratheodory (Set.difference left right) :=
  outer.isCaratheodory_inter leftMeasurable
    (outer.isCaratheodory_complement rightMeasurable)

public theorem isCaratheodory_prefixUnion (outer : OuterMeasure α)
    {sets : Nat → Set α} (measurable : ∀ index,
      outer.IsCaratheodory (sets index)) :
    ∀ count, outer.IsCaratheodory (Set.prefixUnion sets count)
  | 0 => outer.isCaratheodory_empty
  | count + 1 => outer.isCaratheodory_union
      (outer.isCaratheodory_prefixUnion measurable count)
      (measurable count)

private theorem interUnionApply (outer : OuterMeasure α)
    {left right : Set α} (disjoint : Set.Disjoint left right)
    (leftMeasurable : outer.IsCaratheodory left) (set : Set α) :
    outer (Set.inter set (Set.union left right)) =
      ENNReal.add (outer (Set.inter set left))
        (outer (Set.inter set right)) := by
  have first :
      Set.inter (Set.inter set (Set.union left right)) left =
        Set.inter set left := by
    apply Set.ext
    intro value
    constructor
    · exact fun member => ⟨member.1.1, member.2⟩
    · exact fun member => ⟨⟨member.1, Or.inl member.2⟩, member.2⟩
  have second :
      Set.difference (Set.inter set (Set.union left right)) left =
        Set.inter set right := by
    apply Set.ext
    intro value
    constructor
    · rintro ⟨⟨setMember, leftMember | rightMember⟩, notLeft⟩
      · exact False.elim (notLeft leftMember)
      · exact ⟨setMember, rightMember⟩
    · intro member
      exact ⟨⟨member.1, Or.inr member.2⟩,
        fun inLeft => disjoint inLeft member.2⟩
  calc
    outer (Set.inter set (Set.union left right)) =
        ENNReal.add
          (outer (Set.inter (Set.inter set (Set.union left right)) left))
          (outer (Set.difference
            (Set.inter set (Set.union left right)) left)) :=
      leftMeasurable _
    _ = ENNReal.add (outer (Set.inter set left))
        (outer (Set.inter set right)) := by rw [first, second]

public theorem partialSum_inter_eq (outer : OuterMeasure α)
    {sets : Nat → Set α}
    (measurable : ∀ index, outer.IsCaratheodory (sets index))
    (disjoint : Set.PairwiseDisjoint sets) (set : Set α) :
    ∀ count,
      ENNReal.partialSum (fun index => outer (Set.inter set (sets index))) count =
        outer (Set.inter set (Set.prefixUnion sets count))
  | 0 => by rw [ENNReal.partialSum, Set.prefixUnion, interEmpty,
      outer.empty_apply]
  | count + 1 => by
      rw [ENNReal.partialSum,
        outer.partialSum_inter_eq measurable disjoint set count,
        Set.prefixUnion]
      exact (interUnionApply outer
        (Set.prefixUnion_disjoint_right disjoint count)
        (outer.isCaratheodory_prefixUnion measurable count) set).symm

end OuterMeasure

end Foundations.Measure
