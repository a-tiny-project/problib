module

public import Foundations.Measure.Space

set_option autoImplicit false

/-
Copyright (c) 2021 Martin Zinkevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Martin Zinkevich, Rémy Degenne

Adapted from Mathlib/MeasureTheory/PiSystem.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny uses explicit spaces and requires unconditional intersection closure for
pi-systems.
-/

namespace Foundations.Measure

universe u

variable {α : Type u}

public section

/-- A pi-system is closed under every binary intersection. -/
@[expose] def PiSystem (sets : Set (Set α)) : Prop :=
  ∀ {left right}, sets left → sets right → sets (Set.inter left right)

namespace PiSystem

theorem measurable (space : Space α) : PiSystem space.Measurable :=
  fun leftMeasurable rightMeasurable =>
    space.inter leftMeasurable rightMeasurable

end PiSystem

/-- A Dynkin system contains the empty set, complements, and disjoint
countable unions. -/
structure DynkinSystem (α : Type u) where
  Contains : Set α → Prop
  empty : Contains Set.empty
  complement : ∀ {set}, Contains set → Contains (Set.complement set)
  iUnion : ∀ {sets : Nat → Set α}, Set.PairwiseDisjoint sets →
    (∀ index, Contains (sets index)) → Contains (Set.iUnion sets)

namespace DynkinSystem

@[ext] theorem ext {left right : DynkinSystem α}
    (equal : ∀ set, left.Contains set ↔ right.Contains set) :
    left = right := by
  cases left with
  | mk leftContains leftEmpty leftComplement leftIUnion =>
      cases right with
      | mk rightContains rightEmpty rightComplement rightIUnion =>
          have containsEqual : leftContains = rightContains :=
            funext fun set => propext (equal set)
          subst rightContains
          rfl

theorem univ (system : DynkinSystem α) :
    system.Contains Set.univ := by
  rw [← Set.complement_empty]
  exact system.complement system.empty

private def pairFamily (left right : Set α) : Nat → Set α
  | 0 => left
  | 1 => right
  | _ + 2 => Set.empty

private theorem pairFamilyPairwise {left right : Set α}
    (disjoint : Set.Disjoint left right) :
    Set.PairwiseDisjoint (pairFamily left right) := by
  intro first second different
  cases first with
  | zero =>
      cases second with
      | zero => exact False.elim (different rfl)
      | succ second =>
          cases second with
          | zero => exact disjoint
          | succ second => exact Set.disjoint_empty left
  | succ first =>
      cases first with
      | zero =>
          cases second with
          | zero => exact Set.disjoint_symm disjoint
          | succ second =>
              cases second with
              | zero => exact False.elim (different rfl)
              | succ second => exact Set.disjoint_empty right
      | succ first =>
          cases second with
          | zero => exact Set.empty_disjoint left
          | succ second =>
              cases second with
              | zero => exact Set.empty_disjoint right
              | succ second => exact Set.empty_disjoint Set.empty

private theorem iUnionPairFamily (left right : Set α) :
    Set.iUnion (pairFamily left right) = Set.union left right := by
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

theorem union {system : DynkinSystem α} {left right : Set α}
    (leftContains : system.Contains left)
    (rightContains : system.Contains right)
    (disjoint : Set.Disjoint left right) :
    system.Contains (Set.union left right) := by
  rw [← iUnionPairFamily left right]
  apply system.iUnion (pairFamilyPairwise disjoint)
  intro index
  cases index with
  | zero => exact leftContains
  | succ index =>
      cases index with
      | zero => exact rightContains
      | succ index => exact system.empty

theorem difference {system : DynkinSystem α} {larger smaller : Set α}
    (largerContains : system.Contains larger)
    (smallerContains : system.Contains smaller)
    (included : Set.Subset smaller larger) :
    system.Contains (Set.difference larger smaller) := by
  have disjoint : Set.Disjoint (Set.complement larger) smaller :=
    fun {_} largerAbsent smallerMember =>
      largerAbsent (included smallerMember)
  have joined := union (system.complement largerContains) smallerContains disjoint
  have result := system.complement joined
  have equal :
      Set.complement (Set.union (Set.complement larger) smaller) =
        Set.difference larger smaller := by
    classical
    apply Set.ext
    intro value
    change (¬(¬larger value ∨ smaller value)) ↔
      larger value ∧ ¬smaller value
    constructor
    · intro neither
      constructor
      · exact Classical.byContradiction fun largerAbsent =>
          neither (Or.inl largerAbsent)
      · intro smallerMember
        exact neither (Or.inr smallerMember)
    · rintro ⟨largerMember, smallerAbsent⟩ absentOrSmaller
      cases absentOrSmaller with
      | inl largerAbsent => exact largerAbsent largerMember
      | inr smallerMember => exact smallerAbsent smallerMember
  rw [← equal]
  exact result

/-- Intersect every member of a Dynkin system with one fixed member. -/
@[expose] def restrictOn (system : DynkinSystem α) {region : Set α}
    (regionContains : system.Contains region) : DynkinSystem α where
  Contains set := system.Contains (Set.inter set region)
  empty := by
    rw [Set.inter_empty_left]
    exact system.empty
  complement := by
    intro set setContains
    have result := difference regionContains setContains
      (Set.inter_subset_right set region)
    have equal :
        Set.difference region (Set.inter set region) =
          Set.inter (Set.complement set) region := by
      classical
      apply Set.ext
      intro value
      change (region value ∧ ¬(set value ∧ region value)) ↔
        ¬set value ∧ region value
      constructor
      · rintro ⟨regionMember, notBoth⟩
        exact ⟨fun setMember => notBoth ⟨setMember, regionMember⟩,
          regionMember⟩
      · rintro ⟨setAbsent, regionMember⟩
        exact ⟨regionMember, fun both => setAbsent both.1⟩
    rw [← equal]
    exact result
  iUnion := by
    intro sets disjoint contains
    have intersectionsDisjoint :
        Set.PairwiseDisjoint (fun index => Set.inter (sets index) region) := by
      intro first second different value firstMember secondMember
      exact disjoint first second different firstMember.1 secondMember.1
    have result := system.iUnion intersectionsDisjoint contains
    rw [← Set.iUnion_inter] at result
    exact result

/-- Membership in the least Dynkin system containing `generators`. -/
inductive Generated (generators : Set (Set α)) : Set α → Prop where
  | basic {set} : generators set → Generated generators set
  | empty : Generated generators Set.empty
  | complement {set} : Generated generators set →
      Generated generators (Set.complement set)
  | iUnion {sets : Nat → Set α} : Set.PairwiseDisjoint sets →
      (∀ index, Generated generators (sets index)) →
      Generated generators (Set.iUnion sets)

/-- The least Dynkin system containing `generators`. -/
@[expose] def generated (generators : Set (Set α)) : DynkinSystem α where
  Contains := Generated generators
  empty := Generated.empty
  complement := Generated.complement
  iUnion := Generated.iUnion

theorem generated_contains {generators : Set (Set α)} {set : Set α}
    (member : generators set) :
    (generated generators).Contains set :=
  Generated.basic member

theorem generated_minimal {generators : Set (Set α)}
    (target : DynkinSystem α)
    (contains : ∀ {set}, generators set → target.Contains set) :
    ∀ {set}, (generated generators).Contains set → target.Contains set := by
  intro set member
  induction member with
  | basic generatorMember => exact contains generatorMember
  | empty => exact target.empty
  | complement _ induction => exact target.complement induction
  | iUnion disjoint _ induction => exact target.iUnion disjoint induction

/-- Every measurable space is a Dynkin system. -/
@[expose] def ofSpace (space : Space α) : DynkinSystem α where
  Contains := space.Measurable
  empty := space.empty
  complement := space.complement
  iUnion := fun _ measurable => space.iUnion measurable

private theorem unionOfIntersectionClosed (system : DynkinSystem α)
    (intersection : ∀ {left right}, system.Contains left →
      system.Contains right → system.Contains (Set.inter left right))
    {left right : Set α} (leftContains : system.Contains left)
    (rightContains : system.Contains right) :
    system.Contains (Set.union left right) := by
  have result := system.complement
    (intersection (system.complement leftContains)
      (system.complement rightContains))
  have equal :
      Set.complement
          (Set.inter (Set.complement left) (Set.complement right)) =
        Set.union left right := by
    classical
    apply Set.ext
    intro value
    change (¬(¬left value ∧ ¬right value)) ↔ left value ∨ right value
    constructor
    · intro notNeither
      by_cases leftMember : left value
      · exact Or.inl leftMember
      · exact Or.inr (Classical.byContradiction fun rightAbsent =>
          notNeither ⟨leftMember, rightAbsent⟩)
    · intro member neither
      cases member with
      | inl leftMember => exact neither.1 leftMember
      | inr rightMember => exact neither.2 rightMember
  rw [← equal]
  exact result

private theorem prefixUnionContains (system : DynkinSystem α)
    (intersection : ∀ {left right}, system.Contains left →
      system.Contains right → system.Contains (Set.inter left right))
    {sets : Nat → Set α} (contains : ∀ index, system.Contains (sets index)) :
    ∀ count, system.Contains (Set.prefixUnion sets count) := by
  intro count
  induction count with
  | zero => exact system.empty
  | succ count induction =>
      exact unionOfIntersectionClosed system intersection induction
        (contains count)

/-- An intersection-closed Dynkin system is a measurable space. -/
@[expose] def toSpace (system : DynkinSystem α)
    (intersection : ∀ {left right}, system.Contains left →
      system.Contains right → system.Contains (Set.inter left right)) :
    Space α where
  Measurable := system.Contains
  empty := system.empty
  complement := system.complement
  iUnion := by
    intro sets contains
    have piecesContain :
        ∀ index, system.Contains (Set.disjointed sets index) := by
      intro index
      exact intersection (contains index)
        (system.complement
          (prefixUnionContains system intersection contains index))
    have result := system.iUnion (Set.disjointed_pairwise sets) piecesContain
    rw [Set.iUnion_disjointed] at result
    exact result

end DynkinSystem

end

end Foundations.Measure
