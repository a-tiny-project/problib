module

public import Foundations.Measure.Caratheodory
public import Foundations.Real.Series

set_option autoImplicit false

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Adapted from Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny stores only measurable content. Evaluation on every set is the canonical
outer envelope induced by that content.
-/

namespace Foundations.Measure

open Foundations.Real

universe u

/-- Countably additive content on one explicit measurable space. -/
public structure Measure {α : Type u} (space : Space α) where
  content : (set : Set α) → space.Measurable set → ENNReal
  empty : content Set.empty space.empty = ENNReal.zero
  content_iUnion_disjoint : ∀ (sets : Nat → Set α)
    (measurable : ∀ index, space.Measurable (sets index)),
    Set.PairwiseDisjoint sets →
    content (Set.iUnion sets) (space.iUnion measurable) =
      ENNReal.tsum (fun index => content (sets index) (measurable index))

namespace Measure

variable {α : Type u} {space : Space α}

@[ext] public theorem content_ext {left right : Measure space}
    (equal : ∀ set measurable,
      left.content set measurable = right.content set measurable) :
    left = right := by
  cases left with
  | mk leftContent leftEmpty leftUnion =>
      cases right with
      | mk rightContent rightEmpty rightUnion =>
          have contentEqual : leftContent = rightContent := by
            funext set measurable
            exact equal set measurable
          subst rightContent
          rfl

private def pairSets (left right : Set α) : Nat → Set α
  | 0 => left
  | 1 => right
  | _ + 2 => Set.empty

private theorem pairSets_iUnion (left right : Set α) :
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

private theorem pairSets_disjoint {left right : Set α}
    (disjoint : Set.Disjoint left right) :
    Set.PairwiseDisjoint (pairSets left right) := by
  intro first second different value firstMember secondMember
  cases first with
  | zero =>
      cases second with
      | zero => exact different rfl
      | succ second =>
          cases second with
          | zero => exact disjoint firstMember secondMember
          | succ second => exact secondMember
  | succ first =>
      cases first with
      | zero =>
          cases second with
          | zero => exact disjoint secondMember firstMember
          | succ second =>
              cases second with
              | zero => exact different rfl
              | succ second => exact secondMember
      | succ first => exact firstMember

private def pairValues (left right : ENNReal) : Nat → ENNReal
  | 0 => left
  | 1 => right
  | _ + 2 => ENNReal.zero

private theorem tsum_pairValues (left right : ENNReal) :
    ENNReal.tsum (pairValues left right) = ENNReal.add left right := by
  have equal : pairValues left right = fun index =>
      ENNReal.add (ENNReal.single 0 left index)
        (ENNReal.single 1 right index) := by
    funext index
    cases index with
    | zero => simp [pairValues, ENNReal.single, ENNReal.addZero]
    | succ index =>
        cases index with
        | zero => simp [pairValues, ENNReal.single, ENNReal.zeroAdd]
        | succ index => simp [pairValues, ENNReal.single, ENNReal.zeroAdd]
  rw [equal, ENNReal.tsumAdd, ENNReal.tsumSingle, ENNReal.tsumSingle]

public theorem content_union (μ : Measure space) {left right : Set α}
    (leftMeasurable : space.Measurable left)
    (rightMeasurable : space.Measurable right)
    (disjoint : Set.Disjoint left right) :
    μ.content (Set.union left right)
        (space.union leftMeasurable rightMeasurable) =
      ENNReal.add (μ.content left leftMeasurable)
        (μ.content right rightMeasurable) := by
  let sets := pairSets left right
  have measurable : ∀ index, space.Measurable (sets index) := by
    intro index
    cases index with
    | zero => exact leftMeasurable
    | succ index =>
        cases index with
        | zero => exact rightMeasurable
        | succ index => exact space.empty
  have exactUnion := μ.content_iUnion_disjoint sets measurable
    (pairSets_disjoint disjoint)
  have unionEqual : Set.iUnion sets = Set.union left right :=
    pairSets_iUnion left right
  calc
    μ.content (Set.union left right)
        (space.union leftMeasurable rightMeasurable) =
        ENNReal.tsum (fun index =>
          μ.content (sets index) (measurable index)) := by
      simpa only [unionEqual] using exactUnion
    _ = ENNReal.tsum (pairValues
        (μ.content left leftMeasurable)
        (μ.content right rightMeasurable)) := by
      apply ENNReal.tsumCongr
      intro index
      cases index with
      | zero => rfl
      | succ index =>
          cases index with
          | zero => rfl
          | succ index => exact μ.empty
    _ = ENNReal.add (μ.content left leftMeasurable)
        (μ.content right rightMeasurable) := tsum_pairValues _ _

public theorem content_mono (μ : Measure space) {left right : Set α}
    (leftMeasurable : space.Measurable left)
    (rightMeasurable : space.Measurable right)
    (included : Set.Subset left right) :
    ENNReal.le (μ.content left leftMeasurable)
      (μ.content right rightMeasurable) := by
  classical
  have differenceMeasurable := space.difference rightMeasurable leftMeasurable
  have disjoint : Set.Disjoint left (Set.difference right left) :=
    fun {_} leftMember differenceMember => differenceMember.2 leftMember
  have unionEqual : Set.union left (Set.difference right left) = right := by
    apply Set.ext
    intro value
    constructor
    · intro member
      cases member with
      | inl leftMember => exact included leftMember
      | inr differenceMember => exact differenceMember.1
    · intro rightMember
      by_cases leftMember : left value
      · exact Or.inl leftMember
      · exact Or.inr ⟨rightMember, leftMember⟩
  have additive := μ.content_union leftMeasurable differenceMeasurable disjoint
  have additive' : μ.content right rightMeasurable =
      ENNReal.add (μ.content left leftMeasurable)
        (μ.content (Set.difference right left) differenceMeasurable) := by
    simpa only [unionEqual] using additive
  rw [additive']
  have shifted := ENNReal.addLeAddLeft
    (ENNReal.zeroLe (μ.content (Set.difference right left)
      differenceMeasurable)) (μ.content left leftMeasurable)
  simpa only [ENNReal.addZero] using shifted

public theorem content_iUnion_le (μ : Measure space)
    (sets : Nat → Set α)
    (measurable : ∀ index, space.Measurable (sets index)) :
    ENNReal.le
      (μ.content (Set.iUnion sets) (space.iUnion measurable))
      (ENNReal.tsum (fun index =>
        μ.content (sets index) (measurable index))) := by
  let pieces := Set.disjointed sets
  have piecesMeasurable : ∀ index, space.Measurable (pieces index) :=
    space.disjointed_measurable measurable
  have exactUnion := μ.content_iUnion_disjoint pieces piecesMeasurable
    (Set.disjointed_pairwise sets)
  have unionEqual : Set.iUnion pieces = Set.iUnion sets :=
    Set.iUnion_disjointed sets
  have exactUnion' :
      μ.content (Set.iUnion sets) (space.iUnion measurable) =
        ENNReal.tsum (fun index =>
          μ.content (pieces index) (piecesMeasurable index)) := by
    simpa only [unionEqual] using exactUnion
  rw [exactUnion']
  apply ENNReal.tsumLeTsum
  intro index
  exact μ.content_mono (piecesMeasurable index) (measurable index)
    (Set.disjointed_subset sets index)

@[expose] public noncomputable def extendedContent
    (μ : Measure space) (set : Set α) : ENNReal := by
  classical
  exact if measurable : space.Measurable set then
    μ.content set measurable
  else
    ENNReal.top

@[simp] public theorem extendedContent_apply_measurable
    (μ : Measure space) {set : Set α} (measurable : space.Measurable set) :
    μ.extendedContent set = μ.content set measurable := by
  classical
  unfold extendedContent
  simp only [dif_pos measurable]

@[simp] public theorem extendedContent_empty (μ : Measure space) :
    μ.extendedContent Set.empty = ENNReal.zero := by
  rw [μ.extendedContent_apply_measurable space.empty, μ.empty]

private theorem extendedContent_mono_at (μ : Measure space)
    {set : Set α} (setMeasurable : space.Measurable set)
    {superset : Set α} (included : Set.Subset set superset) :
    ENNReal.le (μ.extendedContent set) (μ.extendedContent superset) := by
  classical
  by_cases supersetMeasurable : space.Measurable superset
  · rw [μ.extendedContent_apply_measurable setMeasurable,
      μ.extendedContent_apply_measurable supersetMeasurable]
    exact μ.content_mono setMeasurable supersetMeasurable included
  · unfold extendedContent
    simp only [dif_neg supersetMeasurable]
    exact ENNReal.leTop _

private theorem extendedContent_iUnion_le (μ : Measure space)
    (sets : Nat → Set α) :
    ENNReal.le (μ.extendedContent (Set.iUnion sets))
      (ENNReal.tsum (fun index => μ.extendedContent (sets index))) := by
  classical
  by_cases measurable : ∀ index, space.Measurable (sets index)
  · rw [μ.extendedContent_apply_measurable (space.iUnion measurable)]
    have included := μ.content_iUnion_le sets measurable
    exact ENNReal.leTrans included
      (ENNReal.tsumLeTsum fun index => by
        rw [μ.extendedContent_apply_measurable (measurable index)]
        exact ENNReal.leRefl _)
  · have missing : ∃ index, ¬space.Measurable (sets index) := by
      exact Classical.not_forall.mp measurable
    rcases missing with ⟨index, notMeasurable⟩
    have topIncluded := ENNReal.termLeTsum
      (fun current => μ.extendedContent (sets current)) index
    unfold extendedContent at topIncluded
    simp only [dif_neg notMeasurable] at topIncluded
    exact ENNReal.leTrans (ENNReal.leTop _) topIncluded

@[expose] public noncomputable def toOuterMeasure
    (μ : Measure space) : OuterMeasure α :=
  OuterMeasure.ofFunction μ.extendedContent μ.extendedContent_empty

public theorem toOuterMeasure_apply_measurable (μ : Measure space)
    {set : Set α} (measurable : space.Measurable set) :
    μ.toOuterMeasure set = μ.content set measurable := by
  calc
    μ.toOuterMeasure set = μ.extendedContent set :=
      OuterMeasure.ofFunction_eq μ.extendedContent μ.extendedContent_empty
        set (μ.extendedContent_mono_at measurable)
        μ.extendedContent_iUnion_le
    _ = μ.content set measurable :=
      μ.extendedContent_apply_measurable measurable

public noncomputable instance :
    CoeFun (Measure space) (fun _ => Set α → ENNReal) where
  coe μ := μ.toOuterMeasure

@[simp] public theorem empty_apply (μ : Measure space) :
    μ Set.empty = ENNReal.zero := by
  rw [μ.toOuterMeasure_apply_measurable space.empty, μ.empty]

public theorem mono (μ : Measure space) {left right : Set α}
    (included : Set.Subset left right) :
    ENNReal.le (μ left) (μ right) :=
  μ.toOuterMeasure.mono_apply included

public theorem iUnion_le (μ : Measure space) (sets : Nat → Set α) :
    ENNReal.le (μ (Set.iUnion sets))
      (ENNReal.tsum (fun index => μ (sets index))) :=
  μ.toOuterMeasure.iUnion_apply_le sets

public theorem union_le (μ : Measure space) (left right : Set α) :
    ENNReal.le (μ (Set.union left right))
      (ENNReal.add (μ left) (μ right)) :=
  μ.toOuterMeasure.union_apply_le left right

public theorem apply_measurable (μ : Measure space) {set : Set α}
    (measurable : space.Measurable set) :
    μ set = μ.content set measurable :=
  μ.toOuterMeasure_apply_measurable measurable

public theorem iUnion_disjoint (μ : Measure space)
    (sets : Nat → Set α)
    (measurable : ∀ index, space.Measurable (sets index))
    (disjoint : Set.PairwiseDisjoint sets) :
    μ (Set.iUnion sets) = ENNReal.tsum (fun index => μ (sets index)) := by
  rw [μ.apply_measurable (space.iUnion measurable),
    μ.content_iUnion_disjoint sets measurable disjoint]
  apply ENNReal.tsumCongr
  intro index
  exact (μ.apply_measurable (measurable index)).symm

public theorem union_disjoint (μ : Measure space) {left right : Set α}
    (leftMeasurable : space.Measurable left)
    (rightMeasurable : space.Measurable right)
    (disjoint : Set.Disjoint left right) :
    μ (Set.union left right) = ENNReal.add (μ left) (μ right) := by
  rw [μ.apply_measurable (space.union leftMeasurable rightMeasurable),
    μ.content_union leftMeasurable rightMeasurable disjoint,
    μ.apply_measurable leftMeasurable,
    μ.apply_measurable rightMeasurable]

public theorem isCaratheodory (μ : Measure space) {region : Set α}
    (regionMeasurable : space.Measurable region) :
    μ.toOuterMeasure.IsCaratheodory region := by
  unfold toOuterMeasure
  apply OuterMeasure.ofFunction_caratheodory
  intro set
  classical
  by_cases setMeasurable : space.Measurable set
  · have interMeasurable := space.inter setMeasurable regionMeasurable
    have differenceMeasurable :=
      space.difference setMeasurable regionMeasurable
    rw [μ.extendedContent_apply_measurable interMeasurable,
      μ.extendedContent_apply_measurable differenceMeasurable,
      μ.extendedContent_apply_measurable setMeasurable]
    have split := μ.content_union interMeasurable differenceMeasurable
      (Set.inter_difference_disjoint set region)
    have split' : μ.content set setMeasurable =
        ENNReal.add (μ.content (Set.inter set region) interMeasurable)
          (μ.content (Set.difference set region) differenceMeasurable) := by
      simpa only [Set.inter_union_difference] using split
    rw [← split']
    exact ENNReal.leRefl _
  · unfold extendedContent
    simp only [dif_neg setMeasurable]
    exact ENNReal.leTop _

@[ext] public theorem ext {left right : Measure space}
    (equal : ∀ set, space.Measurable set → left set = right set) :
    left = right := by
  apply content_ext
  intro set measurable
  rw [← left.apply_measurable measurable,
    ← right.apply_measurable measurable]
  exact equal set measurable

end Measure

namespace OuterMeasure

variable {α : Type u} {space : Space α}

/-- Restrict an outer measure to its Carathéodory measurable content. -/
public def toMeasure (outer : OuterMeasure α)
    (measurable : ∀ set, space.Measurable set → outer.IsCaratheodory set) :
    Measure space where
  content := fun set _ => outer set
  empty := outer.empty
  content_iUnion_disjoint := by
    intro sets setsMeasurable disjoint
    exact outer.iUnion_eq_of_caratheodory
      (fun index => measurable (sets index) (setsMeasurable index)) disjoint

public theorem toMeasure_apply (outer : OuterMeasure α)
    (measurable : ∀ set, space.Measurable set → outer.IsCaratheodory set)
    {set : Set α} (setMeasurable : space.Measurable set) :
    (outer.toMeasure measurable) set = outer set :=
  (outer.toMeasure measurable).apply_measurable setMeasurable

end OuterMeasure

end Foundations.Measure
