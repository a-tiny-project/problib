module

public import Foundations.Measure.Extended.Basic
import Std

set_option autoImplicit false

/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl

Adapted from Mathlib/MeasureTheory/Function/SimpleFunc.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny uses explicit measurable spaces and an exact duplicate-free list of
attained values instead of Mathlib's finite-range typeclass hierarchy.
-/

namespace Foundations.Measure

open Foundations.Real

universe u

/-- A function has finite range when a duplicate-free list records exactly
its attained values. This witness lives in `Prop`, so function equality is the
equality of simple functions. -/
@[expose] public def HasFiniteRange {alpha : Type u}
    (function : alpha → ENNReal) : Prop :=
  ∃ values : List ENNReal, values.Nodup ∧ ∀ value,
    value ∈ values ↔ ∃ input, function input = value

/-- A Borel-measurable extended-nonnegative function with finite range. -/
public structure SimpleFunction {alpha : Type u} (source : Space alpha) where
  toFunction : alpha → ENNReal
  fiberMeasurable : ∀ value, source.Measurable
    (Set.preimage toFunction (ennrealSingleton value))
  finiteRange : HasFiniteRange toFunction

namespace SimpleFunction

variable {alpha : Type u} {source : Space alpha}

noncomputable section

local instance ennrealDecidableEq : DecidableEq ENNReal :=
  Classical.typeDecidableEq ENNReal

public noncomputable instance :
    CoeFun (SimpleFunction source) (fun _ => alpha → ENNReal) where
  coe function := function.toFunction

@[ext] public theorem ext {left right : SimpleFunction source}
    (equal : ∀ input, left input = right input) : left = right := by
  cases left with
  | mk leftFunction leftMeasurable leftFinite =>
      cases right with
      | mk rightFunction rightMeasurable rightFinite =>
          have functionEqual : leftFunction = rightFunction := funext equal
          subst rightFunction
          rfl

private noncomputable def exactValues
    (function : alpha → ENNReal) (candidates : List ENNReal) :
    List ENNReal := by
  classical
  exact (candidates.filter fun value =>
    decide (∃ input, function input = value)).eraseDups

private theorem eraseDups_nodup : ∀ values : List ENNReal,
    values.eraseDups.Nodup
  | [] => by simp
  | value :: tail => by
      rw [List.eraseDups_cons]
      apply List.nodup_cons.mpr
      constructor
      · intro member
        have filteredMember : value ∈ tail.filter
            (fun candidate => !candidate == value) :=
          List.mem_eraseDups.mp member
        have unequal := (List.mem_filter.mp filteredMember).2
        simp at unequal
      · exact eraseDups_nodup _
termination_by values => values.length
decreasing_by
  exact Nat.lt_of_le_of_lt (List.length_filter_le _ _)
    (Nat.lt_succ_self _)

private theorem exactValues_nodup (function : alpha → ENNReal)
    (candidates : List ENNReal) :
    (exactValues function candidates).Nodup := by
  classical
  exact eraseDups_nodup _

private theorem mem_exactValues_iff (function : alpha → ENNReal)
    (candidates : List ENNReal)
    (covered : ∀ input, function input ∈ candidates) (value : ENNReal) :
    value ∈ exactValues function candidates ↔
      ∃ input, function input = value := by
  classical
  simp only [exactValues, List.mem_eraseDups, List.mem_filter,
    decide_eq_true_eq]
  constructor
  · exact fun member => member.2
  · rintro ⟨input, equal⟩
    exact ⟨equal ▸ covered input, input, equal⟩

/-- Package a finite-range function from a possibly redundant candidate list.
The proof-irrelevant witness is reduced to its exact attained range. -/
public noncomputable def ofCandidates
    (function : alpha → ENNReal)
    (candidates : List ENNReal)
    (covered : ∀ input, function input ∈ candidates)
    (fibersMeasurable : ∀ value, source.Measurable
      (Set.preimage function (ennrealSingleton value))) :
    SimpleFunction source where
  toFunction := function
  fiberMeasurable := fibersMeasurable
  finiteRange := ⟨exactValues function candidates,
    exactValues_nodup function candidates,
    mem_exactValues_iff function candidates covered⟩

@[simp] public theorem ofCandidates_apply
    (function : alpha → ENNReal)
    (candidates : List ENNReal)
    (covered : ∀ input, function input ∈ candidates)
    (fibersMeasurable : ∀ value, source.Measurable
      (Set.preimage function (ennrealSingleton value)))
    (input : alpha) :
    ofCandidates function candidates covered fibersMeasurable input =
      function input := by
  unfold ofCandidates
  rfl

/-- The canonical chosen list of exactly attained values. -/
@[expose] public noncomputable def values
    (function : SimpleFunction source) : List ENNReal :=
  Classical.choose function.finiteRange

public theorem values_nodup (function : SimpleFunction source) :
    function.values.Nodup :=
  (Classical.choose_spec function.finiteRange).1

public theorem mem_values_iff_attained (function : SimpleFunction source)
    (value : ENNReal) :
    value ∈ function.values ↔ ∃ input, function input = value :=
  (Classical.choose_spec function.finiteRange).2 value

public theorem value_mem_values (function : SimpleFunction source)
    (input : alpha) : function input ∈ function.values :=
  (function.mem_values_iff_attained (function input)).mpr ⟨input, rfl⟩

public theorem value_attained (function : SimpleFunction source)
    {value : ENNReal} (member : value ∈ function.values) :
    ∃ input, function input = value :=
  (function.mem_values_iff_attained value).mp member

@[expose] public def fiber (function : SimpleFunction source)
    (value : ENNReal) : Set alpha :=
  Set.preimage function (ennrealSingleton value)

public theorem mem_fiber_iff (function : SimpleFunction source)
    (value : ENNReal) (input : alpha) :
    fiber function value input ↔ function input = value :=
  Iff.rfl

private def listUnion (sets : List (Set alpha)) : Set alpha :=
  fun input => ∃ set, set ∈ sets ∧ set input

private theorem listUnion_measurable (sets : List (Set alpha))
    (measurable : ∀ set, set ∈ sets → source.Measurable set) :
    source.Measurable (listUnion sets) := by
  induction sets with
  | nil =>
      have equal : listUnion ([] : List (Set alpha)) = Set.empty := by
        apply Set.ext
        intro input
        simp [listUnion, Set.empty]
      rw [equal]
      exact source.empty
  | cons set sets induction =>
      have tailMeasurable := induction fun member memberInTail =>
        measurable member (List.mem_cons_of_mem set memberInTail)
      have equal : listUnion (set :: sets) = Set.union set (listUnion sets) := by
        apply Set.ext
        intro input
        simp [listUnion, Set.union]
      rw [equal]
      exact source.union (measurable set (List.mem_cons_self)) tailMeasurable

public theorem fiber_measurable (function : SimpleFunction source)
    (value : ENNReal) : source.Measurable (fiber function value) := by
  exact function.fiberMeasurable value

public theorem preimage_measurable (function : SimpleFunction source)
    (target : Set ENNReal) :
    source.Measurable (Set.preimage function target) := by
  classical
  let selected := function.values.filter fun value => decide (target value)
  let fibers := selected.map (fiber function)
  have fibersMeasurable : ∀ set, set ∈ fibers → source.Measurable set := by
    intro set member
    rcases List.mem_map.mp member with ⟨value, _, rfl⟩
    exact function.fiber_measurable value
  have unionMeasurable := listUnion_measurable fibers fibersMeasurable
  have equal : Set.preimage function target = listUnion fibers := by
    apply Set.ext
    intro input
    constructor
    · intro member
      have inValues := (function.mem_values_iff_attained (function input)).mpr
        ⟨input, rfl⟩
      have inSelected : function input ∈ selected := by
        exact List.mem_filter.mpr ⟨inValues, decide_eq_true member⟩
      exact ⟨fiber function (function input),
        List.mem_map.mpr ⟨function input, inSelected, rfl⟩, rfl⟩
    · rintro ⟨set, setMember, inputMember⟩
      rcases List.mem_map.mp setMember with ⟨value, valueMember, rfl⟩
      have targetMember : target value := by
        exact of_decide_eq_true (List.mem_filter.mp valueMember).2
      have functionEqual :=
        (mem_fiber_iff function value input).mp inputMember
      change target (function input)
      rw [functionEqual]
      exact targetMember
  rw [equal]
  exact unionMeasurable

public theorem measurable (function : SimpleFunction source) :
    ENNRealMeasurable source function := by
  intro threshold
  exact function.preimage_measurable (ennrealIoi threshold)

@[expose] public def PointwiseLe
    (lower : SimpleFunction source) (upper : alpha → ENNReal) : Prop :=
  ∀ input, ENNReal.le (lower input) (upper input)

public theorem pointwiseLe_refl (function : SimpleFunction source) :
    PointwiseLe function function :=
  fun input => ENNReal.leRefl (function input)

public theorem pointwiseLe_trans {first second : SimpleFunction source}
    {third : alpha → ENNReal}
    (firstSecond : PointwiseLe first second)
    (secondThird : PointwiseLe second third) :
    PointwiseLe first third :=
  fun input => ENNReal.leTrans (firstSecond input) (secondThird input)

private theorem constant_fiber_measurable (source : Space alpha)
    (value target : ENNReal) : source.Measurable
      (Set.preimage (fun _ : alpha => value) (ennrealSingleton target)) := by
  classical
  by_cases equal : value = target
  · have setEqual :
        Set.preimage (fun _ : alpha => value) (ennrealSingleton target) =
          Set.univ := by
      apply Set.ext
      intro input
      exact ⟨fun _ => True.intro, fun _ => equal⟩
    rw [setEqual]
    exact source.univ
  · have setEqual :
        Set.preimage (fun _ : alpha => value) (ennrealSingleton target) =
          Set.empty := by
      apply Set.ext
      intro input
      exact ⟨fun member => False.elim (equal member), False.elim⟩
    rw [setEqual]
    exact source.empty

/-- A constant simple function. -/
public noncomputable def constant (source : Space alpha)
    (value : ENNReal) : SimpleFunction source :=
  ofCandidates (fun _ => value) [value]
    (fun _ => List.mem_cons_self)
    (constant_fiber_measurable source value)

@[simp] public theorem constant_apply (source : Space alpha)
    (value : ENNReal) (input : alpha) :
    constant source value input = value := by
  classical
  unfold constant
  apply ofCandidates_apply

/-- Select between two simple functions on a measurable region. -/
public noncomputable def piecewise (region : Set alpha)
    (regionMeasurable : source.Measurable region)
    (inside outside : SimpleFunction source) : SimpleFunction source := by
  classical
  let function := ennrealPiecewise region inside outside
  refine ofCandidates function (inside.values ++ outside.values) ?_ ?_
  · intro input
    by_cases member : region input
    · have equal : function input = inside input := by
        simp [function, ennrealPiecewise, member]
      rw [equal]
      exact List.mem_append_left _ (inside.value_mem_values input)
    · have equal : function input = outside input := by
        simp [function, ennrealPiecewise, member]
      rw [equal]
      exact List.mem_append_right _ (outside.value_mem_values input)
  · intro value
    have measurable := source.union
      (source.inter regionMeasurable (inside.fiber_measurable value))
      (source.inter (source.complement regionMeasurable)
        (outside.fiber_measurable value))
    have equal : Set.preimage function (ennrealSingleton value) =
        Set.union
          (Set.inter region (fiber inside value))
          (Set.inter (Set.complement region) (fiber outside value)) := by
      apply Set.ext
      intro input
      by_cases member : region input
      · simp [function, ennrealPiecewise, fiber, ennrealSingleton,
          Set.preimage, Set.union, Set.inter, Set.complement, member]
      · simp [function, ennrealPiecewise, fiber, ennrealSingleton,
          Set.preimage, Set.union, Set.inter, Set.complement, member]
    rw [equal]
    exact measurable

@[simp] public theorem piecewise_apply (region : Set alpha)
    (regionMeasurable : source.Measurable region)
    (inside outside : SimpleFunction source) (input : alpha) :
    piecewise region regionMeasurable inside outside input =
      ennrealPiecewise region inside outside input := by
  classical
  unfold piecewise
  rw [ofCandidates_apply]

public theorem piecewise_apply_of_mem (region : Set alpha)
    (regionMeasurable : source.Measurable region)
    (inside outside : SimpleFunction source) (input : alpha)
    (member : region input) :
    piecewise region regionMeasurable inside outside input = inside input := by
  classical
  rw [piecewise_apply]
  simp [ennrealPiecewise, member]

public theorem piecewise_apply_of_not_mem (region : Set alpha)
    (regionMeasurable : source.Measurable region)
    (inside outside : SimpleFunction source) (input : alpha)
    (notMember : ¬region input) :
    piecewise region regionMeasurable inside outside input = outside input := by
  classical
  rw [piecewise_apply]
  simp [ennrealPiecewise, notMember]

/-- A constant on a measurable region and zero elsewhere. -/
public noncomputable def indicator (region : Set alpha)
    (regionMeasurable : source.Measurable region) (value : ENNReal) :
    SimpleFunction source :=
  piecewise region regionMeasurable
    (constant source value) (constant source ENNReal.zero)

@[simp] public theorem indicator_apply (region : Set alpha)
    (regionMeasurable : source.Measurable region) (value : ENNReal)
    (input : alpha) :
    indicator region regionMeasurable value input =
      ennrealIndicator region (fun _ => value) input := by
  classical
  unfold indicator
  rw [piecewise_apply]
  unfold ennrealIndicator
  congr

public theorem indicator_apply_of_mem (region : Set alpha)
    (regionMeasurable : source.Measurable region) (value : ENNReal)
    (input : alpha) (member : region input) :
    indicator region regionMeasurable value input = value := by
  unfold indicator
  calc
    piecewise region regionMeasurable
        (constant source value) (constant source ENNReal.zero) input =
        constant source value input :=
      piecewise_apply_of_mem region regionMeasurable _ _ input member
    _ = value := constant_apply source value input

public theorem indicator_apply_of_not_mem (region : Set alpha)
    (regionMeasurable : source.Measurable region) (value : ENNReal)
    (input : alpha) (notMember : ¬region input) :
    indicator region regionMeasurable value input = ENNReal.zero := by
  unfold indicator
  calc
    piecewise region regionMeasurable
        (constant source value) (constant source ENNReal.zero) input =
        constant source ENNReal.zero input :=
      piecewise_apply_of_not_mem region regionMeasurable _ _ input notMember
    _ = ENNReal.zero := constant_apply source ENNReal.zero input

end

end SimpleFunction

end Foundations.Measure
