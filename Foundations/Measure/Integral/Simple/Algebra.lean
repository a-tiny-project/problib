module

public import Foundations.Measure.Integral.Simple.Basic
public import Foundations.Measure.Extended.Order

set_option autoImplicit false

/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl

Adapted from Mathlib/MeasureTheory/Function/SimpleFunc.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny derives algebra directly from finite measurable fibers.
-/

namespace Foundations.Measure

open Foundations.Real

universe u v

namespace SimpleFunction

variable {alpha : Type u} {source : Space alpha}

noncomputable section

private def finiteUnion (sets : List (Set alpha)) : Set alpha :=
  fun input => ∃ set, set ∈ sets ∧ set input

private theorem finiteUnion_measurable (sets : List (Set alpha))
    (measurable : ∀ set, set ∈ sets → source.Measurable set) :
    source.Measurable (finiteUnion sets) := by
  induction sets with
  | nil =>
      have equal : finiteUnion ([] : List (Set alpha)) = Set.empty := by
        apply Set.ext
        intro input
        simp [finiteUnion, Set.empty]
      rw [equal]
      exact source.empty
  | cons set sets induction =>
      have tailMeasurable := induction fun member memberInTail =>
        measurable member (List.mem_cons_of_mem set memberInTail)
      have equal : finiteUnion (set :: sets) =
          Set.union set (finiteUnion sets) := by
        apply Set.ext
        intro input
        simp [finiteUnion, Set.union]
      rw [equal]
      exact source.union (measurable set List.mem_cons_self) tailMeasurable

/-- Apply an arbitrary transformation to a simple function. Finite range makes
the result measurable without a separate measurability premise. -/
public noncomputable def map (function : SimpleFunction source)
    (transform : ENNReal → ENNReal) : SimpleFunction source := by
  let mapped := fun input => transform (function input)
  refine ofCandidates mapped (function.values.map transform) ?_ ?_
  · intro input
    exact List.mem_map.mpr
      ⟨function input, function.value_mem_values input, rfl⟩
  · intro value
    have measurable := function.preimage_measurable
      (fun candidate => transform candidate = value)
    have equal : Set.preimage mapped (ennrealSingleton value) =
        Set.preimage function (fun candidate => transform candidate = value) :=
      rfl
    rw [equal]
    exact measurable

@[simp] public theorem map_apply (function : SimpleFunction source)
    (transform : ENNReal → ENNReal) (input : alpha) :
    map function transform input = transform (function input) := by
  unfold map
  rw [ofCandidates_apply]

/-- Precompose a simple function with a measurable map of its domain. -/
public noncomputable def comp {beta : Type v} {target : Space beta}
    (function : SimpleFunction target) (before : alpha → beta)
    (beforeMeasurable : MeasurableMap source target before) :
    SimpleFunction source := by
  let composed := fun input => function (before input)
  refine ofCandidates composed function.values ?_ ?_
  · intro input
    exact function.value_mem_values (before input)
  · intro value
    have measurable := beforeMeasurable (function.fiber_measurable value)
    exact measurable

@[simp] public theorem comp_apply {beta : Type v} {target : Space beta}
    (function : SimpleFunction target) (before : alpha → beta)
    (beforeMeasurable : MeasurableMap source target before) (input : alpha) :
    comp function before beforeMeasurable input = function (before input) := by
  unfold comp
  rw [ofCandidates_apply]

/-- Combine two simple functions pointwise. -/
public noncomputable def combine (left right : SimpleFunction source)
    (operation : ENNReal → ENNReal → ENNReal) :
    SimpleFunction source := by
  let combined := fun input => operation (left input) (right input)
  let candidates := left.values.flatMap fun leftValue =>
    right.values.map (operation leftValue)
  refine ofCandidates combined candidates ?_ ?_
  · intro input
    apply List.mem_flatMap.mpr
    exact ⟨left input, left.value_mem_values input,
      List.mem_map.mpr
        ⟨right input, right.value_mem_values input, rfl⟩⟩
  · intro value
    let pieces := left.values.map fun leftValue =>
      Set.inter (fiber left leftValue)
        (Set.preimage right
          (fun rightValue => operation leftValue rightValue = value))
    have piecesMeasurable : ∀ set, set ∈ pieces →
        source.Measurable set := by
      intro set member
      rcases List.mem_map.mp member with ⟨leftValue, _, rfl⟩
      exact source.inter (left.fiber_measurable leftValue)
        (right.preimage_measurable
          (fun rightValue => operation leftValue rightValue = value))
    have unionMeasurable := finiteUnion_measurable pieces piecesMeasurable
    have equal : Set.preimage combined (ennrealSingleton value) =
        finiteUnion pieces := by
      apply Set.ext
      intro input
      constructor
      · intro member
        refine ⟨Set.inter (fiber left (left input))
            (Set.preimage right
              (fun rightValue => operation (left input) rightValue = value)),
          ?_, rfl, member⟩
        exact List.mem_map.mpr
          ⟨left input, left.value_mem_values input, rfl⟩
      · rintro ⟨set, setMember, inputMember⟩
        rcases List.mem_map.mp setMember with
          ⟨leftValue, _, rfl⟩
        rcases inputMember with ⟨leftMember, rightMember⟩
        change operation (left input) (right input) = value
        have leftEqual := (mem_fiber_iff left leftValue input).mp leftMember
        rw [leftEqual]
        exact rightMember
    rw [equal]
    exact unionMeasurable

@[simp] public theorem combine_apply (left right : SimpleFunction source)
    (operation : ENNReal → ENNReal → ENNReal) (input : alpha) :
    combine left right operation input =
      operation (left input) (right input) := by
  unfold combine
  rw [ofCandidates_apply]

public noncomputable def zero (source : Space alpha) :
    SimpleFunction source :=
  constant source ENNReal.zero

@[simp] public theorem zero_apply (source : Space alpha) (input : alpha) :
    zero source input = ENNReal.zero :=
  constant_apply source ENNReal.zero input

public noncomputable def add (left right : SimpleFunction source) :
    SimpleFunction source :=
  combine left right ENNReal.add

@[simp] public theorem add_apply (left right : SimpleFunction source)
    (input : alpha) :
    add left right input = ENNReal.add (left input) (right input) :=
  combine_apply left right ENNReal.add input

@[expose] public noncomputable def maximum
    (left right : ENNReal) : ENNReal := by
  classical
  exact if ENNReal.le left right then right else left

private theorem le_maximum_left (left right : ENNReal) :
    ENNReal.le left (maximum left right) := by
  classical
  unfold maximum
  split
  · assumption
  · exact ENNReal.leRefl left

private theorem le_maximum_right (left right : ENNReal) :
    ENNReal.le right (maximum left right) := by
  classical
  unfold maximum
  split
  · exact ENNReal.leRefl right
  · rename_i notIncluded
    exact Or.resolve_left (ENNReal.leTotal left right) notIncluded

private theorem maximum_le {left right upper : ENNReal}
    (leftUpper : ENNReal.le left upper)
    (rightUpper : ENNReal.le right upper) :
    ENNReal.le (maximum left right) upper := by
  classical
  unfold maximum
  split
  · exact rightUpper
  · exact leftUpper

/-- The pointwise maximum of two simple functions. -/
public noncomputable def sup (left right : SimpleFunction source) :
    SimpleFunction source :=
  combine left right maximum

@[simp] public theorem sup_apply (left right : SimpleFunction source)
    (input : alpha) :
    sup left right input = maximum (left input) (right input) :=
  combine_apply left right maximum input

public theorem le_sup_left (left right : SimpleFunction source) :
    PointwiseLe left (sup left right) := by
  intro input
  rw [sup_apply]
  exact le_maximum_left _ _

public theorem le_sup_right (left right : SimpleFunction source) :
    PointwiseLe right (sup left right) := by
  intro input
  rw [sup_apply]
  exact le_maximum_right _ _

public theorem sup_le {left right : SimpleFunction source}
    {upper : alpha → ENNReal}
    (leftUpper : PointwiseLe left upper)
    (rightUpper : PointwiseLe right upper) :
    PointwiseLe (sup left right) upper := by
  intro input
  rw [sup_apply]
  exact maximum_le (leftUpper input) (rightUpper input)

public noncomputable def mul (left right : SimpleFunction source) :
    SimpleFunction source :=
  combine left right ENNReal.mul

@[simp] public theorem mul_apply (left right : SimpleFunction source)
    (input : alpha) :
    mul left right input = ENNReal.mul (left input) (right input) :=
  combine_apply left right ENNReal.mul input

public noncomputable def sub (left right : SimpleFunction source) :
    SimpleFunction source :=
  combine left right ENNReal.sub

@[simp] public theorem sub_apply (left right : SimpleFunction source)
    (input : alpha) :
    sub left right input = ENNReal.sub (left input) (right input) :=
  combine_apply left right ENNReal.sub input

public noncomputable def smul (factor : ENNReal)
    (function : SimpleFunction source) : SimpleFunction source :=
  map function (ENNReal.mul factor)

@[simp] public theorem smul_apply (factor : ENNReal)
    (function : SimpleFunction source) (input : alpha) :
    smul factor function input = ENNReal.mul factor (function input) :=
  map_apply function (ENNReal.mul factor) input

/-- Keep a simple function on a measurable region and set it to zero outside. -/
public noncomputable def restrict (function : SimpleFunction source)
    (region : Set alpha) (regionMeasurable : source.Measurable region) :
    SimpleFunction source :=
  piecewise region regionMeasurable function (zero source)

public theorem restrict_apply (function : SimpleFunction source)
    (region : Set alpha) (regionMeasurable : source.Measurable region)
    (input : alpha) :
    restrict function region regionMeasurable input =
      ennrealIndicator region function input := by
  classical
  unfold restrict
  rw [piecewise_apply]
  unfold ennrealIndicator ennrealPiecewise
  by_cases member : region input
  · simp [member]
  · simp [member, zero_apply]

public theorem restrict_apply_of_mem (function : SimpleFunction source)
    (region : Set alpha) (regionMeasurable : source.Measurable region)
    (input : alpha) (member : region input) :
    restrict function region regionMeasurable input = function input :=
  piecewise_apply_of_mem region regionMeasurable _ _ input member

public theorem restrict_apply_of_not_mem (function : SimpleFunction source)
    (region : Set alpha) (regionMeasurable : source.Measurable region)
    (input : alpha) (notMember : ¬region input) :
    restrict function region regionMeasurable input = ENNReal.zero := by
  unfold restrict
  rw [piecewise_apply_of_not_mem region regionMeasurable _ _ input notMember]
  exact zero_apply source input

public theorem comparison_measurable (lower : SimpleFunction source)
    {upper : alpha → ENNReal}
    (upperMeasurable : ENNRealMeasurable source upper) :
    source.Measurable
      (fun input => ENNReal.le (lower input) (upper input)) :=
  ENNRealMeasurable.le_set lower.measurable upperMeasurable

public theorem reverseComparison_measurable
    {lower : alpha → ENNReal}
    (lowerMeasurable : ENNRealMeasurable source lower)
    (upper : SimpleFunction source) :
    source.Measurable
      (fun input => ENNReal.le (lower input) (upper input)) :=
  ENNRealMeasurable.le_set lowerMeasurable upper.measurable

end

end SimpleFunction

end Foundations.Measure
