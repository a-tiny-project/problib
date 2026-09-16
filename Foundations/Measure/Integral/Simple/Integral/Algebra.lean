module

public import Foundations.Measure.Integral.Simple.Integral.Basic

set_option autoImplicit false

/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl

Adapted from Mathlib/MeasureTheory/Function/SimpleFunc.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.
-/

namespace Foundations.Measure

open Foundations.Real

universe u v

namespace SimpleFunction

variable {alpha : Type u} {source : Space alpha}

private def fiberUnion (region : Set alpha)
    (function : SimpleFunction source) : List ENNReal → Set alpha
  | [] => Set.empty
  | value :: values => Set.union
      (Set.inter region (function.fiber value))
      (fiberUnion region function values)

private theorem mem_fiberUnion_iff (region : Set alpha)
    (function : SimpleFunction source) (values : List ENNReal)
    (input : alpha) :
    fiberUnion region function values input ↔
      ∃ value, value ∈ values ∧
        region input ∧ function input = value := by
  induction values with
  | nil =>
      simp [fiberUnion, Set.empty]
  | cons value values induction =>
      constructor
      · intro member
        rcases member with current | later
        · exact ⟨value, List.mem_cons_self, current.1,
            (function.mem_fiber_iff value input).mp current.2⟩
        · rcases induction.mp later with
            ⟨laterValue, laterMember, regionMember, equal⟩
          exact ⟨laterValue, List.mem_cons_of_mem value laterMember,
            regionMember, equal⟩
      · rintro ⟨memberValue, member, regionMember, equal⟩
        rcases List.mem_cons.mp member with current | later
        · exact Or.inl ⟨regionMember,
            (function.mem_fiber_iff value input).mpr
              (equal.trans current)⟩
        · exact Or.inr (induction.mpr
            ⟨memberValue, later, regionMember, equal⟩)

private theorem fiberUnion_all (region : Set alpha)
    (function : SimpleFunction source) :
    fiberUnion region function function.values = region := by
  apply Set.ext
  intro input
  constructor
  · intro member
    rcases (mem_fiberUnion_iff region function function.values input).mp
      member with ⟨_, _, regionMember, _⟩
    exact regionMember
  · intro member
    exact (mem_fiberUnion_iff region function function.values input).mpr
      ⟨function input, function.value_mem_values input, member, rfl⟩

private theorem fiberUnion_measurable (region : Set alpha)
    (regionMeasurable : source.Measurable region)
    (function : SimpleFunction source) (values : List ENNReal) :
    source.Measurable (fiberUnion region function values) := by
  induction values with
  | nil => exact source.empty
  | cons value values induction =>
      exact source.union
        (source.inter regionMeasurable (function.fiber_measurable value))
        induction

private theorem fiberUnion_disjoint_head (region : Set alpha)
    (function : SimpleFunction source) {value : ENNReal}
    {values : List ENNReal} (notMember : value ∉ values) :
    Set.Disjoint (Set.inter region (function.fiber value))
      (fiberUnion region function values) := by
  intro input current later
  rcases (mem_fiberUnion_iff region function values input).mp later with
    ⟨laterValue, laterMember, _, laterEqual⟩
  have currentEqual :=
    (function.mem_fiber_iff value input).mp current.2
  exact notMember (currentEqual.symm.trans laterEqual ▸ laterMember)

private theorem measure_fiberUnion (measure : Measure source)
    (region : Set alpha) (regionMeasurable : source.Measurable region)
    (function : SimpleFunction source) (values : List ENNReal)
    (nodup : values.Nodup) :
    measure (fiberUnion region function values) =
      finiteSum (values.map fun value =>
        measure (Set.inter region (function.fiber value))) := by
  induction values with
  | nil => exact measure.empty_apply
  | cons value values induction =>
      have notMember := (List.nodup_cons.mp nodup).1
      have tailNodup := (List.nodup_cons.mp nodup).2
      rw [fiberUnion, measure.union_disjoint
        (source.inter regionMeasurable (function.fiber_measurable value))
        (fiberUnion_measurable region regionMeasurable function values)
        (fiberUnion_disjoint_head region function notMember),
        induction tailNodup]
      rfl

public theorem measure_fiber_split (measure : Measure source)
    (region : Set alpha) (regionMeasurable : source.Measurable region)
    (function : SimpleFunction source) :
    measure region = finiteSum (function.values.map fun value =>
      measure (Set.inter region (function.fiber value))) := by
  calc
    measure region = measure
        (fiberUnion region function function.values) := by
      rw [fiberUnion_all]
    _ = finiteSum (function.values.map fun value =>
        measure (Set.inter region (function.fiber value))) :=
      measure_fiberUnion measure region regionMeasurable function
        function.values function.values_nodup

public theorem integral_mono_function
    {lower upper : SimpleFunction source}
    (included : PointwiseLe lower upper) (measure : Measure source) :
    ENNReal.le (integral lower measure) (integral upper measure) := by
  let mass := fun lowerValue upperValue =>
    measure (Set.inter (lower.fiber lowerValue)
      (upper.fiber upperValue))
  have lowerExpansion : integral lower measure =
      finiteSum (lower.values.map fun lowerValue =>
        finiteSum (upper.values.map fun upperValue =>
          ENNReal.mul lowerValue (mass lowerValue upperValue))) := by
    unfold integral
    apply congrArg finiteSum
    apply List.map_congr_left
    intro lowerValue _
    rw [measure_fiber_split measure (lower.fiber lowerValue)
      (lower.fiber_measurable lowerValue) upper]
    exact (finiteSum_map_mul_left upper.values lowerValue
      (mass lowerValue)).symm
  have interSwap (lowerValue upperValue : ENNReal) :
      Set.inter (upper.fiber upperValue) (lower.fiber lowerValue) =
        Set.inter (lower.fiber lowerValue) (upper.fiber upperValue) := by
    apply Set.ext
    intro input
    exact ⟨fun member => ⟨member.2, member.1⟩,
      fun member => ⟨member.2, member.1⟩⟩
  have upperExpansion : integral upper measure =
      finiteSum (lower.values.map fun lowerValue =>
        finiteSum (upper.values.map fun upperValue =>
          ENNReal.mul upperValue (mass lowerValue upperValue))) := by
    calc
      integral upper measure =
          finiteSum (upper.values.map fun upperValue =>
            finiteSum (lower.values.map fun lowerValue =>
              ENNReal.mul upperValue (mass lowerValue upperValue))) := by
        unfold integral
        apply congrArg finiteSum
        apply List.map_congr_left
        intro upperValue _
        rw [measure_fiber_split measure (upper.fiber upperValue)
          (upper.fiber_measurable upperValue) lower]
        apply Eq.trans _ (finiteSum_map_mul_left lower.values upperValue
          (fun lowerValue => mass lowerValue upperValue)).symm
        apply congrArg (ENNReal.mul upperValue)
        apply congrArg finiteSum
        apply List.map_congr_left
        intro lowerValue _
        rw [interSwap]
      _ = finiteSum (lower.values.map fun lowerValue =>
          finiteSum (upper.values.map fun upperValue =>
            ENNReal.mul upperValue (mass lowerValue upperValue))) :=
        finiteSum_comm upper.values lower.values fun upperValue lowerValue =>
          ENNReal.mul upperValue (mass lowerValue upperValue)
  rw [lowerExpansion, upperExpansion]
  apply finiteSum_map_mono
  intro lowerValue
  apply finiteSum_map_mono
  intro upperValue
  classical
  by_cases nonempty : Set.Nonempty
      (Set.inter (lower.fiber lowerValue) (upper.fiber upperValue))
  · rcases nonempty with ⟨input, lowerMember, upperMember⟩
    have lowerEqual :=
      (lower.mem_fiber_iff lowerValue input).mp lowerMember
    have upperEqual :=
      (upper.mem_fiber_iff upperValue input).mp upperMember
    have valuesIncluded := included input
    rw [lowerEqual, upperEqual] at valuesIncluded
    exact ENNReal.mulLeMulRight valuesIncluded (mass lowerValue upperValue)
  · have empty : Set.inter (lower.fiber lowerValue)
        (upper.fiber upperValue) = Set.empty := by
      apply Set.ext
      intro input
      exact ⟨fun member => False.elim (nonempty ⟨input, member⟩),
        False.elim⟩
    unfold mass
    rw [empty, measure.empty_apply, ENNReal.mulZero, ENNReal.mulZero]
    exact ENNReal.leRefl ENNReal.zero

public theorem integral_mono {lower upper : SimpleFunction source}
    (included : PointwiseLe lower upper) (measure : Measure source) :
    ENNReal.le (integral lower measure) (integral upper measure) :=
  integral_mono_function included measure

end SimpleFunction

end Foundations.Measure
