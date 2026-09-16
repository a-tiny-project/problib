module

public import Foundations.Measure.Integral.Simple.Integral.Partition
public import Foundations.Measure.Additive.Restrict

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

universe u

namespace SimpleFunction

variable {alpha : Type u} {source : Space alpha}

private theorem none_not_mem_some_map (values : List ENNReal) :
    (none : Option ENNReal) ∉ values.map some := by
  intro member
  rcases List.mem_map.mp member with ⟨value, _, impossible⟩
  cases impossible

private theorem nodup_some_map (values : List ENNReal)
    (nodup : values.Nodup) : (values.map some).Nodup := by
  induction values with
  | nil => exact List.nodup_nil
  | cons value values induction =>
      apply List.nodup_cons.mpr
      constructor
      · intro member
        rcases List.mem_map.mp member with ⟨other, otherMember, equal⟩
        have valueEqual : value = other := (Option.some.inj equal).symm
        exact (List.nodup_cons.mp nodup).1 (valueEqual ▸ otherMember)
      · exact induction (List.nodup_cons.mp nodup).2

/-- The integral of a constant is its value times the total mass. This also
holds on an empty carrier, where the total mass is zero. -/
public theorem constant_integral (source : Space alpha) (value : ENNReal)
    (measure : Measure source) :
    integral (constant source value) measure =
      ENNReal.mul value (measure Set.univ) := by
  have partition := integral_eq_partition
    (constant source value) measure [()]
    (by simp) (fun _ : Unit => Set.univ) (fun _ => value)
    (fun _ _ => source.univ)
    (by
      intro first _ second _ different
      cases first
      cases second
      exact False.elim (different rfl))
    (fun _ => ⟨(), List.mem_cons_self, True.intro⟩)
    (fun _ _ input _ => constant_apply source value input)
  simpa [finiteSum, ENNReal.addZero] using partition

/-- Restricting a simple function agrees with integrating against the
restricted measure. -/
public theorem integral_restrict (function : SimpleFunction source)
    (region : Set alpha) (regionMeasurable : source.Measurable region)
    (measure : Measure source) :
    integral (restrict function region regionMeasurable) measure =
      integral function (measure.restrict region) := by
  let indices : List (Option ENNReal) :=
    none :: function.values.map some
  let pieces : Option ENNReal → Set alpha
    | none => Set.complement region
    | some value => Set.inter region (function.fiber value)
  let coefficients : Option ENNReal → ENNReal
    | none => ENNReal.zero
    | some value => value
  have indicesNodup : indices.Nodup := by
    unfold indices
    exact List.nodup_cons.mpr ⟨none_not_mem_some_map function.values,
      nodup_some_map function.values function.values_nodup⟩
  have piecesMeasurable : ∀ index, index ∈ indices →
      source.Measurable (pieces index) := by
    intro index _
    cases index with
    | none => exact source.complement regionMeasurable
    | some value =>
        exact source.inter regionMeasurable
          (function.fiber_measurable value)
  have piecesDisjoint : ∀ first, first ∈ indices →
      ∀ second, second ∈ indices → first ≠ second →
        Set.Disjoint (pieces first) (pieces second) := by
    intro first _ second _ different
    cases first with
    | none =>
        cases second with
        | none => exact False.elim (different rfl)
        | some value =>
            intro input outside inside
            exact outside inside.1
    | some firstValue =>
        cases second with
        | none =>
            intro input inside outside
            exact outside inside.1
        | some secondValue =>
            intro input firstMember secondMember
            have valueEqual : firstValue = secondValue :=
              ((function.mem_fiber_iff firstValue input).mp
                firstMember.2).symm.trans
                ((function.mem_fiber_iff secondValue input).mp
                  secondMember.2)
            exact different (congrArg some valueEqual)
  have piecesCover : ∀ input, ∃ index, index ∈ indices ∧
      pieces index input := by
    intro input
    by_cases member : region input
    · refine ⟨some (function input), ?_, member, rfl⟩
      exact List.mem_cons_of_mem none (List.mem_map.mpr
        ⟨function input, function.value_mem_values input, rfl⟩)
    · exact ⟨none, List.mem_cons_self, member⟩
  have functionConstant : ∀ index, index ∈ indices →
      ∀ input, pieces index input →
        restrict function region regionMeasurable input =
          coefficients index := by
    intro index _ input member
    cases index with
    | none =>
        exact restrict_apply_of_not_mem function region regionMeasurable
          input member
    | some value =>
        calc
          restrict function region regionMeasurable input = function input :=
            restrict_apply_of_mem function region regionMeasurable input
              member.1
          _ = value := (function.mem_fiber_iff value input).mp member.2
  have partition := integral_eq_partition
    (restrict function region regionMeasurable) measure indices
    indicesNodup pieces coefficients piecesMeasurable piecesDisjoint
    piecesCover functionConstant
  rw [partition]
  unfold indices pieces coefficients integral
  simp only [List.map, finiteSum, ENNReal.zeroMul, ENNReal.zeroAdd]
  rw [List.map_map]
  apply congrArg finiteSum
  apply List.map_congr_left
  intro value _
  rw [measure.restrict_apply region (function.fiber_measurable value)]
  exact congrArg (ENNReal.mul value)
    (congrArg measure (Set.inter_comm region (function.fiber value)))

/-- The integral of a constant indicator is its value times the mass of the
indicated region. -/
public theorem indicator_integral (region : Set alpha)
    (regionMeasurable : source.Measurable region) (value : ENNReal)
    (measure : Measure source) :
    integral (indicator region regionMeasurable value) measure =
      ENNReal.mul value (measure region) := by
  have equal : ∀ input,
      indicator region regionMeasurable value input =
        restrict (constant source value) region regionMeasurable input := by
    intro input
    by_cases member : region input
    · rw [indicator_apply_of_mem region regionMeasurable value input member,
        restrict_apply_of_mem (constant source value) region
          regionMeasurable input member,
        constant_apply]
    · rw [indicator_apply_of_not_mem region regionMeasurable value input
          member,
        restrict_apply_of_not_mem (constant source value) region
          regionMeasurable input member]
  calc
    integral (indicator region regionMeasurable value) measure =
        integral (restrict (constant source value) region
          regionMeasurable) measure :=
      integral_congr equal measure
    _ = integral (constant source value) (measure.restrict region) :=
      integral_restrict (constant source value) region regionMeasurable
        measure
    _ = ENNReal.mul value ((measure.restrict region) Set.univ) :=
      constant_integral source value (measure.restrict region)
    _ = ENNReal.mul value (measure region) := by
      rw [measure.restrict_apply_univ region]

/-- Scalar multiplication commutes with simple integration. -/
public theorem smul_integral (factor : ENNReal)
    (function : SimpleFunction source) (measure : Measure source) :
    integral (smul factor function) measure =
      ENNReal.mul factor (integral function measure) := by
  have partition := integral_eq_partition (smul factor function) measure
    function.values function.values_nodup function.fiber
    (fun value => ENNReal.mul factor value)
    (fun value _ => function.fiber_measurable value)
    (by
      intro first _ second _ different input firstMember secondMember
      have equal : first = second :=
        ((function.mem_fiber_iff first input).mp firstMember).symm.trans
          ((function.mem_fiber_iff second input).mp secondMember)
      exact different equal)
    (fun input => ⟨function input, function.value_mem_values input, rfl⟩)
    (by
      intro value _ input member
      rw [smul_apply]
      exact congrArg (ENNReal.mul factor)
        ((function.mem_fiber_iff value input).mp member))
  rw [partition]
  unfold integral
  calc
    finiteSum (function.values.map fun value =>
        ENNReal.mul (ENNReal.mul factor value)
          (measure (function.fiber value))) =
        finiteSum (function.values.map fun value =>
          ENNReal.mul factor
            (ENNReal.mul value (measure (function.fiber value)))) := by
      apply congrArg finiteSum
      apply List.map_congr_left
      intro value _
      exact ENNReal.mulAssoc factor value
        (measure (function.fiber value))
    _ = ENNReal.mul factor (finiteSum (function.values.map fun value =>
          ENNReal.mul value (measure (function.fiber value)))) :=
      finiteSum_map_mul_left function.values factor
        (fun value => ENNReal.mul value (measure (function.fiber value)))

end SimpleFunction

end Foundations.Measure
