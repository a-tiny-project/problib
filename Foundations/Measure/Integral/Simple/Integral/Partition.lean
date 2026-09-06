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

private def pieceUnion {Index : Type v} (pieces : Index → Set alpha) :
    List Index → Set alpha
  | [] => Set.empty
  | index :: indices =>
      Set.union (pieces index) (pieceUnion pieces indices)

private theorem mem_pieceUnion_iff {Index : Type v}
    (pieces : Index → Set alpha) (indices : List Index) (input : alpha) :
    pieceUnion pieces indices input ↔
      ∃ index, index ∈ indices ∧ pieces index input := by
  induction indices with
  | nil => simp [pieceUnion, Set.empty]
  | cons index indices induction =>
      constructor
      · intro member
        rcases member with current | later
        · exact ⟨index, List.mem_cons_self, current⟩
        · rcases induction.mp later with ⟨laterIndex, inTail, present⟩
          exact ⟨laterIndex, List.mem_cons_of_mem index inTail, present⟩
      · rintro ⟨memberIndex, member, present⟩
        rcases List.mem_cons.mp member with current | later
        · subst memberIndex
          exact Or.inl present
        · exact Or.inr (induction.mpr ⟨memberIndex, later, present⟩)

private theorem pieceUnion_measurable {Index : Type v}
    (pieces : Index → Set alpha) (indices : List Index)
    (measurable : ∀ index, index ∈ indices →
      source.Measurable (pieces index)) :
    source.Measurable (pieceUnion pieces indices) := by
  induction indices with
  | nil => exact source.empty
  | cons index indices induction =>
      exact source.union
        (measurable index List.mem_cons_self)
        (induction fun tailIndex tailMember =>
          measurable tailIndex (List.mem_cons_of_mem index tailMember))

private theorem head_disjoint_pieceUnion {Index : Type v}
    (pieces : Index → Set alpha) (head : Index) (tail : List Index)
    (headNotTail : head ∉ tail)
    (disjoint : ∀ first, first ∈ head :: tail →
      ∀ second, second ∈ head :: tail → first ≠ second →
        Set.Disjoint (pieces first) (pieces second)) :
    Set.Disjoint (pieces head) (pieceUnion pieces tail) := by
  intro input headMember tailMember
  rcases (mem_pieceUnion_iff pieces tail input).mp tailMember with
    ⟨tailIndex, tailIndexMember, indexMember⟩
  have different : head ≠ tailIndex := by
    intro equal
    exact headNotTail (equal ▸ tailIndexMember)
  exact disjoint head List.mem_cons_self tailIndex
    (List.mem_cons_of_mem head tailIndexMember) different
    headMember indexMember

private theorem measure_pieceUnion {Index : Type v}
    (measure : Measure source) (pieces : Index → Set alpha)
    (indices : List Index) (nodup : indices.Nodup)
    (measurable : ∀ index, index ∈ indices →
      source.Measurable (pieces index))
    (disjoint : ∀ first, first ∈ indices →
      ∀ second, second ∈ indices → first ≠ second →
        Set.Disjoint (pieces first) (pieces second)) :
    measure (pieceUnion pieces indices) =
      finiteSum (indices.map fun index => measure (pieces index)) := by
  induction indices with
  | nil => exact measure.empty_apply
  | cons index indices induction =>
      have headNotTail := (List.nodup_cons.mp nodup).1
      have tailNodup := (List.nodup_cons.mp nodup).2
      rw [pieceUnion, measure.union_disjoint
        (measurable index List.mem_cons_self)
        (pieceUnion_measurable pieces indices fun tailIndex tailMember =>
          measurable tailIndex (List.mem_cons_of_mem index tailMember))
        (head_disjoint_pieceUnion pieces index indices headNotTail disjoint),
        induction tailNodup
          (fun tailIndex tailMember =>
            measurable tailIndex (List.mem_cons_of_mem index tailMember))
          (fun first firstMember second secondMember different =>
            disjoint first (List.mem_cons_of_mem index firstMember)
              second (List.mem_cons_of_mem index secondMember) different)]
      rfl

private theorem measure_partition {Index : Type v}
    (measure : Measure source) (region : Set alpha)
    (regionMeasurable : source.Measurable region)
    (indices : List Index) (nodup : indices.Nodup)
    (pieces : Index → Set alpha)
    (measurable : ∀ index, index ∈ indices →
      source.Measurable (pieces index))
    (disjoint : ∀ first, first ∈ indices →
      ∀ second, second ∈ indices → first ≠ second →
        Set.Disjoint (pieces first) (pieces second))
    (cover : ∀ input, ∃ index, index ∈ indices ∧ pieces index input) :
    measure region = finiteSum (indices.map fun index =>
      measure (Set.inter region (pieces index))) := by
  let localized := fun index => Set.inter region (pieces index)
  have unionEqual : pieceUnion localized indices = region := by
    apply Set.ext
    intro input
    constructor
    · intro member
      rcases (mem_pieceUnion_iff localized indices input).mp member with
        ⟨_, _, regionMember, _⟩
      exact regionMember
    · intro regionMember
      rcases cover input with ⟨index, indexMember, pieceMember⟩
      exact (mem_pieceUnion_iff localized indices input).mpr
        ⟨index, indexMember, regionMember, pieceMember⟩
  calc
    measure region = measure (pieceUnion localized indices) := by
      rw [unionEqual]
    _ = finiteSum (indices.map fun index => measure (localized index)) :=
      measure_pieceUnion measure localized indices nodup
        (fun index member => source.inter regionMeasurable
          (measurable index member))
        (fun first firstMember second secondMember different input
            firstPresent secondPresent =>
          disjoint first firstMember second secondMember different
            firstPresent.2 secondPresent.2)
    _ = finiteSum (indices.map fun index =>
        measure (Set.inter region (pieces index))) := rfl

private theorem finiteSum_map_eq_zero {Index : Type v}
    (indices : List Index) (values : Index → ENNReal)
    (zero : ∀ index, index ∈ indices →
      values index = ENNReal.zero) :
    finiteSum (indices.map values) = ENNReal.zero := by
  induction indices with
  | nil => rfl
  | cons index indices induction =>
      simp only [List.map, finiteSum, zero index List.mem_cons_self,
        induction (fun tailIndex tailMember =>
          zero tailIndex (List.mem_cons_of_mem index tailMember)),
        ENNReal.zeroAdd]

private theorem finiteSum_eq_one {Index : Type v}
    (indices : List Index) (target : Index) (nodup : indices.Nodup)
    (targetMember : target ∈ indices) (values : Index → ENNReal)
    (zeroAway : ∀ index, index ∈ indices → index ≠ target →
      values index = ENNReal.zero) :
    finiteSum (indices.map values) = values target := by
  induction indices with
  | nil => exact False.elim (List.not_mem_nil targetMember)
  | cons index indices induction =>
      have indexNotTail := (List.nodup_cons.mp nodup).1
      have tailNodup := (List.nodup_cons.mp nodup).2
      rcases List.mem_cons.mp targetMember with equal | inTail
      · subst index
        have tailZero := finiteSum_map_eq_zero indices values
          (fun tailIndex tailMember => zeroAway tailIndex
            (List.mem_cons_of_mem target tailMember)
            (fun tailEqual => indexNotTail (tailEqual ▸ tailMember)))
        simp only [List.map, finiteSum, tailZero, ENNReal.addZero]
      · have different : index ≠ target := by
          intro equal
          exact indexNotTail (equal ▸ inTail)
        simp only [List.map, finiteSum,
          zeroAway index List.mem_cons_self different, ENNReal.zeroAdd]
        exact induction tailNodup inTail
          (fun tailIndex tailMember tailDifferent =>
            zeroAway tailIndex (List.mem_cons_of_mem index tailMember)
              tailDifferent)

private theorem weighted_fibers_on_piece (function : SimpleFunction source)
    (measure : Measure source) (piece : Set alpha) (coefficient : ENNReal)
    (constant : ∀ input, piece input → function input = coefficient) :
    finiteSum (function.values.map fun value =>
      ENNReal.mul value
        (measure (Set.inter (function.fiber value) piece))) =
      ENNReal.mul coefficient (measure piece) := by
  classical
  by_cases nonempty : Set.Nonempty piece
  · rcases nonempty with ⟨witness, witnessMember⟩
    have coefficientMember : coefficient ∈ function.values :=
      (function.mem_values_iff_attained coefficient).mpr
        ⟨witness, constant witness witnessMember⟩
    rw [finiteSum_eq_one function.values coefficient
      function.values_nodup coefficientMember]
    · congr 1
      apply congrArg measure
      apply Set.ext
      intro input
      exact ⟨fun member => member.2,
        fun member => ⟨constant input member, member⟩⟩
    · intro value _ different
      have empty : Set.inter (function.fiber value) piece = Set.empty := by
        apply Set.ext
        intro input
        constructor
        · intro member
          have valueEqual :=
            (function.mem_fiber_iff value input).mp member.1
          exact False.elim (different (valueEqual.symm.trans
            (constant input member.2)))
        · exact False.elim
      rw [empty, measure.empty_apply, ENNReal.mulZero]
  · have pieceEmpty : piece = Set.empty := by
      apply Set.ext
      intro input
      exact ⟨fun member => False.elim (nonempty ⟨input, member⟩),
        False.elim⟩
    have termsZero : finiteSum (function.values.map fun value =>
        ENNReal.mul value
          (measure (Set.inter (function.fiber value) piece))) =
        ENNReal.zero := by
      apply finiteSum_map_eq_zero
      intro value _
      rw [pieceEmpty, Set.inter_empty_right, measure.empty_apply,
        ENNReal.mulZero]
    rw [termsZero, pieceEmpty, measure.empty_apply, ENNReal.mulZero]

/-- Evaluate an integral on any finite measurable partition on which the
simple function has the stated constant values. -/
public theorem integral_eq_partition {Index : Type v}
    (function : SimpleFunction source) (measure : Measure source)
    (indices : List Index) (nodup : indices.Nodup)
    (pieces : Index → Set alpha) (coefficients : Index → ENNReal)
    (measurable : ∀ index, index ∈ indices →
      source.Measurable (pieces index))
    (disjoint : ∀ first, first ∈ indices →
      ∀ second, second ∈ indices → first ≠ second →
        Set.Disjoint (pieces first) (pieces second))
    (cover : ∀ input, ∃ index, index ∈ indices ∧ pieces index input)
    (constant : ∀ index, index ∈ indices →
      ∀ input, pieces index input →
        function input = coefficients index) :
    integral function measure = finiteSum (indices.map fun index =>
      ENNReal.mul (coefficients index) (measure (pieces index))) := by
  let mass := fun value index =>
    measure (Set.inter (function.fiber value) (pieces index))
  calc
    integral function measure =
        finiteSum (function.values.map fun value =>
          finiteSum (indices.map fun index =>
            ENNReal.mul value (mass value index))) := by
      unfold integral
      apply congrArg finiteSum
      apply List.map_congr_left
      intro value _
      rw [measure_partition measure (function.fiber value)
        (function.fiber_measurable value) indices nodup pieces measurable
        disjoint cover]
      exact (finiteSum_map_mul_left indices value (mass value)).symm
    _ = finiteSum (indices.map fun index =>
        finiteSum (function.values.map fun value =>
          ENNReal.mul value (mass value index))) :=
      finiteSum_comm function.values indices fun value index =>
        ENNReal.mul value (mass value index)
    _ = finiteSum (indices.map fun index =>
        ENNReal.mul (coefficients index) (measure (pieces index))) := by
      apply congrArg finiteSum
      apply List.map_congr_left
      intro index member
      exact weighted_fibers_on_piece function measure (pieces index)
        (coefficients index) (constant index member)

end SimpleFunction

end Foundations.Measure
