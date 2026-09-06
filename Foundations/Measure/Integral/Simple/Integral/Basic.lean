module

public import Foundations.Measure.Additive.Core
public import Foundations.Measure.Integral.Simple.Decomposition

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

@[expose] public def finiteSum : List ENNReal → ENNReal
  | [] => ENNReal.zero
  | value :: values => ENNReal.add value (finiteSum values)

private theorem finiteSum_append (left right : List ENNReal) :
    finiteSum (left ++ right) =
      ENNReal.add (finiteSum left) (finiteSum right) := by
  induction left with
  | nil => simp [finiteSum, ENNReal.zeroAdd]
  | cons value values induction =>
      simp only [List.cons_append, finiteSum]
      rw [induction, ENNReal.addAssoc]

private theorem finiteSum_congr {left right : List ENNReal}
    (equal : ∀ (index : Nat), left[index]? = right[index]?) :
    finiteSum left = finiteSum right := by
  have listsEqual : left = right := by
    apply List.ext_getElem?
    exact equal
  rw [listsEqual]

private theorem finiteSum_perm {left right : List ENNReal}
    (permutation : left.Perm right) :
    finiteSum left = finiteSum right := by
  induction permutation with
  | nil => rfl
  | cons value permutation induction =>
      simp only [finiteSum]
      rw [induction]
  | swap left right values =>
      simp only [finiteSum]
      calc
        ENNReal.add right (ENNReal.add left (finiteSum values)) =
            ENNReal.add (ENNReal.add right left) (finiteSum values) :=
          (ENNReal.addAssoc _ _ _).symm
        _ = ENNReal.add (ENNReal.add left right) (finiteSum values) := by
          rw [ENNReal.addComm right left]
        _ = ENNReal.add left (ENNReal.add right (finiteSum values)) :=
          ENNReal.addAssoc _ _ _
  | trans first second firstInduction secondInduction =>
      exact firstInduction.trans secondInduction

private theorem perm_of_nodup_mem_iff {Value : Type u}
    {left right : List Value}
    (leftNodup : left.Nodup) (rightNodup : right.Nodup)
    (same : ∀ value, value ∈ left ↔ value ∈ right) :
    left.Perm right := by
  induction left generalizing right with
  | nil =>
      have rightEmpty : right = [] := by
        cases right with
        | nil => rfl
        | cons value values =>
            have impossible : value ∈ ([] : List Value) :=
              (same value).mpr (List.mem_cons_self)
            exact False.elim (List.not_mem_nil impossible)
      rw [rightEmpty]
  | cons value values induction =>
      have valueInRight : value ∈ right :=
        (same value).mp List.mem_cons_self
      rcases List.append_of_mem valueInRight with
        ⟨before, after, rightEqual⟩
      subst right
      have movedNodup :
          (value :: (before ++ after)).Nodup :=
        rightNodup.perm List.perm_middle
      have valueNotTail : value ∉ before ++ after :=
        (List.nodup_cons.mp movedNodup).1
      have tailNodup : (before ++ after).Nodup :=
        (List.nodup_cons.mp movedNodup).2
      have valueNotValues : value ∉ values :=
        (List.nodup_cons.mp leftNodup).1
      have sameTail : ∀ candidate,
          candidate ∈ values ↔ candidate ∈ before ++ after := by
        intro candidate
        constructor
        · intro member
          have inRight : candidate ∈ before ++ value :: after :=
            (same candidate).mp (List.mem_cons_of_mem value member)
          rcases List.mem_append.mp inRight with inBefore | inRest
          · exact List.mem_append.mpr (Or.inl inBefore)
          · rcases List.mem_cons.mp inRest with equal | inAfter
            · subst candidate
              exact False.elim (valueNotValues member)
            · exact List.mem_append.mpr (Or.inr inAfter)
        · intro member
          have candidateDifferent : candidate ≠ value := by
            intro equal
            subst candidate
            exact valueNotTail member
          have inRight : candidate ∈ before ++ value :: after := by
            rcases List.mem_append.mp member with inBefore | inAfter
            · exact List.mem_append.mpr (Or.inl inBefore)
            · exact List.mem_append.mpr
                (Or.inr (List.mem_cons_of_mem value inAfter))
          have inLeft : candidate ∈ value :: values :=
            (same candidate).mpr inRight
          rcases (List.mem_cons.mp inLeft) with equal | inValues
          · exact False.elim (candidateDifferent equal)
          · exact inValues
      exact (List.Perm.cons value
        (induction (List.nodup_cons.mp leftNodup).2
          tailNodup sameTail)).trans List.perm_middle.symm

public theorem finiteSum_map_add {Index : Type u}
    (indices : List Index) (left right : Index → ENNReal) :
    finiteSum (indices.map (fun index =>
      ENNReal.add (left index) (right index))) =
      ENNReal.add
        (finiteSum (indices.map left))
        (finiteSum (indices.map right)) := by
  induction indices with
  | nil => simp [finiteSum, ENNReal.addZero]
  | cons index indices induction =>
      simp only [List.map, finiteSum]
      rw [induction]
      calc
        ENNReal.add (ENNReal.add (left index) (right index))
            (ENNReal.add (finiteSum (List.map left indices))
              (finiteSum (List.map right indices))) =
          ENNReal.add (left index)
            (ENNReal.add (right index)
              (ENNReal.add (finiteSum (List.map left indices))
                (finiteSum (List.map right indices)))) :=
            ENNReal.addAssoc _ _ _
        _ = ENNReal.add (left index)
            (ENNReal.add (finiteSum (List.map left indices))
              (ENNReal.add (right index)
                (finiteSum (List.map right indices)))) := by
          rw [← ENNReal.addAssoc (right index)
              (finiteSum (List.map left indices))
              (finiteSum (List.map right indices)),
            ENNReal.addComm (right index)
              (finiteSum (List.map left indices)),
            ENNReal.addAssoc]
        _ = ENNReal.add
            (ENNReal.add (left index)
              (finiteSum (List.map left indices)))
            (ENNReal.add (right index)
              (finiteSum (List.map right indices))) :=
          (ENNReal.addAssoc _ _ _).symm

public theorem finiteSum_map_mul_left {Index : Type u}
    (indices : List Index) (factor : ENNReal)
    (values : Index → ENNReal) :
    finiteSum (indices.map (fun index =>
      ENNReal.mul factor (values index))) =
      ENNReal.mul factor (finiteSum (indices.map values)) := by
  induction indices with
  | nil => simp [finiteSum, ENNReal.mulZero]
  | cons index indices induction =>
      simp only [List.map, finiteSum]
      rw [induction, ENNReal.mulAdd]

public theorem finiteSum_map_mono {Index : Type u}
    (indices : List Index) (left right : Index → ENNReal)
    (included : ∀ index, ENNReal.le (left index) (right index)) :
    ENNReal.le (finiteSum (indices.map left))
      (finiteSum (indices.map right)) := by
  induction indices with
  | nil => exact ENNReal.leRefl ENNReal.zero
  | cons index indices induction =>
      simp only [List.map, finiteSum]
      exact ENNReal.addLeAdd (included index) induction

private theorem finiteSum_map_zero {Index : Type u}
    (indices : List Index) :
    finiteSum (indices.map fun _ => ENNReal.zero) = ENNReal.zero := by
  induction indices with
  | nil => rfl
  | cons index indices induction =>
      simp only [List.map, finiteSum, induction, ENNReal.zeroAdd]

public theorem finiteSum_comm {Left : Type u} {Right : Type v}
    (left : List Left) (right : List Right)
    (values : Left → Right → ENNReal) :
    finiteSum (left.map fun first =>
      finiteSum (right.map (values first))) =
      finiteSum (right.map fun second =>
        finiteSum (left.map fun first => values first second)) := by
  induction left with
  | nil =>
      simp only [List.map, finiteSum]
      exact (finiteSum_map_zero right).symm
  | cons first left induction =>
      simp only [List.map, finiteSum]
      rw [induction]
      exact (finiteSum_map_add right (values first)
        (fun second => finiteSum (left.map fun remaining =>
          values remaining second))).symm

public theorem finiteSum_map_tsum {Index : Type u}
    (indices : List Index) (values : Nat → Index → ENNReal) :
    finiteSum (indices.map (fun index =>
      ENNReal.tsum (fun measureIndex => values measureIndex index))) =
      ENNReal.tsum (fun measureIndex =>
        finiteSum (indices.map (values measureIndex))) := by
  induction indices with
  | nil =>
      simp only [List.map, finiteSum]
      exact ENNReal.tsumZero.symm
  | cons index indices induction =>
      simp only [List.map, finiteSum]
      rw [induction]
      exact (ENNReal.tsumAdd
        (fun measureIndex => values measureIndex index)
        (fun measureIndex =>
          finiteSum (List.map (values measureIndex) indices))).symm

public theorem finiteSum_map_iSup {Index : Type u}
    (indices : List Index) (values : Nat → Index → ENNReal)
    (monotone : ∀ stage index,
      ENNReal.le (values stage index) (values (stage + 1) index)) :
    finiteSum (indices.map fun index =>
      ENNReal.iSup (fun stage => values stage index)) =
      ENNReal.iSup (fun stage =>
        finiteSum (indices.map (values stage))) := by
  induction indices with
  | nil =>
      simpa only [List.map, finiteSum] using
        (ENNReal.iSupConst ENNReal.zero).symm
  | cons index indices induction =>
      simp only [List.map, finiteSum]
      rw [induction]
      exact (ENNReal.iSupDiagonalAdd
        (fun stage => values stage index)
        (fun stage => finiteSum (indices.map (values stage)))
        (fun stage => monotone stage index)
        (fun stage => finiteSum_map_mono indices
          (values stage) (values (stage + 1))
          (monotone stage))).symm

public theorem finiteSum_flatMap {Index : Type u} {Entry : Type v}
    (indices : List Index) (entries : Index → List Entry)
    (values : Index → Entry → ENNReal) :
    finiteSum (indices.flatMap fun index =>
      (entries index).map (values index)) =
      finiteSum (indices.map fun index =>
        finiteSum ((entries index).map (values index))) := by
  induction indices with
  | nil => rfl
  | cons index indices induction =>
      simp only [List.flatMap_cons, List.map, finiteSum]
      rw [finiteSum_append, induction]

/-- The integral of a simple function is the finite weighted sum of the
measures of its level sets. -/
@[expose] public noncomputable def integral
    (function : SimpleFunction source) (measure : Measure source) : ENNReal :=
  finiteSum (function.values.map fun value =>
    ENNReal.mul value (measure (function.fiber value)))

public theorem integral_eq_finiteSum
    (function : SimpleFunction source) (measure : Measure source) :
    integral function measure =
      finiteSum (function.values.map fun value =>
        ENNReal.mul value (measure (function.fiber value))) :=
  rfl

public theorem integral_congr {left right : SimpleFunction source}
    (equal : ∀ input, left input = right input)
    (measure : Measure source) :
    integral left measure = integral right measure := by
  have functionsEqual : left = right := SimpleFunction.ext equal
  rw [functionsEqual]

end SimpleFunction

end Foundations.Measure
