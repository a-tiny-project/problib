module

public import Problib.Measure.Integral.Simple.Algebra

set_option autoImplicit false

/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl

Adapted from Mathlib/MeasureTheory/Function/SimpleFunc.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny decomposes over the exact chosen list of attained values.
-/

namespace Problib.Measure

open Problib.Real

universe u

namespace SimpleFunction

variable {alpha : Type u} {source : Space alpha}

noncomputable section

@[expose] public def levelSet (function : SimpleFunction source)
    (value : ENNReal) : Set alpha :=
  fiber function value

public theorem mem_levelSet_iff (function : SimpleFunction source)
    (value : ENNReal) (input : alpha) :
    levelSet function value input ↔ function input = value :=
  Iff.rfl

public theorem levelSet_measurable (function : SimpleFunction source)
    (value : ENNReal) : source.Measurable (levelSet function value) :=
  function.fiber_measurable value

public theorem levelSet_disjoint (function : SimpleFunction source)
    {left right : ENNReal} (different : left ≠ right) :
    Set.Disjoint (levelSet function left) (levelSet function right) := by
  intro input leftMember rightMember
  have leftEqual :=
    (mem_levelSet_iff function left input).mp leftMember
  have rightEqual :=
    (mem_levelSet_iff function right input).mp rightMember
  exact different (leftEqual.symm.trans rightEqual)

public theorem mem_some_levelSet (function : SimpleFunction source)
    (input : alpha) :
    ∃ value, value ∈ function.values ∧ levelSet function value input :=
  ⟨function input, function.value_mem_values input, rfl⟩

@[expose] public noncomputable def sumList
    (functions : List (SimpleFunction source)) : SimpleFunction source :=
  match functions with
  | [] => zero source
  | function :: rest => add function (sumList rest)

@[simp] public theorem sumList_nil :
    sumList ([] : List (SimpleFunction source)) = zero source :=
  rfl

public theorem sumList_cons (function : SimpleFunction source)
    (rest : List (SimpleFunction source)) :
    sumList (function :: rest) = add function (sumList rest) :=
  rfl

public theorem sumList_apply_nil (input : alpha) :
    sumList ([] : List (SimpleFunction source)) input = ENNReal.zero :=
  zero_apply source input

public theorem sumList_apply_cons (function : SimpleFunction source)
    (rest : List (SimpleFunction source)) (input : alpha) :
    sumList (function :: rest) input =
      ENNReal.add (function input) (sumList rest input) :=
  add_apply function (sumList rest) input

private def levelIndicators (function : SimpleFunction source)
    (values : List ENNReal) : List (SimpleFunction source) :=
  values.map fun value =>
    indicator (levelSet function value)
      (function.levelSet_measurable value) value

private theorem levelIndicators_zero_of_not_mem
    (function : SimpleFunction source) (values : List ENNReal)
    (input : alpha) (notMember : function input ∉ values) :
    sumList (levelIndicators function values) input = ENNReal.zero := by
  induction values with
  | nil => exact sumList_apply_nil input
  | cons value values induction =>
      have valueDifferent : function input ≠ value := by
        intro equal
        exact notMember (List.mem_cons.mpr (Or.inl equal))
      have notTail : function input ∉ values := by
        intro member
        exact notMember (List.mem_cons.mpr (Or.inr member))
      have outside : ¬levelSet function value input :=
        fun member => valueDifferent
          ((mem_levelSet_iff function value input).mp member)
      have tailZero := induction notTail
      unfold levelIndicators at tailZero ⊢
      rw [List.map, sumList_apply_cons,
        indicator_apply_of_not_mem _ _ _ _ outside,
        tailZero, ENNReal.zero_add]

private theorem levelIndicators_apply_of_mem
    (function : SimpleFunction source) (values : List ENNReal)
    (nodup : values.Nodup) (input : alpha)
    (member : function input ∈ values) :
    sumList (levelIndicators function values) input = function input := by
  induction values with
  | nil => simp at member
  | cons value values induction =>
      have headNotTail := (List.nodup_cons.mp nodup).1
      have tailNodup := (List.nodup_cons.mp nodup).2
      rcases List.mem_cons.mp member with head | tail
      · have inside : levelSet function value input := head
        have current := indicator_apply_of_mem
          (levelSet function value) (function.levelSet_measurable value)
          value input inside
        have absent : function input ∉ values := by
          intro inTail
          exact headNotTail (head ▸ inTail)
        have tailZero :=
          levelIndicators_zero_of_not_mem function values input absent
        unfold levelIndicators at tailZero ⊢
        rw [List.map, sumList_apply_cons, current, tailZero,
          ENNReal.add_zero, head]
      · have outside : ¬levelSet function value input := by
          intro inLevel
          have equal := (mem_levelSet_iff function value input).mp inLevel
          exact headNotTail (equal ▸ tail)
        have tailValue := induction tailNodup tail
        unfold levelIndicators at tailValue ⊢
        rw [List.map, sumList_apply_cons,
          indicator_apply_of_not_mem _ _ _ _ outside,
          ENNReal.zero_add]
        exact tailValue

/-- The sum of the value-weighted measurable level indicators. -/
public noncomputable def decomposition
    (function : SimpleFunction source) : SimpleFunction source :=
  sumList (levelIndicators function function.values)

public theorem decomposition_apply (function : SimpleFunction source)
    (input : alpha) : decomposition function input = function input := by
  unfold decomposition
  exact levelIndicators_apply_of_mem function function.values
    function.values_nodup input (function.value_mem_values input)

public theorem decomposition_eq (function : SimpleFunction source) :
    decomposition function = function :=
  SimpleFunction.ext (function.decomposition_apply)

/-- Induction over zero, measurable constant indicators, and addition. -/
public protected theorem induction {motive : SimpleFunction source → Prop}
    (zeroCase : motive (zero source))
    (indicatorCase : ∀ (region : Set alpha)
      (regionMeasurable : source.Measurable region) (value : ENNReal),
      motive (indicator region regionMeasurable value))
    (addCase : ∀ left right, motive left → motive right →
      motive (add left right))
    (function : SimpleFunction source) : motive function := by
  have sumMotive : ∀ functions : List (SimpleFunction source),
      (∀ member, member ∈ functions → motive member) →
      motive (sumList functions) := by
    intro functions
    induction functions with
    | nil => exact fun _ => zeroCase
    | cons head tail induction =>
        intro each
        rw [sumList_cons]
        exact addCase head (sumList tail)
          (each head List.mem_cons_self)
          (induction fun member memberInTail =>
            each member (List.mem_cons_of_mem head memberInTail))
  have decomposed : motive (decomposition function) := by
    unfold decomposition
    apply sumMotive
    intro member memberInIndicators
    rcases List.mem_map.mp memberInIndicators with ⟨value, _, rfl⟩
    exact indicatorCase (levelSet function value)
      (function.levelSet_measurable value) value
  rw [function.decomposition_eq] at decomposed
  exact decomposed

end

end SimpleFunction

end Problib.Measure
