module

public import Problib.Measure.Integral.Simple.Decomposition
public import Problib.Measure.Extended.Order
public import Problib.Real.Series.Core

set_option autoImplicit false

/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl

Adapted from Mathlib/MeasureTheory/Function/SimpleFunc.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny uses the package's enumerated rational basis and supremum-defined series.
-/

namespace Problib.Measure

open Problib.Real

universe u v

namespace SimpleFunction

variable {alpha : Type u} {source : Space alpha}

noncomputable section

private def approximationCandidates : Nat → List ENNReal
  | 0 => [ENNReal.zero]
  | index + 1 =>
      ENNReal.rationalBasis index :: approximationCandidates index

private theorem approximation_mem_candidates (value : ENNReal) :
    ∀ index, ENNReal.approximation value index ∈
      approximationCandidates index
  | 0 => List.mem_cons_self
  | index + 1 => by
      classical
      rw [ENNReal.approximation]
      split
      · split
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _
            (approximation_mem_candidates value index)
      · exact List.mem_cons_of_mem _
          (approximation_mem_candidates value index)

/-- The canonical finite rational approximation of a measurable function. -/
public noncomputable def approximation (function : alpha → ENNReal)
    (functionMeasurable : ENNRealMeasurable source function)
    (index : Nat) : SimpleFunction source :=
  ofCandidates
    (fun input => ENNReal.approximation (function input) index)
    (approximationCandidates index)
    (fun input => approximation_mem_candidates (function input) index)
    (fun value =>
      (ENNRealMeasurable.approximation functionMeasurable index).singleton
        value)

@[simp] public theorem approximation_apply (function : alpha → ENNReal)
    (functionMeasurable : ENNRealMeasurable source function)
    (index : Nat) (input : alpha) :
    approximation function functionMeasurable index input =
      ENNReal.approximation (function input) index := by
  unfold approximation
  rw [ofCandidates_apply]

public theorem approximation_measurable (function : alpha → ENNReal)
    (functionMeasurable : ENNRealMeasurable source function)
    (index : Nat) :
    ENNRealMeasurable source (approximation function functionMeasurable index) :=
  (approximation function functionMeasurable index).measurable

public theorem approximation_finite (function : alpha → ENNReal)
    (functionMeasurable : ENNRealMeasurable source function)
    (index : Nat) (input : alpha) :
    ENNReal.Finite (approximation function functionMeasurable index input) := by
  rw [approximation_apply]
  exact ENNReal.approximation_finite (function input) index

public theorem approximation_le (function : alpha → ENNReal)
    (functionMeasurable : ENNRealMeasurable source function)
    (index : Nat) :
    PointwiseLe (approximation function functionMeasurable index) function := by
  intro input
  rw [approximation_apply]
  exact ENNReal.approximation_le (function input) index

public theorem approximation_mono (function : alpha → ENNReal)
    (functionMeasurable : ENNRealMeasurable source function)
    (index : Nat) :
    PointwiseLe (approximation function functionMeasurable index)
      (approximation function functionMeasurable (index + 1)) := by
  intro input
  rw [approximation_apply, approximation_apply]
  exact ENNReal.approximation_step (function input) index

public theorem approximation_mono_index (function : alpha → ENNReal)
    (functionMeasurable : ENNRealMeasurable source function)
    {first second : Nat} (included : first ≤ second) :
    PointwiseLe (approximation function functionMeasurable first)
      (approximation function functionMeasurable second) := by
  intro input
  induction second with
  | zero =>
      have equal : first = 0 := by omega
      rw [equal]
      exact ENNReal.le_refl _
  | succ second induction =>
      by_cases equal : first = second + 1
      · rw [equal]
        exact ENNReal.le_refl _
      · have before : first ≤ second := by omega
        exact ENNReal.le_trans (induction before)
          (approximation_mono function functionMeasurable second input)

public theorem approximation_value_mono {left right : ENNReal}
    (included : ENNReal.le left right) : ∀ index,
    ENNReal.le (ENNReal.approximation left index)
      (ENNReal.approximation right index)
  | 0 => ENNReal.le_refl ENNReal.zero
  | index + 1 => by
      classical
      have previous := approximation_value_mono included index
      by_cases leftIncluded :
          ENNReal.le (ENNReal.rationalBasis index) left
      · have rightIncluded := ENNReal.le_trans leftIncluded included
        by_cases leftDominates : ENNReal.le
            (ENNReal.approximation left index)
            (ENNReal.rationalBasis index)
        · by_cases rightDominates : ENNReal.le
              (ENNReal.approximation right index)
              (ENNReal.rationalBasis index)
          · simp only [ENNReal.approximation, dif_pos leftIncluded,
              dif_pos rightIncluded, dif_pos leftDominates,
              dif_pos rightDominates]
            exact ENNReal.le_refl _
          · have basisRight : ENNReal.le (ENNReal.rationalBasis index)
                (ENNReal.approximation right index) :=
              Or.resolve_left (ENNReal.le_total
                (ENNReal.approximation right index)
                (ENNReal.rationalBasis index)) rightDominates
            simpa [ENNReal.approximation, leftIncluded, rightIncluded,
              leftDominates, rightDominates] using basisRight
        · by_cases rightDominates : ENNReal.le
              (ENNReal.approximation right index)
              (ENNReal.rationalBasis index)
          · exact False.elim (leftDominates
              (ENNReal.le_trans previous rightDominates))
          · simpa [ENNReal.approximation, leftIncluded, rightIncluded,
              leftDominates, rightDominates] using previous
      · by_cases rightIncluded :
            ENNReal.le (ENNReal.rationalBasis index) right
        · by_cases rightDominates : ENNReal.le
              (ENNReal.approximation right index)
              (ENNReal.rationalBasis index)
          · have leftBasis : ENNReal.le
                (ENNReal.approximation left index)
                (ENNReal.rationalBasis index) :=
              ENNReal.le_trans previous rightDominates
            simpa [ENNReal.approximation, leftIncluded, rightIncluded,
              rightDominates] using leftBasis
          · simpa [ENNReal.approximation, leftIncluded, rightIncluded,
              rightDominates] using previous
        · simpa [ENNReal.approximation, leftIncluded, rightIncluded]
            using previous

public theorem approximation_mono_function
    {left right : alpha → ENNReal}
    (leftMeasurable : ENNRealMeasurable source left)
    (rightMeasurable : ENNRealMeasurable source right)
    (included : ∀ input, ENNReal.le (left input) (right input))
    (index : Nat) :
    PointwiseLe (approximation left leftMeasurable index)
      (approximation right rightMeasurable index) := by
  intro input
  rw [approximation_apply, approximation_apply]
  exact approximation_value_mono (included input) index

public theorem approximation_comp {beta : Type v} {target : Space beta}
    (function : beta → ENNReal)
    (functionMeasurable : ENNRealMeasurable target function)
    (before : alpha → beta)
    (beforeMeasurable : MeasurableMap source target before)
    (index : Nat) :
    comp (approximation function functionMeasurable index)
        before beforeMeasurable =
      approximation (fun input => function (before input))
        (ENNRealMeasurable.comp functionMeasurable beforeMeasurable) index := by
  apply SimpleFunction.ext
  intro input
  rw [comp_apply, approximation_apply, approximation_apply]

public theorem iSup_approximation (function : alpha → ENNReal)
    (functionMeasurable : ENNRealMeasurable source function)
    (input : alpha) :
    ENNReal.iSup (fun index =>
      approximation function functionMeasurable index input) =
      function input := by
  calc
    ENNReal.iSup (fun index =>
        approximation function functionMeasurable index input) =
        ENNReal.iSup (ENNReal.approximation (function input)) := by
      apply congrArg ENNReal.iSup
      funext index
      exact approximation_apply function functionMeasurable index input
    _ = function input := ENNReal.iSup_approximation (function input)

private def approximationBound : Nat → ENNReal
  | 0 => ENNReal.zero
  | index + 1 => ENNReal.add (approximationBound index)
      (ENNReal.rationalBasis index)

private theorem approximationBound_finite : ∀ index,
    ENNReal.Finite (approximationBound index)
  | 0 => True.intro
  | index + 1 => by
      rcases ENNReal.exists_finite_of_finite
          (approximationBound_finite index) with ⟨left, leftEqual⟩
      rcases ENNReal.exists_finite_of_finite
          (ENNReal.rationalBasis_finite index) with ⟨right, rightEqual⟩
      rw [approximationBound, leftEqual, rightEqual]
      exact True.intro

private theorem approximation_le_bound (value : ENNReal) : ∀ index,
    ENNReal.le (ENNReal.approximation value index)
      (approximationBound index)
  | 0 => ENNReal.le_refl ENNReal.zero
  | index + 1 => by
      classical
      have previousIncluded := approximation_le_bound value index
      have previousBound : ENNReal.le (approximationBound index)
          (approximationBound (index + 1)) := by
        have shifted := ENNReal.add_le_add_right
          (ENNReal.zero_le (ENNReal.rationalBasis index))
          (approximationBound index)
        rw [ENNReal.zero_add, ENNReal.add_comm] at shifted
        simpa only [approximationBound] using shifted
      have basisBound : ENNReal.le (ENNReal.rationalBasis index)
          (approximationBound (index + 1)) := by
        have shifted := ENNReal.add_le_add_left
          (ENNReal.zero_le (approximationBound index))
          (ENNReal.rationalBasis index)
        rw [ENNReal.add_zero] at shifted
        rw [ENNReal.add_comm] at shifted
        simpa only [approximationBound] using shifted
      rw [ENNReal.approximation]
      split
      · split
        · exact basisBound
        · exact ENNReal.le_trans previousIncluded previousBound
      · exact ENNReal.le_trans previousIncluded previousBound

/-- The nonnegative increment between consecutive canonical approximations. -/
public noncomputable def increment (function : alpha → ENNReal)
    (functionMeasurable : ENNRealMeasurable source function)
    (index : Nat) : SimpleFunction source :=
  sub (approximation function functionMeasurable (index + 1))
    (approximation function functionMeasurable index)

@[simp] public theorem increment_apply (function : alpha → ENNReal)
    (functionMeasurable : ENNRealMeasurable source function)
    (index : Nat) (input : alpha) :
    increment function functionMeasurable index input =
      ENNReal.sub
        (ENNReal.approximation (function input) (index + 1))
        (ENNReal.approximation (function input) index) := by
  unfold increment
  rw [sub_apply, approximation_apply, approximation_apply]

public theorem increment_measurable (function : alpha → ENNReal)
    (functionMeasurable : ENNRealMeasurable source function)
    (index : Nat) :
    ENNRealMeasurable source (increment function functionMeasurable index) :=
  (increment function functionMeasurable index).measurable

public theorem increment_finite (function : alpha → ENNReal)
    (functionMeasurable : ENNRealMeasurable source function)
    (index : Nat) (input : alpha) :
    ENNReal.Finite (increment function functionMeasurable index input) := by
  rw [increment_apply]
  exact ENNReal.sub_finite_of_finite_left
    (ENNReal.approximation_finite (function input) (index + 1))

public theorem increment_uniformly_bounded (function : alpha → ENNReal)
    (functionMeasurable : ENNRealMeasurable source function)
    (index : Nat) :
    ∃ bound, ENNReal.Finite bound ∧ ∀ input,
      ENNReal.le (increment function functionMeasurable index input) bound := by
  refine ⟨approximationBound (index + 1),
    approximationBound_finite (index + 1), ?_⟩
  intro input
  rw [increment_apply]
  exact ENNReal.le_trans
    (ENNReal.sub_le_self _ _)
    (approximation_le_bound (function input) (index + 1))

public theorem partialSum_increment (function : alpha → ENNReal)
    (functionMeasurable : ENNRealMeasurable source function)
    (count : Nat) (input : alpha) :
    ENNReal.partialSum
      (fun index => increment function functionMeasurable index input) count =
      approximation function functionMeasurable count input := by
  induction count with
  | zero =>
      rw [ENNReal.partialSum, approximation_apply]
      rfl
  | succ count induction =>
      rw [ENNReal.partialSum, induction, increment_apply,
        approximation_apply, approximation_apply,
        ENNReal.add_comm,
        ENNReal.sub_add_cancel
          (ENNReal.approximation_step (function input) count)]

public theorem tsum_increments (function : alpha → ENNReal)
    (functionMeasurable : ENNRealMeasurable source function)
    (input : alpha) :
    ENNReal.tsum
      (fun index => increment function functionMeasurable index input) =
      function input := by
  unfold ENNReal.tsum
  calc
    ENNReal.iSup (ENNReal.partialSum
        (fun index => increment function functionMeasurable index input)) =
        ENNReal.iSup (fun count =>
          approximation function functionMeasurable count input) := by
      apply congrArg ENNReal.iSup
      funext count
      exact partialSum_increment function functionMeasurable count input
    _ = function input := iSup_approximation function functionMeasurable input

end

end SimpleFunction

end Problib.Measure
