module

public import Problib.Measure.Kernel.Iteration.Recurrence

set_option autoImplicit false

namespace Problib.Measure.Kernel

open Problib.Real

universe u
variable {α : Type u} {space : Space α}

/-- Positive, disjoint measurable cells rotated surely by a kernel. -/
public structure MeasureCycle (kernel : Kernel space space)
    (reference : Measure space) (period : Nat) (cell : Nat → Set α) : Prop where
  measurable : ∀ index, index < period → space.Measurable (cell index)
  disjoint : ∀ first second, first < period → second < period →
    first ≠ second → ∀ value, cell first value → ¬ cell second value
  positive : ∀ index, index < period →
    ENNReal.lt ENNReal.zero (reference (cell index))
  advance : ∀ index, index < period → ∀ input, cell index input →
    kernel input (cell ((index + 1) % period)) = ENNReal.one

@[expose] public def MeasureAperiodic (kernel : Kernel space space)
    (reference : Measure space) : Prop :=
  ∀ period cell, MeasureCycle kernel reference period cell → period ≤ 1

private theorem lintegral_one_of_full_event (measure : Measure space)
    (probability : Measure.IsProbability measure)
    (event : Set α) (eventMeasurable : space.Measurable event)
    (full : measure event = ENNReal.one) (function : α → ENNReal)
    (bounded : ∀ value, ENNReal.le (function value) ENNReal.one)
    (onEvent : ∀ value, event value → function value = ENNReal.one) :
    lintegral measure function = ENNReal.one := by
  apply ENNReal.le_antisymm
  · have upper := lintegral_mono measure bounded
    rw [lintegral_const, probability.univ_eq_one,
      ENNReal.one_mul] at upper
    exact upper
  · have lower : ∀ value,
        ENNReal.le (ennrealIndicator event (fun _ => ENNReal.one) value)
          (function value) := by
      intro value
      by_cases member : event value
      · rw [ennrealIndicator, ennrealPiecewise, if_pos member,
          onEvent value member]
        exact ENNReal.le_refl _
      · rw [ennrealIndicator, ennrealPiecewise, if_neg member]
        exact ENNReal.zero_le _
    have integralLower := lintegral_mono measure lower
    rw [← apply_eq_lintegral_indicator measure eventMeasurable,
      full] at integralLower
    exact integralLower

public theorem MeasureCycle.iterate_advance
    {kernel : Kernel space space} {reference : Measure space}
    {period : Nat} {cell : Nat → Set α}
    (markov : ∀ input, Measure.IsProbability (kernel input))
    (cycle : MeasureCycle kernel reference period cell)
    (index : Nat) (inRange : index < period)
    (input : α) (member : cell index input) (count : Nat) :
    iterate kernel count input (cell ((index + count) % period)) =
      ENNReal.one := by
  induction count with
  | zero =>
      have indexMod : (index + 0) % period = index := by
        rw [Nat.add_zero, Nat.mod_eq_of_lt inRange]
      rw [indexMod, iterate_zero, Kernel.deterministic_apply]
      exact Measure.dirac_apply_of_mem space input
        (cycle.measurable index inRange) member
  | succ count induction =>
      have nextRange : (index + count) % period < period :=
        Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le index) inRange)
      have nextMeasurable := cycle.measurable _ nextRange
      have targetRange : (index + (count + 1)) % period < period :=
        Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le index) inRange)
      have targetMeasurable := cycle.measurable _ targetRange
      have modular : (((index + count) % period) + 1) % period =
          (index + (count + 1)) % period := by
        rw [Nat.mod_add_mod, Nat.add_assoc]
      rw [iterate_succ_right,
        comp_apply_measurable _ _ _ targetMeasurable]
      apply lintegral_one_of_full_event
        (iterate kernel count input)
        (iterate_isProbability kernel markov count input)
        (cell ((index + count) % period)) nextMeasurable
        (induction) _
      · intro value
        exact (markov value).apply_le_one _
      · intro value memberAtNext
        rw [← modular]
        exact cycle.advance _ nextRange value memberAtNext

end Problib.Measure.Kernel
