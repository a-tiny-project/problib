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
      · rw [ennrealIndicator, ennrealPiecewise, ite_eq_left member,
          onEvent value member]
        exact ENNReal.le_refl _
      · rw [ennrealIndicator, ennrealPiecewise, ite_eq_right member]
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

section Strong

variable {kernel : Kernel space space}

/-- A one-step small set charged by both the reference and its minorant. -/
@[expose] public def StrongAperiodic (kernel : Kernel space space)
    (reference : Measure space) : Prop :=
  ∃ region weight minorant, space.Measurable region ∧
    MinorizationOn kernel region 1 weight minorant ∧
    ENNReal.lt ENNReal.zero (reference region) ∧
    ENNReal.lt ENNReal.zero (minorant.val region)

/-- A sure move into a measurable event from a point of a one-step small set
makes the minorant give the complement no mass. -/
private theorem minorant_null_outside {region : Set α} {weight : NNReal}
    {minorant : Giry.Law space}
    (minor : MinorizationOn kernel region 1 weight minorant)
    {input : α} (member : region input) {event : Set α}
    (eventMeasurable : space.Measurable event)
    (sure : kernel input event = ENNReal.one) :
    minorant.val (Set.complement event) = ENNReal.zero := by
  have lower := minor.lower input member (Set.complement event)
    (space.complement eventMeasurable)
  rw [Measure.smul_apply_measurable _ _ (space.complement eventMeasurable),
    iterate_one, Measure.IsProbability.apply_complement (minor.markov input) eventMeasurable,
    sure, ENNReal.sub_self] at lower
  rcases ENNReal.mul_eq_zero_iff.mp (ENNReal.eq_zero_of_le_zero lower) with
    weightZero | outsideZero
  · exact absurd weightZero (ENNReal.zero_lt_iff_ne_zero.mp
      (show ENNReal.lt ENNReal.zero (ENNReal.finite weight) from
        minor.weightPositive))
  · exact outsideZero

private theorem succ_mod_ne {period index : Nat} (large : 2 ≤ period)
    (inRange : index < period) : (index + 1) % period ≠ index := by
  intro equal
  rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt inRange) with below | full
  · rw [Nat.mod_eq_of_lt below] at equal
    omega
  · have whole : index + 1 = period := full
    rw [whole, Nat.mod_self] at equal
    omega

/-- A strongly aperiodic irreducible chain admits no cycle of period two or
more. -/
public theorem strongAperiodic_measureAperiodic {reference : Measure space}
    (markov : ∀ input, Measure.IsProbability (kernel input))
    (irreducible : MeasureIrreducible kernel reference)
    (strong : StrongAperiodic kernel reference) :
    MeasureAperiodic kernel reference := by
  classical
  intro period cell cycle
  rcases strong with ⟨region, weight, minorant, measurable, minor,
    referenceCharged, charged⟩
  apply Classical.byContradiction
  intro notSmall
  have large : 2 ≤ period := by omega
  have periodPositive : 0 < period := by omega
  -- A state of the first cell reaches the small set inside a cell.
  have wholeOutside : reference (Set.complement Set.univ) = ENNReal.zero := by
    rw [Set.complement_univ, Measure.empty_apply]
  rcases Measure.exists_mem_of_positive_of_conull _ (cycle.positive 0 periodPositive)
      wholeOutside with ⟨start, startMember, _⟩
  rcases irreducible.reaches region measurable referenceCharged start with
    ⟨count, reached⟩
  let landing := (0 + (count + 1)) % period
  have landingRange : landing < period := Nat.mod_lt _ periodPositive
  have landingSure := cycle.iterate_advance markov 0 periodPositive start
    startMember (count + 1)
  have landingOutside : iterate kernel (count + 1) start
      (Set.complement (cell landing)) = ENNReal.zero := by
    rw [Measure.IsProbability.apply_complement (iterate_isProbability kernel markov _ start)
      (cycle.measurable _ landingRange), landingSure, ENNReal.sub_self]
  rcases Measure.exists_mem_of_positive_of_conull _ reached landingOutside with
    ⟨first, firstRegion, firstCell⟩
  -- The minorant lives on the next cell, and then on the one after.
  let next := (landing + 1) % period
  have nextRange : next < period := Nat.mod_lt _ periodPositive
  have nextNull := minorant_null_outside minor firstRegion
    (cycle.measurable next nextRange)
    (cycle.advance landing landingRange first firstCell)
  rcases Measure.exists_mem_of_positive_of_conull _ charged nextNull with
    ⟨second, secondRegion, secondCell⟩
  let after := (next + 1) % period
  have afterRange : after < period := Nat.mod_lt _ periodPositive
  have afterNull := minorant_null_outside minor secondRegion
    (cycle.measurable after afterRange)
    (cycle.advance next nextRange second secondCell)
  have distinct : next ≠ after := fun equal =>
    succ_mod_ne large nextRange equal.symm
  have wholeNull := (Measure.NullSet.union (measure := minorant.val) nextNull
    afterNull).mono (left := region) (fun {value} _ => by
      by_cases inside : cell next value
      · exact Or.inr (cycle.disjoint next after nextRange afterRange distinct
          value inside)
      · exact Or.inl inside)
  exact (ENNReal.zero_lt_iff_ne_zero.mp charged) wholeNull

end Strong

end Problib.Measure.Kernel
