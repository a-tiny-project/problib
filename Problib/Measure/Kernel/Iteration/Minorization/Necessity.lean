import Problib.Measure.Kernel.Iteration.Finite
import Problib.Real.Extended.Approximation

set_option autoImplicit false

/-! A block minorization does not survive interleaving.

The composition rules in `Minorization/Composition.lean` take one-step bounds.
On three states, `averaging` averages states 0 and 1 and fixes state 2,
`cycle` sends each state `s` to `s + 1`, and `reverse` sends it back. The step
`averaging.comp cycle` runs `averaging` and then `cycle`. It has a block
minorization (`step_block_minorization`), and it and `reverse` both preserve
the counting law (`step_invariant`, `reverse_invariant`). Yet running `reverse`
after it gives back `averaging` (`step_comp_reverse`), which keeps states 0 and
1 apart from state 2 forever and so has no minorization at any step count
(`averaging_not_minorized`). -/

open scoped Problib.Real.AC

namespace Problib.Measure.Kernel

open Problib.Real

namespace Iteration.Necessity.Interleaving

/-- Three states. Every set is measurable. -/
abbrev states : Space (Fin 3) := Space.discrete (Fin 3)

private theorem half_positive : ENNReal.lt ENNReal.zero (ENNReal.half ENNReal.one) :=
  ENNReal.zero_lt_iff_ne_zero.mpr (ENNReal.half_ne_zero ENNReal.one_ne_zero)

/-- Half the mass on each of two states. -/
noncomputable def fair (first second : Fin 3) : Measure states :=
  Measure.smul (ENNReal.half ENNReal.one)
    (Measure.add (Measure.dirac states first) (Measure.dirac states second))

private theorem lintegral_fair (first second : Fin 3) (function : Fin 3 → ENNReal) :
    lintegral (fair first second) function =
      ENNReal.mul (ENNReal.half ENNReal.one)
        (ENNReal.add (function first) (function second)) := by
  rw [fair, lintegral_smul_measure, lintegral_add_measure,
    lintegral_dirac _ _ (ENNRealMeasurable.from_discrete _),
    lintegral_dirac _ _ (ENNRealMeasurable.from_discrete _)]

theorem fair_probability (first second : Fin 3) :
    Measure.IsProbability (fair first second) := by
  constructor
  have total := lintegral_fair first second (fun _ => ENNReal.one)
  rw [lintegral_const, ENNReal.one_mul, ENNReal.mul_add, ENNReal.mul_one,
    ENNReal.half_add_half] at total
  exact total

/-- Average states 0 and 1, and fix state 2. -/
noncomputable def averaging : Kernel states states where
  toFun := fun state => if state = 2 then Measure.dirac states 2 else fair 0 1
  measurable := fun _ => ENNRealMeasurable.from_discrete _

theorem averaging_fixed : averaging 2 = Measure.dirac states 2 := by
  change (if (2 : Fin 3) = 2 then Measure.dirac states 2 else fair 0 1) = _
  exact ite_eq_left rfl

theorem averaging_moving {state : Fin 3} (moving : state ≠ 2) :
    averaging state = fair 0 1 := by
  change (if state = 2 then Measure.dirac states 2 else fair 0 1) = _
  exact ite_eq_right moving

theorem averaging_markov (state : Fin 3) : Measure.IsProbability (averaging state) := by
  by_cases fixed : state = 2
  · subst fixed
    rw [averaging_fixed]
    exact Measure.IsProbability.dirac _ _
  · rw [averaging_moving fixed]
    exact fair_probability 0 1

/-- Send each state `s` to `s + 1`. -/
noncomputable def cycle : Kernel states states :=
  Kernel.deterministic (fun state : Fin 3 => state + 1) (fun _ => Space.discrete_measurable _)

/-- Send each state `s` to `s + 2`, undoing `cycle`. -/
noncomputable def reverse : Kernel states states :=
  Kernel.deterministic (fun state : Fin 3 => state + 2) (fun _ => Space.discrete_measurable _)

theorem reverse_markov (state : Fin 3) : Measure.IsProbability (reverse state) :=
  Measure.IsProbability.dirac _ _

/-- Average, then cycle. -/
noncomputable def step : Kernel states states := averaging.comp cycle

theorem step_markov (state : Fin 3) : Measure.IsProbability (step state) :=
  (averaging_markov state).bind cycle (fun _ => Measure.IsProbability.dirac _ _)

theorem step_moving {state : Fin 3} (moving : state ≠ 2) (event : Set (Fin 3)) :
    step state event =
      ENNReal.mul (ENNReal.half ENNReal.one)
        (ENNReal.add (Measure.dirac states 1 event) (Measure.dirac states 2 event)) := by
  rw [step, comp_apply_measurable _ _ _ (Space.discrete_measurable _), averaging_moving moving,
    lintegral_fair]
  rfl

theorem step_fixed (event : Set (Fin 3)) : step 2 event = Measure.dirac states 0 event := by
  rw [step, comp_apply_measurable _ _ _ (Space.discrete_measurable _), averaging_fixed,
    lintegral_dirac _ _ (ENNRealMeasurable.from_discrete _)]
  rfl

/-- `step` minorizes over a block of steps: it reaches state 1 from every
state and holds there with positive probability. -/
theorem step_block_minorization :
    ∃ steps : Nat, ∃ weight : NNReal, ∃ reference : Giry.Law states,
      Minorization step steps weight reference := by
  have moves : ∀ state : Fin 3, state ≠ 2 →
      ENNReal.lt ENNReal.zero (step state (Set.singleton 1)) := by
    intro state moving
    rw [step_moving moving,
      Measure.dirac_apply_of_mem _ _ (set := Set.singleton 1) (Space.discrete_measurable _) rfl,
      Measure.dirac_apply_of_not_mem _ _ (set := Set.singleton 1) (Space.discrete_measurable _)
        (show ¬((2 : Fin 3) = 1) by decide),
      ENNReal.add_zero, ENNReal.mul_one]
    exact half_positive
  have fromFixed : ENNReal.lt ENNReal.zero (step 2 (Set.singleton 0)) := by
    rw [step_fixed,
      Measure.dirac_apply_of_mem _ _ (set := Set.singleton 0) (Space.discrete_measurable _) rfl]
    exact ENNReal.zero_lt_iff_ne_zero.mpr ENNReal.one_ne_zero
  have reachesOne : ∀ state : Fin 3, state ≠ 2 → Reaches step state 1 :=
    fun state moving => reaches_step step (moves state moving) (reaches_refl step 1)
  apply finite_accessible_aperiodic_minorization (List.finRange 3)
    (FiniteEnumeration.finRange 3) step step_markov 1
  · intro state
    by_cases fixed : state = 2
    · subst fixed
      exact reaches_step step fromFixed (reachesOne 0 (by decide))
    · exact reachesOne state fixed
  · exact aperiodicAt_of_hold step (moves 1 (by decide))

private theorem cycle_comp_reverse :
    cycle.comp reverse =
      Kernel.deterministic (fun state => state) (MeasurableMap.identity states) := by
  apply Kernel.ext
  intro state
  have loop : state + 1 + 2 = state := by revert state; decide
  rw [comp_apply]
  change (Measure.dirac states (state + 1)).bind reverse = Measure.dirac states state
  rw [Measure.dirac_bind]
  change Measure.dirac states (state + 1 + 2) = Measure.dirac states state
  rw [loop]

/-- Running `reverse` after `step` gives back `averaging`. -/
theorem step_comp_reverse : step.comp reverse = averaging := by
  rw [step, comp_assoc, cycle_comp_reverse, comp_deterministic]
  apply Kernel.ext
  intro state
  rw [map_apply, Measure.map_id]

private theorem averaging_fixed_forever (steps : Nat) :
    iterate averaging steps 2 = Measure.dirac states 2 := by
  induction steps with
  | zero => rw [iterate_zero, Kernel.deterministic_apply]
  | succ steps induction =>
      rw [iterate_succ, comp_apply, averaging_fixed, Measure.dirac_bind, induction]

private theorem averaging_never_fixes (steps : Nat) (state : Fin 3) (moving : state ≠ 2) :
    iterate averaging steps state (Set.singleton 2) = ENNReal.zero := by
  induction steps generalizing state with
  | zero =>
      rw [iterate_zero, Kernel.deterministic_apply,
        Measure.dirac_apply_of_not_mem _ _ (set := Set.singleton 2)
          (Space.discrete_measurable _) moving]
  | succ steps induction =>
      rw [iterate_succ, comp_apply_measurable _ _ _ (Space.discrete_measurable _),
        averaging_moving moving, lintegral_fair, induction 0 (by decide),
        induction 1 (by decide), ENNReal.add_zero, ENNReal.mul_zero]

/-- `averaging` has no minorization at any step count: from state 0 it never
reaches state 2, and from state 2 it never leaves. -/
theorem averaging_not_minorized (steps : Nat) (weight : NNReal)
    (reference : Giry.Law states) : ¬Minorization averaging steps weight reference := by
  intro minor
  let low : Set (Fin 3) := fun state => state ≠ 2
  have weightNonzero : ENNReal.finite weight ≠ ENNReal.zero := fun zero =>
    (NNReal.zero_lt_iff_ne_zero _).mp minor.weightPositive (ENNReal.finite_injective zero)
  have highNull : reference.val (Set.singleton 2) = ENNReal.zero := by
    have lower := minor.lower 0 (Set.singleton 2) (Space.discrete_measurable _)
    rw [averaging_never_fixes steps 0 (by decide),
      Measure.smul_apply_measurable _ _ (Space.discrete_measurable _), ENNReal.le_zero_iff,
      ENNReal.mul_eq_zero_iff] at lower
    exact lower.resolve_left weightNonzero
  have lowNull : reference.val low = ENNReal.zero := by
    have lower := minor.lower 2 low (Space.discrete_measurable _)
    rw [averaging_fixed_forever,
      Measure.dirac_apply_of_not_mem _ _ (set := low) (Space.discrete_measurable _)
        (fun moving => moving rfl),
      Measure.smul_apply_measurable _ _ (Space.discrete_measurable _), ENNReal.le_zero_iff,
      ENNReal.mul_eq_zero_iff] at lower
    exact lower.resolve_left weightNonzero
  have cover : Set.union (Set.singleton 2) low = Set.univ := by
    apply Set.ext
    intro state
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    by_cases fixed : state = 2
    · exact Or.inl fixed
    · exact Or.inr fixed
  have total := reference.property.univ_eq_one
  rw [← cover, reference.val.union_disjoint (Space.discrete_measurable _)
    (Space.discrete_measurable _) (fun _ fixed moving => moving fixed),
    highNull, lowNull, ENNReal.add_zero] at total
  exact ENNReal.one_ne_zero total.symm

/-- One unit of mass on each state. -/
noncomputable def count : Measure states :=
  Measure.add (Measure.add (Measure.dirac states 0) (Measure.dirac states 1))
    (Measure.dirac states 2)

theorem step_invariant : count.bind step = count := by
  apply Measure.ext
  intro event eventMeasurable
  have double : ∀ value, ENNReal.add (ENNReal.mul (ENNReal.half ENNReal.one) value)
      (ENNReal.mul (ENNReal.half ENNReal.one) value) = value := by
    intro value
    rw [ENNReal.mul_comm, ← ENNReal.mul_add, ENNReal.half_add_half, ENNReal.mul_one]
  rw [Measure.bind_apply _ _ eventMeasurable, count, lintegral_add_measure,
    lintegral_add_measure, lintegral_dirac _ _ (ENNRealMeasurable.from_discrete _),
    lintegral_dirac _ _ (ENNRealMeasurable.from_discrete _),
    lintegral_dirac _ _ (ENNRealMeasurable.from_discrete _),
    step_moving (state := 0) (by decide), step_moving (state := 1) (by decide), step_fixed,
    double, Measure.add_apply_measurable _ _ eventMeasurable,
    Measure.add_apply_measurable _ _ eventMeasurable]
  ac_rfl

theorem reverse_invariant : count.bind reverse = count := by
  apply Measure.ext
  intro event eventMeasurable
  rw [Measure.bind_apply _ _ eventMeasurable, count, lintegral_add_measure,
    lintegral_add_measure, lintegral_dirac _ _ (ENNRealMeasurable.from_discrete _),
    lintegral_dirac _ _ (ENNRealMeasurable.from_discrete _),
    lintegral_dirac _ _ (ENNRealMeasurable.from_discrete _),
    Measure.add_apply_measurable _ _ eventMeasurable,
    Measure.add_apply_measurable _ _ eventMeasurable]
  change ENNReal.add (ENNReal.add (Measure.dirac states 2 event) (Measure.dirac states 0 event))
      (Measure.dirac states 1 event) = _
  ac_rfl

/-- A block bound does not survive interleaving, even between Markov steps that
share an invariant law. `step` minorizes over a block, `reverse` is Markov, both
preserve `count`, and `step.comp reverse` has no minorization at any step
count. -/
theorem block_minorization_not_interleaved :
    (∃ steps : Nat, ∃ weight : NNReal, ∃ reference : Giry.Law states,
      Minorization step steps weight reference) ∧
    (∀ state, Measure.IsProbability (reverse state)) ∧
    count.bind step = count ∧ count.bind reverse = count ∧
    ∀ steps weight reference, ¬Minorization (step.comp reverse) steps weight reference := by
  refine ⟨step_block_minorization, reverse_markov, step_invariant, reverse_invariant, ?_⟩
  rw [step_comp_reverse]
  exact averaging_not_minorized

end Iteration.Necessity.Interleaving

end Problib.Measure.Kernel
