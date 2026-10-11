module

public import Problib.Inference.MetropolisHastings.Support

set_option autoImplicit false

/-! A null start stays trapped.

On four states with weights `1, 1, 0, 0`, a Metropolis step proposes a
neighbour, reflecting at the ends (`trap`). It leaves the weighted target, one
unit on each of states 0 and 1, invariant (`trap_invariant`). The strict test
rejects the move from state 3 to state 2 because both weigh zero, so a chain
started at state 3 stays there at every step (`trap_stays`), while the target
gives state 3 no mass (`trapTarget_null`). Convergence from every start needs an
entrance premise beyond invariance. -/

open scoped Problib.Real.AC

namespace Problib.Inference.Necessity.Support

open Problib.Real Problib.Measure
open Problib.Real.Construction
open Problib.Measure.Real (Carrier borel)

public section

/-- Four states. Every set is measurable. -/
abbrev states : Space (Fin 4) := Space.discrete (Fin 4)

theorem states_ennreal (function : Fin 4 → ENNReal) :
    ENNRealMeasurable states function :=
  fun _ => Space.discrete_measurable _

/-- The neighbour below, staying at state 0. -/
@[expose] def below : Fin 4 → Fin 4
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 1
  | _ => 2

/-- The neighbour above, staying at state 3. -/
@[expose] def above : Fin 4 → Fin 4
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 2
  | _ => 3

/-- Propose each neighbour with probability one half. -/
@[expose] noncomputable def neighbour : Kernel states states where
  toFun := fun state => Measure.smul (ENNReal.half ENNReal.one)
    (Measure.add (Measure.dirac states (below state)) (Measure.dirac states (above state)))
  measurable := fun _ => states_ennreal _

private theorem double (value : ENNReal) :
    ENNReal.mul (ENNReal.half ENNReal.one) (ENNReal.add value value) = value := by
  rw [ENNReal.mul_add, ENNReal.mul_comm, ← ENNReal.mul_add, ENNReal.half_add_half,
    ENNReal.mul_one]

theorem neighbour_markov (state : Fin 4) : Measure.IsProbability (neighbour state) := by
  constructor
  change Measure.smul (ENNReal.half ENNReal.one)
    (Measure.add (Measure.dirac states (below state)) (Measure.dirac states (above state)))
      Set.univ = _
  rw [Measure.smul_apply_measurable _ _ states.univ,
    Measure.add_apply_measurable _ _ states.univ, Measure.dirac_apply_univ,
    Measure.dirac_apply_univ, double]

@[expose] noncomputable def neighbourFinite : Kernel.IsSFinite neighbour :=
  Kernel.IsFinite.toSFinite
    { exists_bound := ⟨ENNReal.one, True.intro, fun state => by
        rw [(neighbour_markov state).univ_eq_one]
        exact ENNReal.le_refl _⟩ }

/-- Weight one on states 0 and 1, and zero on states 2 and 3. -/
@[expose] noncomputable def weight (state : Fin 4) : Carrier :=
  if state.val < 2 then Dedekind.one else Dedekind.zero

theorem weight_measurable : MeasurableMap states borel weight :=
  fun _ => Space.discrete_measurable _

/-- The Metropolis step for `weight` with neighbour proposals. -/
@[expose] noncomputable def trap : Kernel states states :=
  mhKernel neighbour neighbourFinite (metropolisAccept weight)
    (metropolisAccept_measurable weight_measurable)

/-- One unit of mass on each state. -/
@[expose] noncomputable def count : Measure states :=
  Measure.add
    (Measure.add (Measure.dirac states 0) (Measure.dirac states 1))
    (Measure.add (Measure.dirac states 2) (Measure.dirac states 3))

/-- The weighted target. -/
@[expose] noncomputable def trapTarget : Measure states :=
  count.withDensity fun state => ENNReal.ofReal (weight state)

private theorem accept_heavy {current proposed : Fin 4}
    (currentHeavy : current.val < 2) (proposedHeavy : proposed.val < 2) :
    metropolisAccept weight (current, proposed) = ENNReal.one := by
  have currentWeight : weight current = Dedekind.one := ite_eq_left currentHeavy
  have proposedWeight : weight proposed = Dedekind.one := ite_eq_left proposedHeavy
  apply metropolisAccept_eq_one
  · change Dedekind.le (weight current) (weight proposed)
    rw [currentWeight, proposedWeight]
    exact Dedekind.le_refl _
  · change Dedekind.lt Dedekind.zero (weight proposed)
    rw [proposedWeight]
    exact Dedekind.one_positive

private theorem weight_nonnegative (state : Fin 4) : Dedekind.le Dedekind.zero (weight state) := by
  unfold weight
  split
  · exact Dedekind.one_positive.1
  · exact Dedekind.le_refl _

private theorem accept_light {current proposed : Fin 4} (proposedLight : ¬proposed.val < 2) :
    metropolisAccept weight (current, proposed) = ENNReal.zero := by
  apply metropolisAccept_eq_zero (weight_nonnegative current)
  change Dedekind.le (weight proposed) Dedekind.zero
  rw [weight, ite_eq_right proposedLight]
  exact Dedekind.le_refl _

private theorem move (proposedIndicator currentIndicator : ENNReal) :
    ENNReal.add (ENNReal.mul ENNReal.one proposedIndicator)
      (ENNReal.mul (ENNReal.sub ENNReal.one ENNReal.one) currentIndicator) =
        proposedIndicator := by
  rw [ENNReal.one_mul, ENNReal.sub_self, ENNReal.zero_mul, ENNReal.add_zero]

private theorem hold (proposedIndicator currentIndicator : ENNReal) :
    ENNReal.add (ENNReal.mul ENNReal.zero proposedIndicator)
      (ENNReal.mul (ENNReal.sub ENNReal.one ENNReal.zero) currentIndicator) =
        currentIndicator := by
  rw [ENNReal.zero_mul, ENNReal.sub_zero, ENNReal.one_mul, ENNReal.zero_add]

private theorem trap_apply (state : Fin 4) {event : Set (Fin 4)} :
    trap state event =
      ENNReal.mul (ENNReal.half ENNReal.one)
        (ENNReal.add
          (ENNReal.add
            (ENNReal.mul (metropolisAccept weight (state, below state))
              (ennrealIndicator event (fun _ => ENNReal.one) (below state)))
            (ENNReal.mul (ENNReal.sub ENNReal.one (metropolisAccept weight (state, below state)))
              (ennrealIndicator event (fun _ => ENNReal.one) state)))
          (ENNReal.add
            (ENNReal.mul (metropolisAccept weight (state, above state))
              (ennrealIndicator event (fun _ => ENNReal.one) (above state)))
            (ENNReal.mul (ENNReal.sub ENNReal.one (metropolisAccept weight (state, above state)))
              (ennrealIndicator event (fun _ => ENNReal.one) state)))) := by
  rw [trap, apply_eq_lintegral_indicator _ (Space.discrete_measurable _),
    lintegral_mhKernel _ _ _ _ _ (states_ennreal _)]
  change lintegral (Measure.smul (ENNReal.half ENNReal.one)
    (Measure.add (Measure.dirac states (below state)) (Measure.dirac states (above state)))) _ = _
  rw [lintegral_smul_measure, lintegral_add_measure, lintegral_dirac _ _ (states_ennreal _),
    lintegral_dirac _ _ (states_ennreal _)]

private theorem dirac_indicator (point : Fin 4) (event : Set (Fin 4)) :
    Measure.dirac states point event = ennrealIndicator event (fun _ => ENNReal.one) point := by
  rw [apply_eq_lintegral_indicator _ (Space.discrete_measurable _),
    lintegral_dirac _ _ (states_ennreal _)]

/-- From state 0, the step moves to states 0 and 1 with probability one half
each. -/
theorem trap_zero (event : Set (Fin 4)) :
    trap 0 event =
      ENNReal.mul (ENNReal.half ENNReal.one)
        (ENNReal.add (Measure.dirac states 0 event) (Measure.dirac states 1 event)) := by
  rw [trap_apply, dirac_indicator, dirac_indicator,
    accept_heavy (current := 0) (proposed := below 0) (by decide) (by decide),
    accept_heavy (current := 0) (proposed := above 0) (by decide) (by decide), move, move]
  rfl

/-- From state 1, the step moves to state 0 or holds, with probability one half
each. -/
theorem trap_one (event : Set (Fin 4)) :
    trap 1 event =
      ENNReal.mul (ENNReal.half ENNReal.one)
        (ENNReal.add (Measure.dirac states 0 event) (Measure.dirac states 1 event)) := by
  rw [trap_apply, dirac_indicator, dirac_indicator,
    accept_heavy (current := 1) (proposed := below 1) (by decide) (by decide),
    accept_light (current := 1) (proposed := above 1) (by decide), move, hold]
  rfl

/-- The strict test rejects every proposal from state 3, so the step holds
there. -/
theorem trap_holds : trap 3 = Measure.dirac states 3 := by
  apply Measure.ext
  intro event _
  rw [trap_apply, accept_light (current := 3) (proposed := below 3) (by decide),
    accept_light (current := 3) (proposed := above 3) (by decide), hold, hold, double,
    dirac_indicator]

/-- A chain started at state 3 stays there at every step. -/
theorem trap_stays (steps : Nat) : Kernel.iterate trap steps 3 = Measure.dirac states 3 := by
  induction steps with
  | zero => rw [Kernel.iterate_zero, Kernel.deterministic_apply]
  | succ steps induction =>
      rw [Kernel.iterate_succ, Kernel.comp_apply, trap_holds, Measure.dirac_bind, induction]

/-- The target is one unit on each of states 0 and 1. -/
theorem trapTarget_eq :
    trapTarget = Measure.add (Measure.dirac states 0) (Measure.dirac states 1) := by
  apply Measure.ext
  intro event eventMeasurable
  have weightMeasurable : ENNRealMeasurable states (fun state => ENNReal.ofReal (weight state)) :=
    states_ennreal _
  rw [trapTarget, apply_eq_lintegral_indicator _ eventMeasurable,
    lintegral_withDensity _ weightMeasurable (states_ennreal _), count,
    lintegral_add_measure, lintegral_add_measure, lintegral_add_measure,
    lintegral_dirac _ _ (states_ennreal _), lintegral_dirac _ _ (states_ennreal _),
    lintegral_dirac _ _ (states_ennreal _), lintegral_dirac _ _ (states_ennreal _),
    Measure.add_apply_measurable _ _ eventMeasurable, dirac_indicator, dirac_indicator]
  have heavy : ∀ state : Fin 4, state.val < 2 → ENNReal.ofReal (weight state) = ENNReal.one :=
    fun state heavy => by rw [weight, ite_eq_left heavy, ENNReal.ofReal_one]
  have light : ∀ state : Fin 4, ¬state.val < 2 → ENNReal.ofReal (weight state) = ENNReal.zero :=
    fun state light => by rw [weight, ite_eq_right light, ENNReal.ofReal_zero]
  rw [heavy 0 (by decide), heavy 1 (by decide), light 2 (by decide), light 3 (by decide),
    ENNReal.one_mul, ENNReal.one_mul, ENNReal.zero_mul, ENNReal.zero_mul, ENNReal.add_zero,
    ENNReal.add_zero]

/-- The target gives state 3 no mass. -/
theorem trapTarget_null : trapTarget (Set.singleton 3) = ENNReal.zero := by
  rw [trapTarget_eq, Measure.add_apply_measurable _ _ (Space.discrete_measurable _),
    Measure.dirac_apply_of_not_mem _ _ (set := Set.singleton 3) (Space.discrete_measurable _)
      (show ¬((0 : Fin 4) = 3) by decide),
    Measure.dirac_apply_of_not_mem _ _ (set := Set.singleton 3) (Space.discrete_measurable _)
      (show ¬((1 : Fin 4) = 3) by decide),
    ENNReal.add_zero]

/-- The step leaves the weighted target invariant. -/
theorem trap_invariant : KernelInvariant trapTarget trap := by
  unfold KernelInvariant
  rw [trapTarget_eq]
  apply Measure.ext
  intro event eventMeasurable
  rw [Measure.bind_apply _ _ eventMeasurable, lintegral_add_measure,
    lintegral_dirac _ _ (states_ennreal _), lintegral_dirac _ _ (states_ennreal _),
    trap_zero, trap_one,
    ← ENNReal.mul_add, ENNReal.mul_add, ENNReal.mul_comm, ← ENNReal.mul_add,
    ENNReal.half_add_half, ENNReal.mul_one, Measure.add_apply_measurable _ _ eventMeasurable]

/-- A null start stays trapped: the Metropolis step leaves its weighted target
invariant, yet from state 3, which the target does not charge, it stays at
state 3 at every step. -/
theorem null_start_trapped :
    KernelInvariant trapTarget trap ∧ trapTarget (Set.singleton 3) = ENNReal.zero ∧
      ∀ steps, Kernel.iterate trap steps 3 = Measure.dirac states 3 :=
  ⟨trap_invariant, trapTarget_null, trap_stays⟩

end

end Problib.Inference.Necessity.Support
