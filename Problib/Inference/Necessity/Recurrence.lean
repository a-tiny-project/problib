module

public import Problib.Inference.MetropolisHastings.Support
public import Problib.Measure.Kernel.Iteration.Recurrence.Necessity

set_option autoImplicit false

/-! An escaping chain is irreducible and invariant but not Harris.

On the natural numbers, `escape` moves each state to state 0 with probability
`leave` and otherwise to the next state. State 0 is absorbing, so the chain
leaves the unit mass `origin` at state 0 invariant (`escape_invariant`), and it
reaches state 0 in one step from every start (`escape_irreducible`). The
chance of leaving for state 0 halves at each state, so a chain started at
state 1 escapes upward with probability at least one half (`escape_super`),
and the chain is not Harris for `origin` (`escape_not_harris`). Its upward
moves land where `origin` puts no mass, so its moves are not dominated
(`escape_not_dominated`). Every premise of `harris_of_dominated_moves` except
dominated moves holds (`escape_needs_dominated`). -/

namespace Problib.Inference.Necessity.Recurrence

open Problib.Real Problib.Measure
open Problib.Measure.Kernel.Iteration.Necessity.Climb

public section

/-- The chance of moving to state 0: one at state 0, and `decay (n + 2)` at
state `n + 1`. -/
@[expose] noncomputable def leave : Nat → ENNReal
  | 0 => ENNReal.one
  | count + 1 => decay (count + 2)

theorem leave_le_one (state : Nat) : ENNReal.le (leave state) ENNReal.one := by
  cases state with
  | zero => exact ENNReal.le_refl _
  | succ count => exact decay_le_one _

theorem leave_positive (state : Nat) : ENNReal.lt ENNReal.zero (leave state) := by
  cases state with
  | zero => exact ENNReal.one_positive
  | succ count => exact decay_positive _

/-- Move to state 0 with probability `leave`, and otherwise to the next state. -/
@[expose] noncomputable def escape : Kernel naturals naturals where
  toFun := fun state => Measure.add (Measure.smul (leave state) (Measure.dirac naturals 0))
    (Measure.smul (ENNReal.sub ENNReal.one (leave state)) (Measure.dirac naturals (state + 1)))
  measurable := fun _ => naturals_ennreal _

theorem escape_apply (state : Nat) (event : Set Nat) :
    escape state event =
      ENNReal.add (ENNReal.mul (leave state) (Measure.dirac naturals 0 event))
        (ENNReal.mul (ENNReal.sub ENNReal.one (leave state))
          (Measure.dirac naturals (state + 1) event)) := by
  change Measure.add _ _ event = _
  rw [Measure.add_apply_measurable _ _ (Space.discrete_measurable _),
    Measure.smul_apply_measurable _ _ (Space.discrete_measurable _),
    Measure.smul_apply_measurable _ _ (Space.discrete_measurable _)]

theorem escape_markov (state : Nat) : Measure.IsProbability (escape state) := by
  constructor
  rw [escape_apply, Measure.dirac_apply_univ, Measure.dirac_apply_univ, ENNReal.mul_one,
    ENNReal.mul_one, ENNReal.add_comm, ENNReal.sub_add_cancel (leave_le_one state)]

/-- State 0 is absorbing. -/
theorem escape_zero : escape 0 = origin := by
  apply Measure.ext
  intro event _
  rw [escape_apply]
  change ENNReal.add (ENNReal.mul ENNReal.one _)
    (ENNReal.mul (ENNReal.sub ENNReal.one ENNReal.one) _) = _
  rw [ENNReal.one_mul, ENNReal.sub_self, ENNReal.zero_mul, ENNReal.add_zero]
  rfl

theorem escape_invariant : KernelInvariant origin escape := by
  change (Measure.dirac naturals 0).bind escape = origin
  rw [Measure.dirac_bind, escape_zero]

/-- Every start reaches every event that holds state 0 in one step. -/
theorem escape_irreducible : Kernel.MeasureIrreducible escape origin := by
  refine ⟨?_, ?_⟩
  · rw [origin, Measure.dirac_apply_univ]
    exact ENNReal.one_positive
  · intro event _ positive input
    refine ⟨0, ?_⟩
    have member := origin_positive_iff.mp positive
    rw [Kernel.iterate_succ, Kernel.iterate_zero, Kernel.comp_apply,
      Measure.bind_deterministic, Measure.map_id, escape_apply,
      Measure.dirac_apply_of_mem _ _ (Space.discrete_measurable _) member, ENNReal.mul_one]
    have raised := ENNReal.add_le_add (ENNReal.le_refl (leave input))
      (ENNReal.zero_le (ENNReal.mul (ENNReal.sub ENNReal.one (leave input))
        (Measure.dirac naturals (input + 1) event)))
    rw [ENNReal.add_zero] at raised
    exact ⟨ENNReal.zero_le _,
      fun below => (leave_positive input).2 (ENNReal.le_trans raised below)⟩

/-- One step averages `decay` to at most `decay` at every positive state. -/
theorem escape_super (count : Nat) :
    ENNReal.le (lintegral (escape (count + 1)) decay) (decay (count + 1)) := by
  change ENNReal.le (lintegral (Measure.add
    (Measure.smul (leave (count + 1)) (Measure.dirac naturals 0))
    (Measure.smul (ENNReal.sub ENNReal.one (leave (count + 1)))
      (Measure.dirac naturals (count + 1 + 1)))) decay) _
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac _ _ (naturals_ennreal _), lintegral_dirac _ _ (naturals_ennreal _)]
  change ENNReal.le (ENNReal.add (ENNReal.mul (decay (count + 2)) ENNReal.one)
    (ENNReal.mul (ENNReal.sub ENNReal.one (decay (count + 2))) (decay (count + 2)))) _
  have rest : ENNReal.le
      (ENNReal.mul (ENNReal.sub ENNReal.one (decay (count + 2))) (decay (count + 2)))
      (decay (count + 2)) := by
    have lowered := ENNReal.mul_le_mul_right
      (ENNReal.sub_le_self ENNReal.one (decay (count + 2))) (decay (count + 2))
    rwa [ENNReal.one_mul] at lowered
  rw [ENNReal.mul_one, ← decay_add_decay (count + 1)]
  exact ENNReal.add_le_add (ENNReal.le_refl _) rest

/-- From state 1, the chain hits state 0 with probability at most one half. -/
theorem escape_not_harris : ¬Kernel.HarrisRecurrent escape origin :=
  not_harris_of_supersolution escape decay (ENNReal.le_refl _) escape_super decay_one_lt

/-- The move from state 1 to state 2 has positive probability, and `origin`
gives state 2 no mass. -/
theorem escape_not_dominated : ¬DominatedMoves escape origin := by
  rintro ⟨accepted, holding, _, _, decomposition, dominated⟩
  have originNull : origin (Set.singleton 2) = ENNReal.zero :=
    Measure.dirac_apply_of_not_mem _ _ (set := Set.singleton 2) (Space.discrete_measurable _)
      (show ¬((0 : Nat) = 2) by decide)
  have acceptedNull : accepted 1 (Set.singleton 2) = ENNReal.zero :=
    dominated 1 (Space.discrete_measurable (Set.singleton 2)) originNull
  have stepNull : escape 1 (Set.singleton 2) = ENNReal.zero := by
    rw [decomposition 1, Measure.add_apply_measurable _ _ (Space.discrete_measurable _),
      Measure.smul_apply_measurable _ _ (Space.discrete_measurable _), acceptedNull,
      Measure.dirac_apply_of_not_mem _ _ (set := Set.singleton 2) (Space.discrete_measurable _)
        (show ¬((1 : Nat) = 2) by decide),
      ENNReal.mul_zero, ENNReal.add_zero]
  rw [escape_apply,
    Measure.dirac_apply_of_not_mem _ _ (set := Set.singleton 2) (Space.discrete_measurable _)
      (show ¬((0 : Nat) = 2) by decide),
    Measure.dirac_apply_of_mem _ _ (set := Set.singleton 2) (Space.discrete_measurable _)
      (show (1 + 1 : Nat) = 2 from rfl),
    ENNReal.mul_zero, ENNReal.zero_add, ENNReal.mul_one] at stepNull
  exact decay_one_lt.2
    (ENNReal.le_trans (ENNReal.sub_eq_zero_iff_le.mp stepNull) (decay_succ_le 1))

/-- Dominated moves are needed in `harris_of_dominated_moves`: the chain is
Markov, `origin` is finite, invariant and charged from every start, yet the
moves are not dominated and the chain is not Harris. -/
theorem escape_needs_dominated :
    (∀ state, Measure.IsProbability (escape state)) ∧ Measure.IsFinite origin ∧
      KernelInvariant origin escape ∧ Kernel.MeasureIrreducible escape origin ∧
      ¬DominatedMoves escape origin ∧ ¬Kernel.HarrisRecurrent escape origin :=
  ⟨escape_markov, Measure.IsFinite.dirac naturals 0, escape_invariant, escape_irreducible,
    escape_not_dominated, escape_not_harris⟩

end

end Problib.Inference.Necessity.Recurrence
