module

public import Problib.Measure.Kernel.Iteration.Recurrence
public import Problib.Measure.Kernel.Scale
public import Problib.Measure.Integral.Lebesgue.Transport
public import Problib.Real.Extended.Approximation

set_option autoImplicit false

/-! A mixture with one Harris part need not be Harris.

On the natural numbers, `countdown` moves each state `n + 1` to `n` and holds
state 0. It hits every event that holds state 0 from every start, so it is
Harris recurrent for the unit mass at state 0 (`countdown_harris`). The jump
part `climb` holds state 0 and moves each state `n + 1` to `n + 2`. It never
reaches state 0 from state 1, so it is not Harris (`climb_not_harris`). The
mixture `mixed` runs `countdown` with probability one quarter and `climb`
otherwise. From state 1 it hits state 0 with probability at most one half,
because the halving weights `decay` bound the hit mass from above
(`mixed_super`, `not_harris_of_supersolution`). So the mixture is not Harris
(`mixed_not_harris`), although one of its parts is. Harris recurrence does not
pass from one part to the mixture the way a minorization does
(`minorization_mixture`). -/

namespace Problib.Measure.Kernel.Iteration.Necessity.Climb

open Problib.Real Problib.Measure

public section

/-- The natural numbers. Every set is measurable. -/
abbrev naturals : Space Nat := Space.discrete Nat

theorem naturals_ennreal (function : Nat → ENNReal) :
    ENNRealMeasurable naturals function :=
  fun _ => Space.discrete_measurable _

theorem naturals_map (function : Nat → Nat) : MeasurableMap naturals naturals function :=
  fun _ => Space.discrete_measurable _

/-- The unit mass at state 0. -/
@[expose] noncomputable def origin : Measure naturals := Measure.dirac naturals 0

/-- The weight `2⁻ⁿ` at state `n`. -/
@[expose] noncomputable def decay : Nat → ENNReal
  | 0 => ENNReal.one
  | count + 1 => ENNReal.half (decay count)

theorem decay_add_decay (count : Nat) :
    ENNReal.add (decay (count + 1)) (decay (count + 1)) = decay count :=
  ENNReal.half_add_half _

theorem decay_succ_le (count : Nat) : ENNReal.le (decay (count + 1)) (decay count) := by
  rw [← decay_add_decay count]
  exact ENNReal.le_self_add _ _

theorem decay_le_one (count : Nat) : ENNReal.le (decay count) ENNReal.one := by
  induction count with
  | zero => exact ENNReal.le_refl _
  | succ count induction => exact ENNReal.le_trans (decay_succ_le count) induction

theorem decay_positive (count : Nat) : ENNReal.lt ENNReal.zero (decay count) := by
  induction count with
  | zero => exact ENNReal.one_positive
  | succ count induction => exact ENNReal.half_positive induction

theorem decay_one_lt : ENNReal.lt (decay 1) ENNReal.one :=
  ENNReal.half_lt_self_of_positive_of_finite ENNReal.one_positive True.intro

theorem half_one_mul (value : ENNReal) :
    ENNReal.mul (ENNReal.half ENNReal.one) value = ENNReal.half value := by
  conv => lhs; rw [← ENNReal.half_add_half value]
  rw [ENNReal.mul_add, ENNReal.mul_comm, ← ENNReal.mul_add, ENNReal.half_add_half,
    ENNReal.mul_one]

theorem origin_positive_iff {event : Set Nat} :
    ENNReal.lt ENNReal.zero (origin event) ↔ event 0 := by
  constructor
  · intro positive
    apply Classical.byContradiction
    intro absent
    rw [origin, Measure.dirac_apply_of_not_mem _ _ (Space.discrete_measurable _) absent]
      at positive
    exact positive.2 (ENNReal.le_refl _)
  · intro member
    rw [origin, Measure.dirac_apply_of_mem _ _ (Space.discrete_measurable _) member]
    exact ENNReal.one_positive

/-- A chain that hits state 0 from state 1 with probability below one is not
Harris for `origin`. The bound is at least one at state 0 and at least its own
one-step average elsewhere. -/
theorem not_harris_of_supersolution (kernel : Kernel naturals naturals)
    (bound : Nat → ENNReal) (covers : ENNReal.le ENNReal.one (bound 0))
    (super : ∀ count, ENNReal.le (lintegral (kernel (count + 1)) bound) (bound (count + 1)))
    (escapes : ENNReal.lt (bound 1) ENNReal.one) :
    ¬HarrisRecurrent kernel origin := by
  intro harris
  have member : Set.singleton (0 : Nat) 0 := rfl
  rcases harris (Set.singleton 0) (Space.discrete_measurable _)
    (origin_positive_iff.mpr member) 1 with ⟨measurable, hit⟩
  have bounded := hit_mass_le_of_supersolution kernel (Set.singleton 0) measurable bound
    (naturals_ennreal bound)
    (fun input inside => by
      have zero : input = 0 := inside
      subst zero
      exact covers)
    (fun input outside => by
      cases input with
      | zero => exact False.elim (outside rfl)
      | succ count => exact super count)
    1
  rw [hit] at bounded
  exact escapes.2 bounded

/-- Move each state `n + 1` to `n`, and hold state 0. -/
@[expose] noncomputable def countdown : Kernel naturals naturals :=
  Kernel.deterministic Nat.pred (naturals_map _)

/-- The jump part: hold state 0, and move each state `n + 1` to `n + 2`. -/
@[expose] def up : Nat → Nat
  | 0 => 0
  | count + 1 => count + 2

@[expose] noncomputable def climb : Kernel naturals naturals :=
  Kernel.deterministic up (naturals_map _)

/-- The weight one quarter. -/
@[expose] noncomputable def quarter : NNReal := NNReal.half (NNReal.half NNReal.one)

theorem quarter_le_one : NNReal.le quarter NNReal.one :=
  NNReal.le_trans (NNReal.half_le _) (NNReal.half_le _)

/-- Run `countdown` with probability one quarter and `climb` otherwise. -/
@[expose] noncomputable def mixed : Kernel naturals naturals :=
  Kernel.mixture quarter countdown climb

theorem countdown_markov (input : Nat) : Measure.IsProbability (countdown input) :=
  ⟨Measure.dirac_apply_univ _ _⟩

theorem climb_markov (input : Nat) : Measure.IsProbability (climb input) :=
  ⟨Measure.dirac_apply_univ _ _⟩

theorem mixed_markov (input : Nat) : Measure.IsProbability (mixed input) :=
  Kernel.mixture_markov quarter quarter_le_one countdown climb countdown_markov
    climb_markov input

/-- The countdown hits every event that holds state 0, from every start. -/
theorem countdown_harris : HarrisRecurrent countdown origin := by
  intro event measurable positive input
  have zeroMember := origin_positive_iff.mp positive
  induction input with
  | zero => exact hitsAlmostSurely_of_mem _ _ _ measurable zeroMember
  | succ count induction =>
      by_cases member : event (count + 1)
      · exact hitsAlmostSurely_of_mem _ _ _ measurable member
      · refine ⟨measurable, ?_⟩
        rcases induction with ⟨previousMeasurable, previous⟩
        rw [hit_mass_step countdown event measurable member, countdown,
          Kernel.deterministic_apply, lintegral_dirac _ _ (naturals_ennreal _)]
        exact previous

/-- The jump part never reaches state 0 from a positive state. -/
theorem climb_not_harris : ¬HarrisRecurrent climb origin := by
  classical
  apply not_harris_of_supersolution climb
    (fun state => if state = 0 then ENNReal.one else ENNReal.zero)
  · rw [ite_eq_left rfl]
    exact ENNReal.le_refl _
  · intro count
    rw [climb, Kernel.deterministic_apply, lintegral_dirac _ _ (naturals_ennreal _)]
    change ENNReal.le (if count + 2 = 0 then _ else _) _
    rw [ite_eq_right (Nat.succ_ne_zero _)]
    exact ENNReal.zero_le _
  · rw [ite_eq_right (Nat.succ_ne_zero _)]
    exact ENNReal.one_positive

/-- One step of the mixture averages `decay` to at most `decay` at every
positive state. -/
theorem mixed_super (count : Nat) :
    ENNReal.le (lintegral (mixed (count + 1)) decay) (decay (count + 1)) := by
  rw [mixed, Kernel.mixture, Kernel.add_apply, Kernel.smul_apply, Kernel.smul_apply,
    lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure, countdown, climb,
    Kernel.deterministic_apply, Kernel.deterministic_apply,
    lintegral_dirac _ _ (naturals_ennreal _), lintegral_dirac _ _ (naturals_ennreal _)]
  have quartered : ENNReal.mul (ENNReal.finite quarter) (decay count) = decay (count + 2) := by
    change ENNReal.mul (ENNReal.half (ENNReal.half ENNReal.one)) (decay count) =
      ENNReal.half (ENNReal.half (decay count))
    rw [← half_one_mul (ENNReal.half ENNReal.one), ENNReal.mul_assoc, half_one_mul,
      half_one_mul]
  have rest : ENNReal.le (ENNReal.mul (ENNReal.finite (NNReal.sub NNReal.one quarter))
      (decay (count + 2))) (decay (count + 2)) := by
    have lowered := ENNReal.mul_le_mul_right
      (left := ENNReal.finite (NNReal.sub NNReal.one quarter)) (right := ENNReal.one)
      (NNReal.sub_le_self _ _) (decay (count + 2))
    rwa [ENNReal.one_mul] at lowered
  change ENNReal.le (ENNReal.add (ENNReal.mul (ENNReal.finite quarter) (decay count))
    (ENNReal.mul (ENNReal.finite (NNReal.sub NNReal.one quarter)) (decay (count + 2)))) _
  rw [quartered, ← decay_add_decay (count + 1)]
  exact ENNReal.add_le_add (ENNReal.le_refl _) rest

/-- From state 1, the mixture hits state 0 with probability at most one half. -/
theorem mixed_not_harris : ¬HarrisRecurrent mixed origin :=
  not_harris_of_supersolution mixed decay (ENNReal.le_refl _) mixed_super decay_one_lt

end

end Problib.Measure.Kernel.Iteration.Necessity.Climb
