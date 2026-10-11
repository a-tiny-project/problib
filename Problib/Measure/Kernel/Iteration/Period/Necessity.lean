module

public import Problib.Measure.Kernel.Iteration.Period
public import Problib.Real.Extended.Approximation
import Problib.Measure.Integral.Lebesgue.Transport

set_option autoImplicit false

/-!
# A small set the invariant law does not charge

The period lemmas ask that the invariant law charge the region. On three states,
`kernel` sends state 0 to states 1 and 2 with probability one half each, sends
state 1 back to state 0, and fixes state 2. The unit mass at state 2 is invariant
and the kernel is irreducible against it. The region {0} with the unit mass at
state 0 is minorized in two steps, and no odd iterate returns to state 0 from it,
so two divides every minorized count. Yet no two disjoint cells carry mass at
state 2, so the kernel is aperiodic and has no cycle of period two
(`cycle_needs_charged_region`), and the odd counts are never minorized
(`eventually_needs_charged_region`). The region is null for the invariant law,
which is the one premise these fail.
-/

namespace Problib.Measure.Kernel

open Problib.Real

namespace Iteration.Necessity.Transient

/-- Three states. Every set is measurable. -/
public abbrev states : Space (Fin 3) := Space.discrete (Fin 3)

/-- The law of the next state from each state. -/
private noncomputable def next (state : Fin 3) : Measure states :=
  if state = 0 then
    Measure.smul (ENNReal.half ENNReal.one)
      (Measure.add (Measure.dirac states 1) (Measure.dirac states 2))
  else if state = 1 then Measure.dirac states 0 else Measure.dirac states 2

/-- From state 0, move to state 1 or state 2 with probability one half each.
State 1 returns to state 0, and state 2 absorbs. -/
public noncomputable def kernel : Kernel states states where
  toFun := next
  measurable := fun _ => ENNRealMeasurable.from_discrete _

/-- The unit mass at the absorbing state. -/
public noncomputable def absorbed : Giry.Law states :=
  ⟨Measure.dirac states 2, Measure.IsProbability.dirac _ _⟩

/-- The unit mass at the region's state. -/
public noncomputable def start : Giry.Law states :=
  ⟨Measure.dirac states 0, Measure.IsProbability.dirac _ _⟩

/-- The region: state 0 alone. -/
public abbrev region : Set (Fin 3) := Set.singleton 0

private theorem kernel_zero : kernel 0 = Measure.smul (ENNReal.half ENNReal.one)
    (Measure.add (Measure.dirac states 1) (Measure.dirac states 2)) := by
  change next 0 = _
  unfold next
  rw [ite_eq_left rfl]

private theorem kernel_one : kernel 1 = Measure.dirac states 0 := by
  change next 1 = _
  unfold next
  rw [ite_eq_right (by decide), ite_eq_left rfl]

private theorem kernel_two : kernel 2 = Measure.dirac states 2 := by
  change next 2 = _
  unfold next
  rw [ite_eq_right (by decide), ite_eq_right (by decide)]

private theorem lintegral_kernel_zero (function : Fin 3 → ENNReal) :
    lintegral (kernel 0) function =
      ENNReal.mul (ENNReal.half ENNReal.one)
        (ENNReal.add (function 1) (function 2)) := by
  rw [kernel_zero, lintegral_smul_measure, lintegral_add_measure,
    lintegral_dirac _ _ (ENNRealMeasurable.from_discrete _),
    lintegral_dirac _ _ (ENNRealMeasurable.from_discrete _)]

private theorem iterate_succ_apply (count : Nat) (state : Fin 3)
    (event : Set (Fin 3)) :
    iterate kernel (count + 1) state event =
      lintegral (kernel state) (fun next => iterate kernel count next event) := by
  rw [iterate_succ, comp_apply_measurable _ _ _ (Space.discrete_measurable _)]

public theorem kernel_markov (state : Fin 3) :
    Measure.IsProbability (kernel state) := by
  by_cases first : state = 0
  · subst first
    constructor
    have total := lintegral_kernel_zero (fun _ => ENNReal.one)
    rw [lintegral_const, ENNReal.one_mul, ENNReal.mul_add, ENNReal.mul_one,
      ENNReal.half_add_half] at total
    exact total
  by_cases second : state = 1
  · subst second
    rw [kernel_one]
    exact Measure.IsProbability.dirac _ _
  have third : state = 2 := by omega
  subst third
  rw [kernel_two]
  exact Measure.IsProbability.dirac _ _

/-- The unit mass at the absorbing state is invariant. -/
public theorem absorbed_invariant : absorbed.val.bind kernel = absorbed.val := by
  apply Measure.ext
  intro event measurable
  change (Measure.dirac states 2).bind kernel event = Measure.dirac states 2 event
  rw [Measure.bind_apply _ _ measurable, lintegral_dirac _ _ (ENNRealMeasurable.from_discrete _),
    kernel_two]

private theorem mem_of_charged {event : Set (Fin 3)}
    (charged : ENNReal.lt ENNReal.zero (absorbed.val event)) : event 2 := by
  apply Classical.byContradiction
  intro outside
  change ENNReal.lt ENNReal.zero (Measure.dirac states 2 event) at charged
  rw [Measure.dirac_apply_of_not_mem _ _ (Space.discrete_measurable _) outside]
    at charged
  exact (ENNReal.zero_lt_iff_ne_zero.mp charged) rfl

private theorem kernel_zero_charges {event : Set (Fin 3)} (inside : event 2) :
    ENNReal.lt ENNReal.zero (kernel 0 event) := by
  rw [apply_eq_lintegral_indicator _ (Space.discrete_measurable _),
    lintegral_kernel_zero]
  apply ENNReal.zero_lt_iff_ne_zero.mpr
  intro vanished
  rcases ENNReal.mul_eq_zero_iff.mp vanished with half | sum
  · exact ENNReal.half_ne_zero ENNReal.one_ne_zero half
  · have atTwo := (ENNReal.add_eq_zero_iff.mp sum).2
    rw [ennrealIndicator, ennrealPiecewise, ite_eq_left inside] at atTwo
    exact ENNReal.one_ne_zero atTwo

/-- Every state reaches the absorbing state, so the kernel is irreducible
against its unit mass. -/
public theorem absorbed_irreducible : MeasureIrreducible kernel absorbed.val := by
  refine ⟨?_, ?_⟩
  · change ENNReal.lt ENNReal.zero (Measure.dirac states 2 Set.univ)
    rw [Measure.dirac_apply_of_mem _ _ (Space.discrete_measurable _) trivial]
    exact ENNReal.one_positive
  intro event _ charged state
  have inside := mem_of_charged charged
  by_cases first : state = 0
  · subst first
    refine ⟨0, ?_⟩
    rw [iterate_one]
    exact kernel_zero_charges inside
  by_cases second : state = 1
  · subst second
    refine ⟨1, ?_⟩
    rw [iterate_succ_apply, kernel_one, lintegral_dirac _ _ (ENNRealMeasurable.from_discrete _),
      iterate_one]
    exact kernel_zero_charges inside
  have third : state = 2 := by omega
  subst third
  refine ⟨0, ?_⟩
  rw [iterate_one, kernel_two,
    Measure.dirac_apply_of_mem _ _ (Space.discrete_measurable _) inside]
  exact ENNReal.one_positive

/-- The invariant law does not charge the region. -/
public theorem absorbed_region : absorbed.val region = ENNReal.zero :=
  Measure.dirac_apply_of_not_mem _ _ (Space.discrete_measurable _)
    (by decide : ¬(2 : Fin 3) = 0)

/-- The minorant charges the region. -/
public theorem start_region : ENNReal.lt ENNReal.zero (start.val region) := by
  change ENNReal.lt ENNReal.zero (Measure.dirac states 0 (Set.singleton 0))
  rw [Measure.dirac_apply_of_mem _ _ (set := Set.singleton 0)
    (Space.discrete_measurable _) rfl]
  exact ENNReal.one_positive

/-- Two steps from state 0 return to it with probability one half. -/
public theorem region_minorized :
    MinorizationOn kernel region 2 (NNReal.half NNReal.one) start := by
  refine ⟨kernel_markov, by decide, NNReal.half_positive NNReal.one_positive,
    NNReal.half_le NNReal.one, ?_⟩
  intro state member event measurable
  change state = 0 at member
  subst member
  rw [Measure.smul_apply_measurable _ _ measurable,
    show iterate kernel 2 0 event = iterate kernel (1 + 1) 0 event from rfl,
    iterate_succ_apply, lintegral_kernel_zero, iterate_one, kernel_one, kernel_two]
  change ENNReal.le
    (ENNReal.mul (ENNReal.half ENNReal.one) (Measure.dirac states 0 event))
    (ENNReal.mul (ENNReal.half ENNReal.one)
      (ENNReal.add (Measure.dirac states 0 event) (Measure.dirac states 2 event)))
  apply ENNReal.mul_le_mul_left _ _
  have grown := ENNReal.add_le_add_left
    (ENNReal.zero_le (Measure.dirac states 2 event)) (Measure.dirac states 0 event)
  rw [ENNReal.add_zero] at grown
  exact grown

private theorem absorbed_never_returns (count : Nat) :
    iterate kernel count 2 region = ENNReal.zero := by
  induction count with
  | zero =>
      rw [iterate_zero, Kernel.deterministic_apply]
      exact Measure.dirac_apply_of_not_mem _ _ (Space.discrete_measurable _)
        (by decide : ¬(2 : Fin 3) = 0)
  | succ count induction =>
      rw [iterate_succ_apply, kernel_two, lintegral_dirac _ _ (ENNRealMeasurable.from_discrete _)]
      exact induction

private theorem odd_never_returns (half : Nat) :
    iterate kernel (2 * half + 1) 0 region = ENNReal.zero ∧
      iterate kernel (2 * half) 1 region = ENNReal.zero := by
  induction half with
  | zero =>
      refine ⟨?_, ?_⟩
      · rw [Nat.mul_zero, iterate_succ_apply, lintegral_kernel_zero, iterate_zero,
          Kernel.deterministic_apply, Kernel.deterministic_apply,
          Measure.dirac_apply_of_not_mem _ _ (set := region)
            (Space.discrete_measurable _) (by decide : ¬(1 : Fin 3) = 0),
          Measure.dirac_apply_of_not_mem _ _ (set := region)
            (Space.discrete_measurable _) (by decide : ¬(2 : Fin 3) = 0),
          ENNReal.add_zero, ENNReal.mul_zero]
      · rw [Nat.mul_zero, iterate_zero, Kernel.deterministic_apply]
        exact Measure.dirac_apply_of_not_mem _ _ (Space.discrete_measurable _)
          (by decide : ¬(1 : Fin 3) = 0)
  | succ half induction =>
      have even : iterate kernel (2 * (half + 1)) 1 region = ENNReal.zero := by
        rw [show 2 * (half + 1) = (2 * half + 1) + 1 by omega, iterate_succ_apply,
          kernel_one, lintegral_dirac _ _ (ENNRealMeasurable.from_discrete _)]
        exact induction.1
      refine ⟨?_, even⟩
      rw [iterate_succ_apply, lintegral_kernel_zero, even,
        absorbed_never_returns, ENNReal.add_zero, ENNReal.mul_zero]

/-- No odd count is minorized on the region. -/
public theorem odd_not_minorized (half : Nat) :
    ¬MinorizedAt kernel region start (2 * half + 1) := by
  rintro ⟨weight, minor⟩
  have bound := minor.lower 0 rfl region (Space.discrete_measurable _)
  rw [Measure.smul_apply_measurable _ _ (set := region)
    (Space.discrete_measurable _), (odd_never_returns half).1] at bound
  change ENNReal.le (ENNReal.mul (ENNReal.finite weight)
    (Measure.dirac states 0 (Set.singleton 0))) ENNReal.zero at bound
  rw [Measure.dirac_apply_of_mem _ _ (set := region)
    (Space.discrete_measurable _) rfl, ENNReal.mul_one] at bound
  exact minor.weightPositive.2 bound

/-- Two divides every minorized count. -/
public theorem two_divides (count : Nat)
    (minorized : MinorizedAt kernel region start count) : 2 ∣ count := by
  rcases Nat.mod_two_eq_zero_or_one count with even | odd
  · exact Nat.dvd_of_mod_eq_zero even
  · have split : count = 2 * (count / 2) + 1 := by
      have := Nat.div_add_mod count 2
      omega
    rw [split] at minorized
    exact (odd_not_minorized (count / 2) minorized).elim

/-- No two disjoint cells carry mass at the absorbing state. -/
public theorem absorbed_aperiodic : MeasureAperiodic kernel absorbed.val := by
  intro period cell cycle
  apply Classical.byContradiction
  intro long
  have firstInside := mem_of_charged (cycle.positive 0 (by omega))
  have secondInside := mem_of_charged (cycle.positive 1 (by omega))
  exact cycle.disjoint 0 1 (by omega) (by omega) (by decide) 2 firstInside
    secondInside

/-- Every premise of `cycle_of_common_divisor` at divisor two holds except that
the invariant law charge the region, and no cycle of period two exists. -/
public theorem cycle_needs_charged_region :
    absorbed.val.bind kernel = absorbed.val ∧
      MeasureIrreducible kernel absorbed.val ∧
      absorbed.val region = ENNReal.zero ∧
      MinorizationOn kernel region 2 (NNReal.half NNReal.one) start ∧
      (∀ count, MinorizedAt kernel region start count → 2 ∣ count) ∧
      ¬∃ cell, MeasureCycle kernel absorbed.val 2 cell :=
  ⟨absorbed_invariant, absorbed_irreducible, absorbed_region, region_minorized,
    two_divides, fun ⟨cell, cycle⟩ =>
      absurd (absorbed_aperiodic 2 cell cycle) (by decide)⟩

/-- Every premise of `minorizedAt_eventually` holds except that the invariant
law charge the region, and no threshold bounds the minorized counts. -/
public theorem eventually_needs_charged_region :
    MeasureAperiodic kernel absorbed.val ∧
      ENNReal.lt ENNReal.zero (start.val region) ∧
      ¬∃ threshold, ∀ count, threshold ≤ count →
        MinorizedAt kernel region start count :=
  ⟨absorbed_aperiodic, start_region, fun ⟨threshold, large⟩ =>
    odd_not_minorized threshold (large (2 * threshold + 1) (by omega))⟩

end Iteration.Necessity.Transient

end Problib.Measure.Kernel
