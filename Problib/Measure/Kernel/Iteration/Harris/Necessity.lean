module

public import Problib.Measure.Kernel.Iteration.Harris
public import Problib.Real.Extended.Approximation
import Problib.Measure.Integral.Lebesgue.Transport

set_option autoImplicit false

/-!
# A positive Harris chain that does not converge

The convergence theorem `harris_aperiodic_converges` asks for measure
aperiodicity. On the two booleans, `kernel` swaps the state at every step. The
fair law `uniform` is invariant, and from either state the chain enters every
event the fair law charges within one step, so the chain is positive Harris
(`uniform_positiveHarris`). The cells {false} and {true} form a measurable cycle
of period two (`not_measureAperiodic`). From a unit mass the law after every
step is again a unit mass, at total variation one half from the fair law
(`iterate_totalVariation`), so the chain does not converge
(`not_converges`). Aperiodicity is the one premise it fails.
-/

namespace Problib.Measure.Kernel

open Problib.Real

namespace Iteration.Necessity.Flip

/-- The two booleans. Every set is measurable. -/
public abbrev bits : Space Bool := Space.discrete Bool

private theorem swap_measurable : MeasurableMap bits bits not :=
  fun _ => Space.discrete_measurable _

/-- Swap the state at every step. -/
public noncomputable def kernel : Kernel bits bits :=
  Kernel.deterministic not swap_measurable

/-- Half the mass on each state. -/
public noncomputable def fair : Measure bits :=
  Measure.smul (ENNReal.half ENNReal.one)
    (Measure.add (Measure.dirac bits true) (Measure.dirac bits false))

private theorem lintegral_fair (function : Bool → ENNReal) :
    lintegral fair function =
      ENNReal.mul (ENNReal.half ENNReal.one)
        (ENNReal.add (function true) (function false)) := by
  rw [fair, lintegral_smul_measure, lintegral_add_measure,
    lintegral_dirac _ _ (ENNRealMeasurable.from_discrete _),
    lintegral_dirac _ _ (ENNRealMeasurable.from_discrete _)]

private theorem fair_probability : Measure.IsProbability fair := by
  constructor
  have total := lintegral_fair (fun _ => ENNReal.one)
  rw [lintegral_const, ENNReal.one_mul, ENNReal.mul_add, ENNReal.mul_one,
    ENNReal.half_add_half] at total
  exact total

/-- The fair law on the two booleans. -/
public noncomputable def uniform : Giry.Law bits := ⟨fair, fair_probability⟩

/-- The unit mass at one state. -/
public noncomputable def unit (point : Bool) : Giry.Law bits :=
  ⟨Measure.dirac bits point, Measure.IsProbability.dirac _ _⟩

public theorem kernel_markov (state : Bool) : Measure.IsProbability (kernel state) :=
  ⟨Measure.dirac_apply_univ _ _⟩

private theorem kernel_apply (state : Bool) : kernel state = Measure.dirac bits (!state) :=
  Kernel.deterministic_apply not swap_measurable state

private theorem fair_apply (event : Set Bool) :
    fair event = ENNReal.mul (ENNReal.half ENNReal.one)
      (ENNReal.add (Measure.dirac bits true event) (Measure.dirac bits false event)) := by
  rw [fair, Measure.smul_apply_measurable _ _ (Space.discrete_measurable _),
    Measure.add_apply_measurable _ _ (Space.discrete_measurable _)]

/-- The fair law is invariant. -/
public theorem uniform_invariant : uniform.val.bind kernel = uniform.val := by
  apply Measure.ext
  intro event measurable
  change fair.bind kernel event = fair event
  rw [Measure.bind_apply _ _ measurable, lintegral_fair, kernel_apply, kernel_apply,
    fair_apply]
  change ENNReal.mul _ (ENNReal.add (Measure.dirac bits false event)
    (Measure.dirac bits true event)) = _
  rw [ENNReal.add_comm]

private theorem fair_member {event : Set Bool}
    (charged : ENNReal.lt ENNReal.zero (fair event)) :
    ∃ point, event point := Measure.exists_mem_of_positive fair charged

/-- The swap is positive Harris for the fair law: an event the fair law charges
holds a state, and the chain is at that state now or after one step. -/
public theorem uniform_positiveHarris : PositiveHarris kernel uniform := by
  refine ⟨kernel_markov, uniform_invariant, ?_⟩
  intro event measurable positive input
  rcases fair_member positive with ⟨point, member⟩
  by_cases inside : event input
  · exact hitsAlmostSurely_of_mem _ _ _ measurable inside
  have swapped : event (!input) := by
    cases input <;> cases point <;> first | exact member | exact False.elim (inside member)
  refine ⟨measurable, ?_⟩
  rcases hitsAlmostSurely_of_mem kernel event (!input) measurable swapped with
    ⟨_, next⟩
  rw [hit_mass_step kernel event measurable inside, kernel_apply,
    lintegral_dirac _ _ (ENNRealMeasurable.from_discrete _)]
  exact next

private theorem fair_split (point : Bool) (event : Set Bool) :
    fair event = ENNReal.mul (ENNReal.half ENNReal.one)
      (ENNReal.add (Measure.dirac bits point event) (Measure.dirac bits (!point) event)) := by
  rw [fair_apply]
  cases point
  · rw [ENNReal.add_comm]
    rfl
  · rfl

private theorem half_positive : ENNReal.lt ENNReal.zero (ENNReal.half ENNReal.one) :=
  ENNReal.half_positive ENNReal.one_positive

private theorem other_outside (point : Bool) : ¬Set.singleton point (!point) := by
  intro equal
  cases point <;> cases equal

private theorem singleton_fair (point : Bool) :
    fair (Set.singleton point) = ENNReal.half ENNReal.one := by
  rw [fair_split point,
    Measure.dirac_apply_of_mem _ _ (Space.discrete_measurable _)
      (show Set.singleton point point from rfl),
    Measure.dirac_apply_of_not_mem _ _ (Space.discrete_measurable _) (other_outside point),
    ENNReal.add_zero, ENNReal.mul_one]

/-- The cell of each residue: false at 0, true after. -/
private def cell (index : Nat) : Set Bool := Set.singleton (index != 0)

private theorem swap_cycle : MeasureCycle kernel uniform.val 2 cell := by
  refine ⟨fun _ _ => Space.discrete_measurable _, ?_, fun index _ => ?_, ?_⟩
  · intro first second firstSmall secondSmall different value inFirst inSecond
    change value = (first != 0) at inFirst
    change value = (second != 0) at inSecond
    have same : (first != 0) = (second != 0) := inFirst.symm.trans inSecond
    have firstCases : first = 0 ∨ first = 1 := by omega
    have secondCases : second = 0 ∨ second = 1 := by omega
    rcases firstCases with rfl | rfl <;> rcases secondCases with rfl | rfl <;>
      first | exact different rfl | exact absurd same (by decide)
  · change ENNReal.lt ENNReal.zero (fair (Set.singleton (index != 0)))
    rw [singleton_fair]
    exact half_positive
  · intro index small input member
    change input = (index != 0) at member
    rw [kernel_apply]
    apply Measure.dirac_apply_of_mem _ _ (Space.discrete_measurable _)
    change (!input) = ((index + 1) % 2 != 0)
    have indexCases : index = 0 ∨ index = 1 := by omega
    rcases indexCases with rfl | rfl <;> subst member <;> decide

/-- The swap has a measurable cycle of period two, so it is not aperiodic. -/
public theorem not_measureAperiodic : ¬MeasureAperiodic kernel uniform.val :=
  fun aperiodic => absurd (aperiodic 2 cell swap_cycle) (by decide)

/-- The swap does not converge from every start. -/
public theorem not_converges : ¬ConvergesFromEveryLaw kernel uniform :=
  fun converges => not_measureAperiodic (measureAperiodic_of_converges converges)

/-- The state after some number of swaps. -/
private def turn : Nat → Bool → Bool
  | 0, state => state
  | count + 1, state => turn count (!state)

private theorem iterate_apply (count : Nat) (state : Bool) :
    iterate kernel count state = Measure.dirac bits (turn count state) := by
  induction count generalizing state with
  | zero => rw [iterate_zero, Kernel.deterministic_apply]; rfl
  | succ count induction =>
      rw [iterate_succ, Kernel.comp_apply, kernel_apply, Measure.dirac_bind, induction]
      rfl

private theorem one_sub_half :
    ENNReal.sub ENNReal.one (ENNReal.half ENNReal.one) = ENNReal.half ENNReal.one := by
  calc ENNReal.sub ENNReal.one (ENNReal.half ENNReal.one)
      = ENNReal.sub (ENNReal.add (ENNReal.half ENNReal.one) (ENNReal.half ENNReal.one))
          (ENNReal.half ENNReal.one) := by rw [ENNReal.half_add_half]
    _ = ENNReal.half ENNReal.one :=
      ENNReal.add_sub_cancel_right ((ENNReal.half_finite (value := ENNReal.one)).mpr True.intro)

private theorem half_le_fair {point : Bool} {event : Set Bool} (member : event point) :
    ENNReal.le (ENNReal.half ENNReal.one) (fair event) := by
  rw [fair_split point, Measure.dirac_apply_of_mem _ _ (Space.discrete_measurable _) member]
  have lower := ENNReal.mul_le_mul_left
    (ENNReal.le_self_add ENNReal.one (Measure.dirac bits (!point) event))
    (ENNReal.half ENNReal.one)
  rw [ENNReal.mul_one] at lower
  exact lower

private theorem fair_le_half {point : Bool} {event : Set Bool} (outside : ¬event point) :
    ENNReal.le (fair event) (ENNReal.half ENNReal.one) := by
  rw [fair_split point,
    Measure.dirac_apply_of_not_mem _ _ (Space.discrete_measurable _) outside, ENNReal.zero_add]
  have upper := ENNReal.mul_le_mul_left
    ((Measure.IsProbability.dirac bits (!point)).apply_le_one event)
    (ENNReal.half ENNReal.one)
  rw [ENNReal.mul_one] at upper
  exact upper

/-- A unit mass lies at total variation one half from the fair law. -/
private theorem unit_totalVariation (point : Bool) :
    Giry.Law.totalVariation (unit point) uniform = ENNReal.half ENNReal.one := by
  apply ENNReal.le_antisymm
  · apply ENNReal.supremum_le
    rintro distance ⟨event, measurable, rfl⟩
    change ENNReal.le (ENNReal.max
      (ENNReal.sub (Measure.dirac bits point event) (fair event))
      (ENNReal.sub (fair event) (Measure.dirac bits point event))) _
    by_cases member : event point
    · rw [Measure.dirac_apply_of_mem _ _ measurable member,
        ENNReal.sub_eq_zero_iff_le.mpr (fair_probability.apply_le_one event)]
      apply ENNReal.max_le _ (ENNReal.zero_le _)
      rw [← one_sub_half]
      exact ENNReal.sub_le_sub_left (half_le_fair member) ENNReal.one
    · rw [Measure.dirac_apply_of_not_mem _ _ measurable member, ENNReal.zero_sub,
        ENNReal.sub_zero]
      exact ENNReal.max_le (ENNReal.zero_le _) (fair_le_half member)
  · have lower := Giry.Law.event_sub_le (unit point) uniform
      (Space.discrete_measurable (Set.singleton point))
    change ENNReal.le (ENNReal.sub (Measure.dirac bits point (Set.singleton point))
      (fair (Set.singleton point))) _ at lower
    rw [Measure.dirac_apply_of_mem _ _ (Space.discrete_measurable _)
      (show Set.singleton point point from rfl), singleton_fair,
      one_sub_half] at lower
    exact lower

/-- From a unit mass, the law after every number of swaps lies at total
variation one half from the fair law. -/
public theorem iterate_totalVariation (point : Bool) (count : Nat) :
    Giry.Law.totalVariation (iterateLaw kernel kernel_markov (unit point) count) uniform =
      ENNReal.half ENNReal.one := by
  have same : iterateLaw kernel kernel_markov (unit point) count = unit (turn count point) := by
    apply Subtype.ext
    change (Measure.dirac bits point).bind (iterate kernel count) =
      Measure.dirac bits (turn count point)
    rw [Measure.dirac_bind, iterate_apply]
  rw [same, unit_totalVariation]

end Iteration.Necessity.Flip

end Problib.Measure.Kernel
