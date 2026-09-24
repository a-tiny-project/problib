module

public import Problib.Inference.Invariance
public import Problib.Measure.Kernel.Density
public import Problib.Measure.Integral.Density.Change
public import Problib.Measure.Extended.Algebra.Binary
public import Problib.Measure.Extended.Algebra.Fixed
public import Problib.Measure.Kernel.Measurable
public import Problib.Measure.Uniform
public import Problib.Measure.Uniform.Band
public import Problib.Measure.Real.Order
public import Problib.Measure.Real.Arithmetic
public import Problib.Measure.Real.Interval
public import Problib.Measure.Extended.Conversion
set_option autoImplicit false

/-! Metropolis–Hastings kernels.

A Metropolis–Hastings step draws a proposal from a kernel `q` and then moves to
it with probability `accept (x, y)` or stays at `x`
(`mhKernel`, `lintegral_mh_kernel`). With acceptance at most one, every step is a
probability (`mh_kernel_markov`). One step's joint law from any measure is the
accepted proposals plus the rejected ones on the diagonal (`mh_joint`), so the
step is in detailed balance as soon as its accepted part is symmetric
(`mh_detailed_balance`). For a proposal reversible with respect to a reference
measure, a balanced acceptance `w(x)·a(x, y) = w(y)·a(y, x)` gives detailed
balance with the weighted reference (`mh_balanced_detailed_balance`).

The Metropolis acceptance is the uniform mass of `{u | u·c(x) < c(y)}` for a
real weight `c` (`metropolisAccept`). That is exactly the law of the test a
program runs on a uniform draw, so no division appears. It balances the
clamped weight (`metropolis_balance`), so the Metropolis step leaves the
weighted reference invariant (`metropolis_invariant`). A proposal that ignores
the current state is reversible for its own law (`independence_reversible`),
and under a weight bound `c ≤ M` the independence sampler minorizes its target
(`independence_minorization`): `π(A) ≤ M·K(x, A)` from every state `x`. -/

namespace Problib.Inference

open Problib.Real Problib.Measure

universe u

variable {α : Type u} {space : Space α}

public section

/-- From a proposed pair, move to the proposal with probability `accept`, and
otherwise stay. -/
@[expose] noncomputable def moveOrStay (accept : α × α → ENNReal)
    (acceptMeasurable : ENNRealMeasurable (Space.product space space) accept) :
    Kernel (Space.product space space) space :=
  Kernel.add
    ((Kernel.deterministic Prod.snd (Space.second_measurable space space)).withDensity
      (Kernel.IsSFinite.deterministic _ _) (fun pair _ => accept pair)
      (acceptMeasurable.comp (Space.first_measurable _ _)))
    ((Kernel.deterministic Prod.fst (Space.first_measurable space space)).withDensity
      (Kernel.IsSFinite.deterministic _ _) (fun pair _ => ENNReal.sub ENNReal.one (accept pair))
      ((ENNRealMeasurable.sub (ENNRealMeasurable.constant _ ENNReal.one) acceptMeasurable).comp
        (Space.first_measurable _ _)))

theorem lintegral_move_or_stay (accept : α × α → ENNReal)
    (acceptMeasurable : ENNRealMeasurable (Space.product space space) accept)
    (pair : α × α) {function : α → ENNReal} (functionMeasurable : ENNRealMeasurable space function) :
    lintegral (moveOrStay accept acceptMeasurable pair) function =
      ENNReal.add (ENNReal.mul (accept pair) (function pair.2))
        (ENNReal.mul (ENNReal.sub ENNReal.one (accept pair)) (function pair.1)) := by
  unfold moveOrStay
  rw [Kernel.add_apply, lintegral_add_measure, Kernel.withDensity_apply, Kernel.withDensity_apply,
    Kernel.deterministic_apply, Kernel.deterministic_apply,
    lintegral_withDensity _ (ENNRealMeasurable.constant _ _) functionMeasurable,
    lintegral_withDensity _ (ENNRealMeasurable.constant _ _) functionMeasurable,
    lintegral_dirac _ _ (ENNRealMeasurable.mul (ENNRealMeasurable.constant _ _) functionMeasurable),
    lintegral_dirac _ _ (ENNRealMeasurable.mul (ENNRealMeasurable.constant _ _) functionMeasurable)]

/-- Metropolis–Hastings: propose from `proposal`, then move or stay. -/
@[expose] noncomputable def mhKernel (proposal : Kernel space space) (proposalFinite : Kernel.IsSFinite proposal)
    (accept : α × α → ENNReal)
    (acceptMeasurable : ENNRealMeasurable (Space.product space space) accept) :
    Kernel space space :=
  (Kernel.attach proposal proposalFinite).comp (moveOrStay accept acceptMeasurable)

theorem lintegral_mh_kernel (proposal : Kernel space space)
    (proposalFinite : Kernel.IsSFinite proposal) (accept : α × α → ENNReal)
    (acceptMeasurable : ENNRealMeasurable (Space.product space space) accept)
    (state : α) {function : α → ENNReal} (functionMeasurable : ENNRealMeasurable space function) :
    lintegral (mhKernel proposal proposalFinite accept acceptMeasurable state) function =
      lintegral (proposal state) fun proposed =>
        ENNReal.add (ENNReal.mul (accept (state, proposed)) (function proposed))
          (ENNReal.mul (ENNReal.sub ENNReal.one (accept (state, proposed))) (function state)) := by
  unfold mhKernel
  rw [Kernel.comp_apply, Measure.lintegral_bind _ _ functionMeasurable, Kernel.attach_apply,
    lintegral_map]
  · apply lintegral_congr
    intro proposed
    exact lintegral_move_or_stay accept acceptMeasurable (state, proposed) functionMeasurable
  · exact Kernel.lintegral_measurable _ functionMeasurable

/-- With acceptance at most one, every step is a probability. -/
theorem mh_kernel_markov {proposal : Kernel space space} (proposalFinite : Kernel.IsSFinite proposal)
    (markov : ∀ state, Measure.IsProbability (proposal state)) {accept : α × α → ENNReal}
    (acceptMeasurable : ENNRealMeasurable (Space.product space space) accept)
    (atMostOne : ∀ pair, ENNReal.le (accept pair) ENNReal.one) (state : α) :
    Measure.IsProbability (mhKernel proposal proposalFinite accept acceptMeasurable state) := by
  constructor
  have total := lintegral_const (mhKernel proposal proposalFinite accept acceptMeasurable state)
    ENNReal.one
  rw [ENNReal.one_mul] at total
  rw [← total, lintegral_mh_kernel _ _ _ _ _ (ENNRealMeasurable.constant _ _)]
  calc
    lintegral (proposal state) (fun proposed =>
        ENNReal.add (ENNReal.mul (accept (state, proposed)) ENNReal.one)
          (ENNReal.mul (ENNReal.sub ENNReal.one (accept (state, proposed))) ENNReal.one)) =
        lintegral (proposal state) (fun _ => ENNReal.one) := by
      apply lintegral_congr
      intro proposed
      rw [ENNReal.mul_one, ENNReal.mul_one, ENNReal.add_comm,
        ENNReal.sub_add_cancel (atMostOne (state, proposed))]
    _ = ENNReal.one := by
      rw [lintegral_const, (markov state).univ_eq_one, ENNReal.one_mul]

/-- The first coordinate, repeated: a rejected proposal stays where it began. -/
@[expose] def repeatFirst (pair : α × α) : α × α := (pair.1, pair.1)

theorem repeatFirst_measurable :
    MeasurableMap (Space.product space space) (Space.product space space) repeatFirst :=
  Space.pair_measurable (Space.first_measurable space space) (Space.first_measurable space space)

/-- One step's joint law is the accepted proposals plus the rejected ones placed
on the diagonal. The rejected part carries `1 - accept` pointwise, so no mass is
ever subtracted from a total. -/
theorem mh_joint (target : Measure space) {proposal : Kernel space space}
    (proposalFinite : Kernel.IsSFinite proposal) {accept : α × α → ENNReal}
    (acceptMeasurable : ENNRealMeasurable (Space.product space space) accept)
    (stepFinite : Kernel.IsSFinite (mhKernel proposal proposalFinite accept acceptMeasurable)) :
    target.semiproduct (mhKernel proposal proposalFinite accept acceptMeasurable) stepFinite =
      Measure.add ((target.semiproduct proposal proposalFinite).withDensity accept)
        (((target.semiproduct proposal proposalFinite).withDensity
            (fun pair => ENNReal.sub ENNReal.one (accept pair))).map repeatFirst
          repeatFirst_measurable) := by
  apply Measure.ext
  intro set setMeasurable
  let indicator : α × α → ENNReal := ennrealIndicator set fun _ => ENNReal.one
  have indicatorMeasurable : ENNRealMeasurable (Space.product space space) indicator :=
    ENNRealMeasurable.indicator setMeasurable (ENNRealMeasurable.constant _ _)
  have rejectMeasurable : ENNRealMeasurable (Space.product space space)
      (fun pair => ENNReal.sub ENNReal.one (accept pair)) :=
    ENNRealMeasurable.sub (ENNRealMeasurable.constant _ _) acceptMeasurable
  have sectionMeasurable (state : α) :
      ENNRealMeasurable space (fun proposed => indicator (state, proposed)) :=
    indicatorMeasurable.comp (Kernel.pair_left_measurable state)
  rw [Measure.add_apply_measurable _ _ setMeasurable, apply_eq_lintegral_indicator _ setMeasurable,
    apply_eq_lintegral_indicator _ setMeasurable, apply_eq_lintegral_indicator _ setMeasurable,
    lintegral_semiproduct _ _ _ indicatorMeasurable,
    lintegral_withDensity _ acceptMeasurable indicatorMeasurable,
    lintegral_map _ _ _ indicatorMeasurable,
    lintegral_withDensity _ rejectMeasurable (indicatorMeasurable.comp repeatFirst_measurable),
    ← lintegral_add _ (ENNRealMeasurable.mul acceptMeasurable indicatorMeasurable)
      (ENNRealMeasurable.mul rejectMeasurable (indicatorMeasurable.comp repeatFirst_measurable)),
    lintegral_semiproduct _ _ _ (ENNRealMeasurable.add
      (ENNRealMeasurable.mul acceptMeasurable indicatorMeasurable)
      (ENNRealMeasurable.mul rejectMeasurable (indicatorMeasurable.comp repeatFirst_measurable)))]
  apply lintegral_congr
  intro state
  exact lintegral_mh_kernel proposal proposalFinite accept acceptMeasurable state
    (sectionMeasurable state)

/-- One Metropolis–Hastings step is s-finite: attaching an s-finite proposal
and then moving or staying. -/
@[expose] noncomputable def mhKernelSFinite {proposal : Kernel space space}
    (proposalFinite : Kernel.IsSFinite proposal) {accept : α × α → ENNReal}
    (acceptMeasurable : ENNRealMeasurable (Space.product space space) accept) :
    Kernel.IsSFinite (mhKernel proposal proposalFinite accept acceptMeasurable) :=
  Kernel.IsSFinite.comp (Kernel.IsSFinite.attach proposalFinite)
    (Kernel.IsSFinite.add
      (Kernel.IsSFinite.withDensity (Kernel.IsSFinite.deterministic _ _) _ _)
      (Kernel.IsSFinite.withDensity (Kernel.IsSFinite.deterministic _ _) _ _))

/-- The pair swapped. -/
@[expose] def swap (pair : α × α) : α × α := (pair.2, pair.1)

/-- A step is in detailed balance when its accepted part is symmetric. The
rejected part lies on the diagonal, which swapping fixes. -/
theorem mh_detailed_balance (target : Measure space) {proposal : Kernel space space}
    (proposalFinite : Kernel.IsSFinite proposal) {accept : α × α → ENNReal}
    (acceptMeasurable : ENNRealMeasurable (Space.product space space) accept)
    (symmetric : ((target.semiproduct proposal proposalFinite).withDensity accept).map swap
        (Space.swap_measurable space space) =
      (target.semiproduct proposal proposalFinite).withDensity accept) :
    DetailedBalance target (mhKernel proposal proposalFinite accept acceptMeasurable)
      (mhKernelSFinite proposalFinite acceptMeasurable) := by
  unfold DetailedBalance
  rw [mh_joint target proposalFinite acceptMeasurable, Measure.map_add]
  change Measure.add _ _ = _
  have swapped : ((target.semiproduct proposal proposalFinite).withDensity accept).map
      (fun pair : α × α => (pair.2, pair.1)) (Space.swap_measurable space space) =
      (target.semiproduct proposal proposalFinite).withDensity accept := symmetric
  rw [swapped, Measure.map_comp]
  rfl

/-- A symmetric density on a symmetric measure is symmetric. -/
theorem withDensity_swap (measure : Measure (Space.product space space))
    (symmetric : measure.map swap (Space.swap_measurable space space) = measure)
    {density : α × α → ENNReal}
    (densityMeasurable : ENNRealMeasurable (Space.product space space) density)
    (densitySymmetric : ∀ pair, density (swap pair) = density pair) :
    (measure.withDensity density).map swap (Space.swap_measurable space space) =
      measure.withDensity density := by
  apply Measure.ext
  intro set setMeasurable
  let indicator : α × α → ENNReal := ennrealIndicator set fun _ => ENNReal.one
  have indicatorMeasurable : ENNRealMeasurable (Space.product space space) indicator :=
    ENNRealMeasurable.indicator setMeasurable (ENNRealMeasurable.constant _ _)
  have productMeasurable := ENNRealMeasurable.mul densityMeasurable indicatorMeasurable
  have swappedMeasurable : ENNRealMeasurable (Space.product space space)
      (fun pair => indicator (swap pair)) :=
    indicatorMeasurable.comp (Space.swap_measurable _ _)
  rw [apply_eq_lintegral_indicator _ setMeasurable, apply_eq_lintegral_indicator _ setMeasurable,
    lintegral_map _ _ _ indicatorMeasurable,
    lintegral_withDensity _ densityMeasurable swappedMeasurable,
    lintegral_withDensity _ densityMeasurable indicatorMeasurable]
  calc
    lintegral measure (fun pair => ENNReal.mul (density pair) (indicator (swap pair))) =
        lintegral measure (fun pair => ENNReal.mul (density (swap pair)) (indicator (swap pair))) := by
      apply lintegral_congr
      intro pair
      rw [densitySymmetric]
    _ = lintegral (measure.map swap (Space.swap_measurable space space))
          (fun pair => ENNReal.mul (density pair) (indicator pair)) :=
      (lintegral_map _ _ _ productMeasurable).symm
    _ = _ := by rw [symmetric]

/-- Metropolis–Hastings with a proposal reversible for a reference measure: an
acceptance that balances the weight, `weight x · accept (x, y) = weight y ·
accept (y, x)`, puts the step in detailed balance with the weighted reference. -/
theorem mh_balanced_detailed_balance (reference : Measure space) {proposal : Kernel space space}
    (proposalFinite : Kernel.IsSFinite proposal)
    (reversible : DetailedBalance reference proposal proposalFinite)
    {weight : α → ENNReal} (weightMeasurable : ENNRealMeasurable space weight)
    {accept : α × α → ENNReal}
    (acceptMeasurable : ENNRealMeasurable (Space.product space space) accept)
    (balanced : ∀ pair, ENNReal.mul (weight pair.1) (accept pair) =
      ENNReal.mul (weight pair.2) (accept (swap pair))) :
    DetailedBalance (reference.withDensity weight)
      (mhKernel proposal proposalFinite accept acceptMeasurable)
      (mhKernelSFinite proposalFinite acceptMeasurable) := by
  refine mh_detailed_balance _ proposalFinite acceptMeasurable ?_
  rw [Measure.semiproduct_withDensity_left _ weightMeasurable,
    Measure.withDensity_withDensity _ (weightMeasurable.comp (Space.first_measurable _ _)) acceptMeasurable]
  exact withDensity_swap _ reversible
    (ENNRealMeasurable.mul (weightMeasurable.comp (Space.first_measurable _ _)) acceptMeasurable)
    (fun pair => (balanced pair).symm)

section Metropolis

open Problib.Real.Construction
open Problib.Measure.Real (Carrier uniform01 UnitInterval unitBorel borel unitInclusion
  unitInclusion_measurable uniform01_univ uniform01_isProbability uniform01_real_initial
  uniform01_real_initial_of_one_le measurable_lt measurable_mul not_lt_iff_le not_le_iff_lt
  ofReal_measurable ofReal_mul)

/-- The Metropolis test from `x` to a proposal `y` draws a uniform `u` and moves
when `u · c(x) < c(y)`. Its acceptance is the uniform mass of that event, so no
division appears and a state of weight zero accepts every move. -/
@[expose] noncomputable def metropolisAccept (weight : α → Carrier) (pair : α × α) : ENNReal :=
  uniform01 (fun u : UnitInterval =>
    Dedekind.lt (Dedekind.mul u.val (weight pair.1)) (weight pair.2))

/-- The acceptance of a measurable weight is jointly measurable in the pair: it
is the section mass of a measurable event under a constant finite kernel. -/
theorem metropolisAccept_measurable {weight : α → Carrier}
    (weightMeasurable : MeasurableMap space borel weight) :
    ENNRealMeasurable (Space.product space space) (metropolisAccept weight) := by
  have eventMeasurable : (Space.product (Space.product space space) unitBorel).Measurable
      (fun point : (α × α) × UnitInterval =>
        Dedekind.lt (Dedekind.mul point.2.val (weight point.1.1)) (weight point.1.2)) :=
    measurable_lt
      (measurable_mul (MeasurableMap.comp unitInclusion_measurable (Space.second_measurable _ _))
        (MeasurableMap.comp weightMeasurable
          (MeasurableMap.comp (Space.first_measurable _ _) (Space.first_measurable _ _))))
      (MeasurableMap.comp weightMeasurable
        (MeasurableMap.comp (Space.second_measurable _ _) (Space.first_measurable _ _)))
  exact Kernel.section_apply_measurable_of_finite_fibers
    (Kernel.const (Space.product space space) uniform01)
    (fun _ => uniform01_isProbability.to_finite) eventMeasurable

/-- An acceptance is a probability. -/
theorem metropolisAccept_le_one (weight : α → Carrier) (pair : α × α) :
    ENNReal.le (metropolisAccept weight pair) ENNReal.one := by
  have bound := uniform01.mono (Set.subset_univ
    (fun u : UnitInterval =>
      Dedekind.lt (Dedekind.mul u.val (weight pair.1)) (weight pair.2)))
  rw [uniform01_univ] at bound
  exact bound

/-- At a positive current weight the Metropolis event is an initial interval. -/
theorem metropolis_event {scale bound : Carrier} (positive : Dedekind.lt Dedekind.zero scale) :
    (fun u : UnitInterval => Dedekind.lt (Dedekind.mul u.val scale) bound) =
      (fun u : UnitInterval =>
        Dedekind.lt u.val (Dedekind.mul bound (Dedekind.inverse scale))) := by
  have nonzero : scale ≠ Dedekind.zero := fun equal =>
    Dedekind.lt_irrefl _ (equal ▸ positive)
  apply Set.ext
  intro u
  constructor
  · intro less
    have scaled := Dedekind.mul_lt_mul_positive_right less (Dedekind.inverse_of_positive_positive positive)
    rwa [Dedekind.mul_assoc, Dedekind.mul_inverse_cancel_of_positive positive, Dedekind.mul_one]
      at scaled
  · intro less
    have scaled := Dedekind.mul_lt_mul_positive_right less positive
    rwa [Dedekind.mul_assoc, Dedekind.inverse_mul_cancel nonzero, Dedekind.mul_one] at scaled

/-- The Metropolis acceptance balances the clamped weights: the weighted flow
from `x` to `y` is the smaller of the two weights, whichever way it runs. -/
theorem metropolis_balance (weight : α → Carrier) (pair : α × α) :
    ENNReal.mul (ENNReal.ofReal (weight pair.1)) (metropolisAccept weight pair) =
      ENNReal.min (ENNReal.ofReal (weight pair.1)) (ENNReal.ofReal (weight pair.2)) := by
  by_cases positive : Dedekind.lt Dedekind.zero (weight pair.1)
  · have inverseNonnegative := (Dedekind.inverse_of_positive_positive positive).1
    have nonzero : weight pair.1 ≠ Dedekind.zero := fun equal =>
      Dedekind.lt_irrefl _ (equal ▸ positive)
    unfold metropolisAccept
    rw [metropolis_event positive]
    by_cases below : Dedekind.le (weight pair.1) (weight pair.2)
    · have atLeastOne : Dedekind.le Dedekind.one
          (Dedekind.mul (weight pair.2) (Dedekind.inverse (weight pair.1))) := by
        have scaled := Dedekind.mul_le_mul_nonnegative_right below inverseNonnegative
        rwa [Dedekind.mul_inverse_cancel_of_positive positive] at scaled
      rw [uniform01_real_initial_of_one_le _ atLeastOne, ENNReal.mul_one,
        ENNReal.min_eq_left (ENNReal.ofReal_monotone below)]
    · have above := not_le_iff_lt.mp below
      have atMostOne : Dedekind.le
          (Dedekind.mul (weight pair.2) (Dedekind.inverse (weight pair.1))) Dedekind.one := by
        have scaled := Dedekind.mul_le_mul_nonnegative_right above.1 inverseNonnegative
        rwa [Dedekind.mul_inverse_cancel_of_positive positive] at scaled
      rw [uniform01_real_initial _ atMostOne,
        ENNReal.min_eq_right (ENNReal.ofReal_monotone above.1)]
      by_cases nonnegative : Dedekind.le Dedekind.zero (weight pair.2)
      · rw [← ofReal_mul positive.1 (Dedekind.mul_nonnegative nonnegative inverseNonnegative),
          Dedekind.mul_comm (weight pair.1), Dedekind.mul_assoc, Dedekind.inverse_mul_cancel nonzero,
          Dedekind.mul_one]
      · have negative : ¬Dedekind.le Dedekind.zero
            (Dedekind.mul (weight pair.2) (Dedekind.inverse (weight pair.1))) := by
          intro scaledNonnegative
          have back := Dedekind.mul_nonnegative scaledNonnegative positive.1
          rw [Dedekind.mul_assoc, Dedekind.inverse_mul_cancel nonzero, Dedekind.mul_one] at back
          exact nonnegative back
        rw [ENNReal.ofReal_of_not_nonnegative negative, ENNReal.ofReal_of_not_nonnegative nonnegative,
          ENNReal.mul_zero]
  · have zero : ENNReal.ofReal (weight pair.1) = ENNReal.zero :=
      ENNReal.ofReal_eq_zero_iff.mpr (not_lt_iff_le.mp positive)
    rw [zero, ENNReal.zero_mul, ENNReal.min_eq_left (ENNReal.zero_le _)]


/-- The Metropolis step on a weighted reference: with a proposal reversible for
`reference`, the step is in detailed balance with `reference` weighted by the
clamped weight. -/
theorem metropolis_detailed_balance (reference : Measure space) {proposal : Kernel space space}
    (proposalFinite : Kernel.IsSFinite proposal)
    (reversible : DetailedBalance reference proposal proposalFinite)
    {weight : α → Carrier} (weightMeasurable : MeasurableMap space borel weight) :
    DetailedBalance (reference.withDensity fun state => ENNReal.ofReal (weight state))
      (mhKernel proposal proposalFinite (metropolisAccept weight)
        (metropolisAccept_measurable weightMeasurable))
      (mhKernelSFinite proposalFinite (metropolisAccept_measurable weightMeasurable)) := by
  refine mh_balanced_detailed_balance reference proposalFinite reversible
    (ENNRealMeasurable.comp ofReal_measurable weightMeasurable) _ ?_
  intro pair
  have reversed : ENNReal.mul (ENNReal.ofReal (weight pair.2)) (metropolisAccept weight (swap pair)) =
      ENNReal.min (ENNReal.ofReal (weight pair.2)) (ENNReal.ofReal (weight pair.1)) :=
    metropolis_balance weight (swap pair)
  rw [metropolis_balance weight pair, reversed]
  rcases ENNReal.le_total (ENNReal.ofReal (weight pair.1)) (ENNReal.ofReal (weight pair.2))
    with below | above
  · rw [ENNReal.min_eq_left below, ENNReal.min_eq_right below]
  · rw [ENNReal.min_eq_right above, ENNReal.min_eq_left above]

/-- A Markov proposal reversible for `reference` makes the Metropolis step leave
the weighted reference invariant. -/
theorem metropolis_invariant (reference : Measure space) {proposal : Kernel space space}
    (proposalFinite : Kernel.IsSFinite proposal)
    (markov : ∀ state, Measure.IsProbability (proposal state))
    (reversible : DetailedBalance reference proposal proposalFinite)
    {weight : α → Carrier} (weightMeasurable : MeasurableMap space borel weight) :
    KernelInvariant (reference.withDensity fun state => ENNReal.ofReal (weight state))
      (mhKernel proposal proposalFinite (metropolisAccept weight)
        (metropolisAccept_measurable weightMeasurable)) :=
  detailed_balance_invariant
    (mh_kernel_markov proposalFinite markov _ (metropolisAccept_le_one weight))
    (metropolis_detailed_balance reference proposalFinite reversible weightMeasurable)

/-- A proposal that ignores the current state is reversible for the law it draws
from. Only s-finiteness is needed. -/
theorem independence_reversible (prior : Measure space) (priorFinite : Measure.SFinite prior) :
    DetailedBalance prior (Kernel.const space prior) (Kernel.IsSFinite.const space priorFinite) :=
  Measure.prod_swap priorFinite priorFinite

/-- A move toward a weight at least the current one is always accepted. -/
theorem metropolisAccept_eq_one {weight : α → Carrier} {pair : α × α}
    (below : Dedekind.le (weight pair.1) (weight pair.2))
    (positive : Dedekind.lt Dedekind.zero (weight pair.2)) :
    metropolisAccept weight pair = ENNReal.one := by
  unfold metropolisAccept
  by_cases currentPositive : Dedekind.lt Dedekind.zero (weight pair.1)
  · rw [metropolis_event currentPositive]
    apply uniform01_real_initial_of_one_le
    have scaled := Dedekind.mul_le_mul_nonnegative_right below
      (Dedekind.inverse_of_positive_positive currentPositive).1
    rwa [Dedekind.mul_inverse_cancel_of_positive currentPositive] at scaled
  · have full : (fun u : UnitInterval =>
        Dedekind.lt (Dedekind.mul u.val (weight pair.1)) (weight pair.2)) = Set.univ := by
      apply Set.ext
      intro u
      refine ⟨fun _ => trivial, fun _ => Dedekind.lt_of_le_of_lt ?_ positive⟩
      have scaled := Dedekind.mul_le_mul_nonnegative_right (not_lt_iff_le.mp currentPositive) u.property.1
      rwa [Dedekind.zero_mul, Dedekind.mul_comm] at scaled
    rw [full, uniform01_univ]

/-- Under a weight bound `c ≤ M`, a move is accepted with probability at least
`c(y) / M`, stated without division. -/
theorem metropolisAccept_bound {weight : α → Carrier} {bound : Carrier}
    (bounded : ∀ state, Dedekind.le (weight state) bound) (pair : α × α) :
    ENNReal.le (ENNReal.ofReal (weight pair.2))
      (ENNReal.mul (ENNReal.ofReal bound) (metropolisAccept weight pair)) := by
  by_cases positive : Dedekind.lt Dedekind.zero (weight pair.2)
  · by_cases below : Dedekind.le (weight pair.1) (weight pair.2)
    · rw [metropolisAccept_eq_one below positive, ENNReal.mul_one]
      exact ENNReal.ofReal_monotone (bounded pair.2)
    · have above := not_le_iff_lt.mp below
      have balance := metropolis_balance weight pair
      rw [ENNReal.min_eq_right (ENNReal.ofReal_monotone above.1)] at balance
      rw [← balance]
      exact ENNReal.mul_le_mul_right (ENNReal.ofReal_monotone (bounded pair.1)) _
  · rw [ENNReal.ofReal_eq_zero_iff.mpr (not_lt_iff_le.mp positive)]
    exact ENNReal.zero_le _

/-- The independence sampler with a weight bounded by `M` minorizes its target:
from every state, `M` times one step's mass of a set is at least the target's
unnormalized mass of it. So each step forgets the start with probability at
least `Z / M`. -/
theorem independence_minorization (prior : Measure space) (priorFinite : Measure.SFinite prior)
    {weight : α → Carrier} (weightMeasurable : MeasurableMap space borel weight)
    {bound : Carrier} (bounded : ∀ state, Dedekind.le (weight state) bound)
    (state : α) {set : Set α} (setMeasurable : space.Measurable set) :
    ENNReal.le ((prior.withDensity fun proposed => ENNReal.ofReal (weight proposed)) set)
      (ENNReal.mul (ENNReal.ofReal bound)
        (mhKernel (Kernel.const space prior) (Kernel.IsSFinite.const space priorFinite)
          (metropolisAccept weight) (metropolisAccept_measurable weightMeasurable) state set)) := by
  let indicator : α → ENNReal := ennrealIndicator set fun _ => ENNReal.one
  have indicatorMeasurable : ENNRealMeasurable space indicator :=
    ENNRealMeasurable.indicator setMeasurable (ENNRealMeasurable.constant _ _)
  have acceptedMeasurable : ENNRealMeasurable space
      (fun proposed => ENNReal.mul (metropolisAccept weight (state, proposed)) (indicator proposed)) :=
    ENNRealMeasurable.mul
      ((metropolisAccept_measurable weightMeasurable).comp (Kernel.pair_left_measurable state))
      indicatorMeasurable
  rw [Measure.withDensity_apply _ _ setMeasurable, ← lintegral_indicator prior set setMeasurable,
    apply_eq_lintegral_indicator _ setMeasurable, lintegral_mh_kernel _ _ _ _ _ indicatorMeasurable,
    Kernel.const_apply]
  refine ENNReal.le_trans (lintegral_mono prior (upper := fun proposed =>
      ENNReal.mul (ENNReal.ofReal bound)
        (ENNReal.mul (metropolisAccept weight (state, proposed)) (indicator proposed))) ?_) ?_
  · intro proposed
    classical
    by_cases member : set proposed
    · simp only [indicator, ennrealIndicator, ennrealPiecewise, member, if_true, ENNReal.mul_one]
      exact metropolisAccept_bound bounded (state, proposed)
    · simp only [ennrealIndicator, ennrealPiecewise, member, if_false]
      exact ENNReal.zero_le _
  · rw [lintegral_smul prior _ acceptedMeasurable]
    apply ENNReal.mul_le_mul_left _ (ENNReal.ofReal bound)
    apply lintegral_mono
    intro proposed
    have kept := ENNReal.add_le_add_left (ENNReal.zero_le
      (ENNReal.mul (ENNReal.sub ENNReal.one (metropolisAccept weight (state, proposed)))
        (indicator state)))
      (ENNReal.mul (metropolisAccept weight (state, proposed)) (indicator proposed))
    rwa [ENNReal.add_zero] at kept

end Metropolis

end

end Problib.Inference
