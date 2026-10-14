module

public import Problib.Measure.Kernel.Iteration.Aperiodicity
public import Problib.Measure.Kernel.Iteration.Minorization
public import Problib.Measure.Kernel.TotalVariation
public import Problib.Analysis.Real.Sequence
import Problib.Measure.Integral.Lebesgue.Algebra
import Problib.Measure.Integral.Lebesgue.AlmostEverywhere
import Problib.Measure.Integral.Lebesgue.Transport
import Problib.Measure.Integral.Lebesgue.Zero
import Problib.Measure.Integral.Lebesgue.Measure

set_option autoImplicit false

namespace Problib.Measure.Kernel

open Problib.Real

universe u
variable {α : Type u} {space : Space α}

private theorem toReal_add_finite {left right : ENNReal}
    (leftFinite : ENNReal.Finite left) (rightFinite : ENNReal.Finite right) :
    ENNReal.toReal (ENNReal.add left right) =
      Problib.Real.Construction.Dedekind.add
        (ENNReal.toReal left) (ENNReal.toReal right) := by
  rcases ENNReal.exists_finite_of_finite leftFinite with ⟨leftValue, rfl⟩
  rcases ENNReal.exists_finite_of_finite rightFinite with ⟨rightValue, rfl⟩
  exact NNReal.toReal_add leftValue rightValue

public structure ConvergesFromEveryLaw (kernel : Kernel space space)
    (law : Giry.Law space) : Prop where
  markov : ∀ input, Measure.IsProbability (kernel input)
  converges : ∀ start : Giry.Law space,
    Problib.Analysis.Real.ConvergesTo
      (fun count => ENNReal.toReal (Giry.Law.totalVariation
        (iterateLaw kernel markov start count) law))
      Problib.Real.Construction.Dedekind.zero

public theorem ConvergesFromEveryLaw.invariant
    {kernel : Kernel space space} {law : Giry.Law space}
    (converges : ConvergesFromEveryLaw kernel law) :
    law.val.bind kernel = law.val := by
  let next : Giry.Law space :=
    ⟨law.val.bind kernel, law.property.bind kernel converges.markov⟩
  have original := converges.converges law
  have one (start : Giry.Law space) :
      iterateLaw kernel converges.markov start 1 =
        ⟨start.val.bind kernel,
          start.property.bind kernel converges.markov⟩ := by
    apply Subtype.ext
    change start.val.bind (iterate kernel 1) = start.val.bind kernel
    have once : iterate kernel 1 = kernel := by
      rw [iterate_succ, iterate_zero, comp_deterministic]
      apply Kernel.ext
      intro input
      rw [map_apply, Measure.map_id]
    rw [once]
  have forward (count : Nat) :
      iterateLaw kernel converges.markov law (count + 1) =
        ⟨(iterateLaw kernel converges.markov law count).val.bind kernel,
          (iterateLaw kernel converges.markov law count).property.bind
            kernel converges.markov⟩ := by
    rw [iterateLaw_add, one]
  have distanceBound (count : Nat) : ENNReal.le
      (Giry.Law.totalVariation next law)
      (ENNReal.add
        (Giry.Law.totalVariation
          (iterateLaw kernel converges.markov law count) law)
        (Giry.Law.totalVariation
          (iterateLaw kernel converges.markov law (count + 1)) law)) := by
    have triangle := Giry.Law.totalVariation_triangle next
      (iterateLaw kernel converges.markov law (count + 1)) law
    have contraction := totalVariation_bind kernel converges.markov law
      (iterateLaw kernel converges.markov law count)
    change ENNReal.le
      (Giry.Law.totalVariation next
        ⟨(iterateLaw kernel converges.markov law count).val.bind kernel,
          (iterateLaw kernel converges.markov law count).property.bind
            kernel converges.markov⟩)
      (Giry.Law.totalVariation law
        (iterateLaw kernel converges.markov law count)) at contraction
    rw [← forward count,
      Giry.Law.totalVariation_symm law
        (iterateLaw kernel converges.markov law count)] at contraction
    exact ENNReal.le_trans triangle
      (ENNReal.add_le_add_right contraction _)
  have distanceFinite : ENNReal.Finite
      (Giry.Law.totalVariation next law) :=
    ENNReal.finite_of_le (Giry.Law.totalVariation_le_one next law) True.intro
  have realNonpositive : Problib.Real.Construction.Dedekind.le
      (ENNReal.toReal (Giry.Law.totalVariation next law))
      Problib.Real.Construction.Dedekind.zero := by
    apply Problib.Analysis.Real.le_of_forall_lt_add
    intro epsilon positive
    have halfPositive := Problib.Analysis.Real.half_positive positive
    rcases original _ halfPositive with ⟨stage, close⟩
    have firstClose := close stage (Nat.le_refl stage)
    have secondClose := close (stage + 1) (Nat.le_succ stage)
    rw [Problib.Real.Construction.Dedekind.sub_zero,
      Problib.Analysis.Real.abs_of_nonnegative
        (ENNReal.toReal_nonnegative _)] at firstClose secondClose
    have firstFinite : ENNReal.Finite
        (Giry.Law.totalVariation
          (iterateLaw kernel converges.markov law stage) law) :=
      ENNReal.finite_of_le (Giry.Law.totalVariation_le_one _ _) True.intro
    have secondFinite : ENNReal.Finite
        (Giry.Law.totalVariation
          (iterateLaw kernel converges.markov law (stage + 1)) law) :=
      ENNReal.finite_of_le (Giry.Law.totalVariation_le_one _ _) True.intro
    have realBound := (ENNReal.toReal_le_toReal_iff distanceFinite
      (ENNReal.add_finite firstFinite secondFinite)).mpr
        (distanceBound stage)
    rw [toReal_add_finite firstFinite secondFinite] at realBound
    have small := Problib.Real.Construction.Dedekind.add_lt_add
      firstClose secondClose
    rw [Problib.Analysis.Real.add_half] at small
    rw [Problib.Real.Construction.Dedekind.zero_add]
    exact Problib.Real.Construction.Dedekind.lt_of_le_of_lt
      realBound small
  have zeroReal := Problib.Real.Construction.Dedekind.le_antisymm
    realNonpositive (ENNReal.toReal_nonnegative _)
  have zeroTV : Giry.Law.totalVariation next law = ENNReal.zero := by
    apply ENNReal.le_antisymm
    · apply (ENNReal.toReal_le_toReal_iff distanceFinite
        (show ENNReal.Finite ENNReal.zero from True.intro)).mp
      simpa only [ENNReal.toReal_zero] using
        Problib.Real.Construction.Dedekind.le_of_equal zeroReal
    · exact ENNReal.zero_le _
  have same := (Giry.Law.totalVariation_eq_zero_iff next law).mp zeroTV
  exact congrArg Subtype.val same

public theorem ConvergesFromEveryLaw.invariant_unique
    {kernel : Kernel space space} {law : Giry.Law space}
    (converges : ConvergesFromEveryLaw kernel law) (other : Giry.Law space)
    (invariant : other.val.bind kernel = other.val) : other = law := by
  have stationary : ∀ count,
      iterateLaw kernel converges.markov other count = other :=
    iterateLaw_invariant kernel converges.markov other invariant
  have limit := converges.converges other
  have constant : Problib.Analysis.Real.ConvergesTo
      (fun _ : Nat => ENNReal.toReal (Giry.Law.totalVariation other law))
      Problib.Real.Construction.Dedekind.zero := by
    simpa only [stationary] using limit
  have zeroReal : ENNReal.toReal (Giry.Law.totalVariation other law) =
      Problib.Real.Construction.Dedekind.zero := by
    apply Classical.byContradiction
    intro nonzero
    have nonnegative := ENNReal.toReal_nonnegative
      (Giry.Law.totalVariation other law)
    have positive : Problib.Real.Construction.Dedekind.lt
        Problib.Real.Construction.Dedekind.zero
        (ENNReal.toReal (Giry.Law.totalVariation other law)) :=
      ⟨nonnegative, fun reverse => nonzero
        (Problib.Real.Construction.Dedekind.le_antisymm
          nonnegative reverse).symm⟩
    rcases constant _ positive with ⟨stage, close⟩
    have near := close stage (Nat.le_refl stage)
    rw [Problib.Real.Construction.Dedekind.sub_zero,
      Problib.Analysis.Real.abs_of_nonnegative nonnegative] at near
    exact Problib.Real.Construction.Dedekind.lt_irrefl _ near
  have finite : ENNReal.Finite (Giry.Law.totalVariation other law) :=
    ENNReal.finite_of_le (Giry.Law.totalVariation_le_one other law) True.intro
  have zeroTV : Giry.Law.totalVariation other law = ENNReal.zero := by
    apply ENNReal.le_antisymm
    · apply (ENNReal.toReal_le_toReal_iff finite
        (show ENNReal.Finite ENNReal.zero from True.intro)).mp
      simpa only [ENNReal.toReal_zero] using
        Problib.Real.Construction.Dedekind.le_of_equal zeroReal
    · exact ENNReal.zero_le _
  exact (Giry.Law.totalVariation_eq_zero_iff other law).mp zeroTV

/-- Any every-start TV limit forbids a positive measurable cycle. -/
public theorem measureAperiodic_of_converges
    {kernel : Kernel space space} {law : Giry.Law space}
    (converges : ConvergesFromEveryLaw kernel law) :
    MeasureAperiodic kernel law.val := by
  intro period cell cycle
  apply Classical.byContradiction
  intro tooLong
  have periodAtLeastTwo : 2 ≤ period := by omega
  have zeroRange : 0 < period := by omega
  have oneRange : 1 < period := by omega
  have zeroPositive := cycle.positive 0 zeroRange
  have onePositive := cycle.positive 1 oneRange
  have zeroMember : ∃ value, cell 0 value := by
    apply Classical.byContradiction
    intro empty
    have null : law.val (cell 0) = ENNReal.zero := by
      have same : cell 0 = Set.empty := by
        funext value
        apply propext
        constructor
        · intro member
          exact False.elim (empty ⟨value, member⟩)
        · intro member
          exact False.elim member
      rw [same]
      exact law.val.empty_apply
    exact (ENNReal.zero_lt_iff_ne_zero.mp zeroPositive) null
  rcases zeroMember with ⟨start, startInZero⟩
  let initial : Giry.Law space :=
    ⟨Measure.dirac space start, Measure.IsProbability.dirac space start⟩
  have alongCycles : ∀ blocks,
      iterate kernel (blocks * period) start (cell 0) = ENNReal.one := by
    intro blocks
    have advanced := cycle.iterate_advance converges.markov
      0 zeroRange start startInZero (blocks * period)
    have modZero : (blocks * period) % period = 0 := by
      rw [Nat.mul_comm blocks period, Nat.mul_mod_right]
    simpa only [Nat.zero_add, modZero] using advanced
  let gap := ENNReal.sub ENNReal.one (law.val (cell 0))
  have gapPositive : ENNReal.lt ENNReal.zero gap := by
    have complementPositive : ENNReal.lt ENNReal.zero
        (law.val (Set.complement (cell 0))) := by
      have included : Set.Subset (cell 1)
          (Set.complement (cell 0)) := by
        intro value memberOne memberZero
        exact cycle.disjoint 0 1 zeroRange oneRange (by omega)
          value memberZero memberOne
      have bound := law.val.mono included
      exact ⟨ENNReal.le_trans onePositive.1 bound,
        fun reverse => onePositive.2 (ENNReal.le_trans bound reverse)⟩
    change ENNReal.lt ENNReal.zero
      (ENNReal.sub ENNReal.one (law.val (cell 0)))
    rw [← law.property.apply_complement (cycle.measurable 0 zeroRange)]
    exact complementPositive
  have tvBound : ∀ blocks,
      ENNReal.le gap
        (Giry.Law.totalVariation
          (iterateLaw kernel converges.markov initial (blocks * period)) law) := by
    intro blocks
    have eventBound := Giry.Law.event_sub_le
      (iterateLaw kernel converges.markov initial (blocks * period))
      law (cycle.measurable 0 zeroRange)
    have eventMass : (iterateLaw kernel converges.markov initial
        (blocks * period)).val (cell 0) = ENNReal.one := by
      change ((Measure.dirac space start).bind
        (iterate kernel (blocks * period))) (cell 0) = ENNReal.one
      rw [Measure.dirac_bind]
      exact alongCycles blocks
    rw [eventMass] at eventBound
    exact eventBound
  have gapFinite : ENNReal.Finite gap :=
    ENNReal.finite_of_le (ENNReal.sub_le_self _ _)
      (show ENNReal.Finite ENNReal.one from True.intro)
  have realGapPositive : Problib.Real.Construction.Dedekind.lt
      Problib.Real.Construction.Dedekind.zero (ENNReal.toReal gap) := by
    rw [← ENNReal.toReal_zero]
    exact (ENNReal.toReal_lt_toReal_iff
      (show ENNReal.Finite ENNReal.zero from True.intro)
      gapFinite).mpr gapPositive
  rcases converges.converges initial (ENNReal.toReal gap) realGapPositive with
    ⟨stage, close⟩
  let blocks := stage
  have later : stage ≤ blocks * period := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left stage
      (show 1 ≤ period by omega)
  have near := close (blocks * period) later
  have lowerReal : Problib.Real.Construction.Dedekind.le
      (ENNReal.toReal gap)
      (ENNReal.toReal (Giry.Law.totalVariation
        (iterateLaw kernel converges.markov initial (blocks * period)) law)) := by
    exact (ENNReal.toReal_le_toReal_iff gapFinite
      (ENNReal.finite_of_le
        (Giry.Law.totalVariation_le_one _ _)
        (show ENNReal.Finite ENNReal.one from True.intro))).mpr
      (tvBound blocks)
  have realSmall : Problib.Real.Construction.Dedekind.lt
      (ENNReal.toReal (Giry.Law.totalVariation
        (iterateLaw kernel converges.markov initial (blocks * period)) law))
      (ENNReal.toReal gap) := by
    simpa only [Problib.Real.Construction.Dedekind.sub_zero,
      Problib.Analysis.Real.abs_of_nonnegative
        (ENNReal.toReal_nonnegative _)] using near
  exact False.elim (Problib.Real.Construction.Dedekind.lt_irrefl _
    (Problib.Real.Construction.Dedekind.lt_of_le_of_lt
      lowerReal realSmall))

public theorem minorization_convergesFromEveryLaw
    {kernel : Kernel space space} {steps : Nat} {weight : NNReal}
    {reference : Giry.Law space}
    (minor : Minorization kernel steps weight reference)
    (law : Giry.Law space) (invariant : law.val.bind kernel = law.val) :
    ConvergesFromEveryLaw kernel law := by
  refine ⟨minor.markov, ?_⟩
  intro start
  exact minorization_converges minor law start invariant

section Coupling

variable {kernel : Kernel space space} {region : Set α}
  {weight : NNReal} {reference : Giry.Law space}

/-- The uncoupled mass from a start, averaged over an invariant partner. -/
@[expose] public noncomputable def couplingEnvelope
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region)
    (law : Giry.Law space) (count : Nat) (input : α) : ENNReal :=
  lintegral law.val (fun other =>
    uncoupledMass minor measurable count (input, other))

/-- Total variation to the invariant law has a measurable upper envelope whose
infimum vanishes almost everywhere. -/
public structure ConvergesAlmostEverywhere (kernel : Kernel space space)
    (law : Giry.Law space) : Prop where
  markov : ∀ input, Measure.IsProbability (kernel input)
  envelope : ∃ bound : Nat → α → ENNReal,
    (∀ count, ENNRealMeasurable space (bound count)) ∧
    (∀ count input, ENNReal.le
      (Giry.Law.totalVariation
        ⟨iterate kernel count input,
          iterate_isProbability kernel markov count input⟩ law)
      (bound count input)) ∧
    law.val.AE (fun input =>
      ENNReal.iInf (fun count => bound count input) = ENNReal.zero)

private theorem uncoupledMass_section_measurable
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) (count : Nat) (input : α) :
    ENNRealMeasurable space (fun other =>
      uncoupledMass minor measurable count (input, other)) :=
  ENNRealMeasurable.comp
    ((iterate (uncoupledKernel minor measurable) count).measurable
      (Space.product space space).univ)
    (Space.pair_measurable (MeasurableMap.constant space space input)
      (MeasurableMap.identity space))

public theorem couplingEnvelope_measurable
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region)
    (law : Giry.Law space) (count : Nat) :
    ENNRealMeasurable space (couplingEnvelope minor measurable law count) :=
  lintegral_measurable_joint (Kernel.const space law.val)
    (Kernel.IsSFinite.const space
      (Measure.SFinite.ofFinite law.property.to_finite))
    (function := fun input other =>
      uncoupledMass minor measurable count (input, other))
    ((iterate (uncoupledKernel minor measurable) count).measurable
      (Space.product space space).univ)

public theorem couplingEnvelope_bounds_tv
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region)
    (law : Giry.Law space) (invariant : law.val.bind kernel = law.val)
    (count : Nat) (input : α) :
    ENNReal.le
      (Giry.Law.totalVariation
        ⟨iterate kernel count input,
          iterate_isProbability kernel minor.markov count input⟩ law)
      (couplingEnvelope minor measurable law count input) := by
  let start : Giry.Law space :=
    ⟨iterate kernel count input, iterate_isProbability kernel minor.markov count input⟩
  have lawEqual : (⟨law.val.bind (iterate kernel count),
      law.property.bind _ (iterate_isProbability kernel minor.markov count)⟩ :
        Giry.Law space) = law :=
    Subtype.ext (invariant_iterate kernel law invariant count)
  have pointwise : ∀ other, ENNReal.le
      (Giry.Law.totalVariation
        ⟨iterate kernel count other,
          iterate_isProbability kernel minor.markov count other⟩ start)
      (uncoupledMass minor measurable count (input, other)) := by
    intro other
    rw [Giry.Law.totalVariation_symm,
      ← iterate_couplingKernel_inl minor measurable count (input, other)]
    exact coupling_totalVariation_le minor measurable count (Sum.inl (input, other))
  have bound := Giry.Law.totalVariation_bind_le law (iterate kernel count)
    (iterate_isProbability kernel minor.markov count) start
  rw [lawEqual] at bound
  rw [Giry.Law.totalVariation_symm]
  exact ENNReal.le_trans bound (lintegral_mono law.val pointwise)

/-- A one-step small set charged by its minorant and reached from almost every
invariant start gives total-variation convergence almost everywhere. -/
public theorem strong_small_set_converges_ae
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region)
    (selfCharge : ENNReal.lt ENNReal.zero (reference.val region))
    (law : Giry.Law space) (invariant : law.val.bind kernel = law.val)
    (reach : law.val.AE (fun input =>
      ∃ count, ENNReal.lt ENNReal.zero (iterate kernel count input region))) :
    ConvergesAlmostEverywhere kernel law := by
  refine ⟨minor.markov, couplingEnvelope minor measurable law,
    couplingEnvelope_measurable minor measurable law,
    couplingEnvelope_bounds_tv minor measurable law invariant, ?_⟩
  let limit := fun pair : α × α =>
    ENNReal.iInf (fun count => uncoupledMass minor measurable count pair)
  have limitMeasurable : ENNRealMeasurable (Space.product space space) limit :=
    ENNRealMeasurable.iInf (fun count =>
      (iterate (uncoupledKernel minor measurable) count).measurable
        (Space.product space space).univ)
  have vanishes := uncoupledMass_vanishes minor measurable selfCharge law
    invariant reach
  have pairIntegral : lintegral (Measure.prod law.val law.val
      (Measure.SFinite.ofFinite law.property.to_finite)) limit = ENNReal.zero :=
    (lintegral_eq_zero_iff limitMeasurable).mpr vanishes
  rw [lintegral_prod _ _ _ limitMeasurable] at pairIntegral
  have inner := (lintegral_eq_zero_iff
    (lintegral_measurable_joint (Kernel.const space law.val)
      (Kernel.IsSFinite.const space
        (Measure.SFinite.ofFinite law.property.to_finite))
      (function := fun input other => limit (input, other))
      limitMeasurable)).mp pairIntegral
  apply inner.mono
  intro input zero
  have exchange := lintegral_iInf law.val
    (fun count other => uncoupledMass minor measurable count (input, other))
    (fun count => uncoupledMass_section_measurable minor measurable count input)
    (fun count other => uncoupledMass_antitone minor measurable
      (Nat.le_succ count) (input, other))
    ⟨0, by
      change ENNReal.Finite (lintegral law.val (fun other =>
        uncoupledMass minor measurable 0 (input, other)))
      rw [lintegral_congr _ (fun other => uncoupledMass_zero minor measurable
        (input, other)), lintegral_const, ENNReal.one_mul,
        law.property.univ_eq_one]
      exact True.intro⟩
  change ENNReal.iInf (fun count => lintegral law.val (fun other =>
    uncoupledMass minor measurable count (input, other))) = ENNReal.zero
  rw [← exchange]
  exact zero

end Coupling

section EveryStart

variable {kernel : Kernel space space}

/-- The running minimum of an envelope, capped at one. -/
private noncomputable def runningEnvelope (bound : Nat → α → ENNReal) :
    Nat → α → ENNReal
  | 0 => fun input => ENNReal.min ENNReal.one (bound 0 input)
  | count + 1 => fun input =>
      ENNReal.min (runningEnvelope bound count input) (bound (count + 1) input)

private theorem runningEnvelope_measurable {bound : Nat → α → ENNReal}
    (measurable : ∀ count, ENNRealMeasurable space (bound count)) :
    ∀ count, ENNRealMeasurable space (runningEnvelope bound count)
  | 0 => ENNRealMeasurable.min (ENNRealMeasurable.constant space ENNReal.one)
      (measurable 0)
  | count + 1 => ENNRealMeasurable.min
      (runningEnvelope_measurable measurable count) (measurable (count + 1))

private theorem runningEnvelope_le_bound (bound : Nat → α → ENNReal)
    (input : α) : ∀ count,
    ENNReal.le (runningEnvelope bound count input) (bound count input)
  | 0 => ENNReal.min_le_right _ _
  | _ + 1 => ENNReal.min_le_right _ _

private theorem runningEnvelope_le_one (bound : Nat → α → ENNReal)
    (input : α) : ∀ count,
    ENNReal.le (runningEnvelope bound count input) ENNReal.one
  | 0 => ENNReal.min_le_left _ _
  | count + 1 => ENNReal.le_trans (ENNReal.min_le_left _ _)
      (runningEnvelope_le_one bound input count)

private theorem runningEnvelope_antitone (bound : Nat → α → ENNReal)
    (input : α) {first second : Nat} (included : first ≤ second) :
    ENNReal.le (runningEnvelope bound second input)
      (runningEnvelope bound first input) := by
  induction included with
  | refl => exact ENNReal.le_refl _
  | step _ induction =>
      exact ENNReal.le_trans (ENNReal.min_le_left _ _) induction

/-- One more step never increases the distance from a point to an invariant
law. -/
private theorem point_totalVariation_succ_le
    (markov : ∀ input, Measure.IsProbability (kernel input))
    (law : Giry.Law space) (invariant : law.val.bind kernel = law.val)
    (count : Nat) (input : α) :
    ENNReal.le
      (Giry.Law.totalVariation
        ⟨iterate kernel (count + 1) input,
          iterate_isProbability kernel markov (count + 1) input⟩ law)
      (Giry.Law.totalVariation
        ⟨iterate kernel count input,
          iterate_isProbability kernel markov count input⟩ law) := by
  have contraction : ENNReal.le
      (Giry.Law.totalVariation
        ⟨(iterate kernel count input).bind kernel,
          (iterate_isProbability kernel markov count input).bind kernel markov⟩
        ⟨law.val.bind kernel, law.property.bind kernel markov⟩)
      (Giry.Law.totalVariation
        ⟨iterate kernel count input,
          iterate_isProbability kernel markov count input⟩ law) :=
    totalVariation_bind kernel markov
      ⟨iterate kernel count input, iterate_isProbability kernel markov count input⟩ law
  have next : (⟨(iterate kernel count input).bind kernel,
      (iterate_isProbability kernel markov count input).bind kernel markov⟩ :
        Giry.Law space) =
      ⟨iterate kernel (count + 1) input,
        iterate_isProbability kernel markov (count + 1) input⟩ :=
    Subtype.ext (by
      change (iterate kernel count input).bind kernel =
        iterate kernel (count + 1) input
      rw [iterate_succ_right, Kernel.comp_apply])
  have fixed : (⟨law.val.bind kernel, law.property.bind kernel markov⟩ :
      Giry.Law space) = law := Subtype.ext invariant
  rw [next, fixed] at contraction
  exact contraction

private theorem runningEnvelope_bounds_tv
    (markov : ∀ input, Measure.IsProbability (kernel input))
    (law : Giry.Law space) (invariant : law.val.bind kernel = law.val)
    {bound : Nat → α → ENNReal}
    (bounds : ∀ count input, ENNReal.le
      (Giry.Law.totalVariation
        ⟨iterate kernel count input,
          iterate_isProbability kernel markov count input⟩ law)
      (bound count input)) (input : α) :
    ∀ count, ENNReal.le
      (Giry.Law.totalVariation
        ⟨iterate kernel count input,
          iterate_isProbability kernel markov count input⟩ law)
      (runningEnvelope bound count input)
  | 0 => ENNReal.le_min (Giry.Law.totalVariation_le_one _ _) (bounds 0 input)
  | count + 1 => ENNReal.le_min
      (ENNReal.le_trans
        (point_totalVariation_succ_le markov law invariant count input)
        (runningEnvelope_bounds_tv markov law invariant bounds input count))
      (bounds (count + 1) input)

/-- The law of the first entrance to an event within `count` steps. -/
private noncomputable def entranceBy (kernel : Kernel space space)
    (event : Set α) (measurable : space.Measurable event) :
    Nat → Kernel space space
  | 0 => Kernel.zero space space
  | count + 1 => Kernel.add (exitInside event measurable)
      ((continueOutside kernel event measurable).comp
        (entranceBy kernel event measurable count))

private theorem entranceBy_le_hitKernel (kernel : Kernel space space)
    (event : Set α) (measurable : space.Measurable event) :
    ∀ count input set, space.Measurable set →
      ENNReal.le (entranceBy kernel event measurable count input set)
        (hitKernel kernel event measurable input set)
  | 0, input, set, _ => by
      rw [entranceBy, Kernel.zero_apply, Measure.zero_apply]
      exact ENNReal.zero_le _
  | count + 1, input, set, setMeasurable => by
      rw [entranceBy, Kernel.add_apply, Measure.add_apply_measurable _ _ setMeasurable]
      conv => rhs; rw [hitKernel_unfold]
      rw [Kernel.add_apply, Measure.add_apply_measurable _ _ setMeasurable,
        comp_apply_measurable _ _ _ setMeasurable,
        comp_apply_measurable _ _ _ setMeasurable]
      exact ENNReal.add_le_add (ENNReal.le_refl _)
        (lintegral_mono _ (fun state =>
          entranceBy_le_hitKernel kernel event measurable count state set
            setMeasurable))

/-- Peeling first entrances: the distance at time `n + N` is at most the
running envelope averaged over entrances before `N`, plus the chance of no
entrance before `N`. -/
private theorem entrance_bound
    (markov : ∀ input, Measure.IsProbability (kernel input))
    (law : Giry.Law space) (invariant : law.val.bind kernel = law.val)
    {bound : Nat → α → ENNReal}
    (measurable : ∀ count, ENNRealMeasurable space (bound count))
    (bounds : ∀ count input, ENNReal.le
      (Giry.Law.totalVariation
        ⟨iterate kernel count input,
          iterate_isProbability kernel markov count input⟩ law)
      (bound count input))
    (event : Set α) (eventMeasurable : space.Measurable event) (count : Nat) :
    ∀ horizon input, ENNReal.le
      (Giry.Law.totalVariation
        ⟨iterate kernel (count + horizon) input,
          iterate_isProbability kernel markov (count + horizon) input⟩ law)
      (ENNReal.add
        (lintegral (entranceBy kernel event eventMeasurable horizon input)
          (runningEnvelope bound count))
        (survival kernel event eventMeasurable horizon input)) := by
  have envelopeMeasurable := runningEnvelope_measurable measurable count
  intro horizon
  induction horizon with
  | zero =>
      intro input
      rw [survival, iterate_zero, Kernel.deterministic_apply,
        Measure.dirac_apply_univ]
      have below := ENNReal.add_le_add_right
        (ENNReal.zero_le (lintegral (entranceBy kernel event eventMeasurable 0 input)
          (runningEnvelope bound count))) ENNReal.one
      rw [ENNReal.zero_add] at below
      exact ENNReal.le_trans (Giry.Law.totalVariation_le_one _ _) below
  | succ horizon induction =>
      intro input
      by_cases member : event input
      · have entrance : ENNReal.le (runningEnvelope bound count input)
            (lintegral (entranceBy kernel event eventMeasurable (horizon + 1) input)
              (runningEnvelope bound count)) := by
          rw [entranceBy, Kernel.add_apply, lintegral_add_measure, exitInside,
            piecewise_apply_of_mem _ _ _ _ _ member, Kernel.deterministic_apply,
            lintegral_dirac _ _ envelopeMeasurable]
          have below := ENNReal.add_le_add_left (ENNReal.zero_le
            (lintegral (((continueOutside kernel event eventMeasurable).comp
              (entranceBy kernel event eventMeasurable horizon)) input)
              (runningEnvelope bound count))) (runningEnvelope bound count input)
          rw [ENNReal.add_zero] at below
          exact below
        have extra := ENNReal.add_le_add_right (ENNReal.le_refl
          (lintegral (entranceBy kernel event eventMeasurable (horizon + 1) input)
            (runningEnvelope bound count)))
          (survival kernel event eventMeasurable (horizon + 1) input)
        have withSurvival := ENNReal.add_le_add_left (ENNReal.zero_le
          (survival kernel event eventMeasurable (horizon + 1) input))
          (lintegral (entranceBy kernel event eventMeasurable (horizon + 1) input)
            (runningEnvelope bound count))
        rw [ENNReal.add_zero] at withSurvival
        exact ENNReal.le_trans
          (runningEnvelope_bounds_tv markov law invariant bounds input _)
          (ENNReal.le_trans
            (runningEnvelope_antitone bound input (Nat.le_add_right count _))
            (ENNReal.le_trans entrance withSurvival))
      · have mix : ENNReal.le
            (Giry.Law.totalVariation
              ⟨iterate kernel (count + (horizon + 1)) input,
                iterate_isProbability kernel markov (count + (horizon + 1)) input⟩
              law)
            (lintegral (kernel input) (fun state =>
              Giry.Law.totalVariation
                ⟨iterate kernel (count + horizon) state,
                  iterate_isProbability kernel markov (count + horizon) state⟩
                law)) :=
          Giry.Law.totalVariation_bind_le ⟨kernel input, markov input⟩
            (iterate kernel (count + horizon))
            (iterate_isProbability kernel markov (count + horizon)) law
        have entrance : lintegral
            (entranceBy kernel event eventMeasurable (horizon + 1) input)
            (runningEnvelope bound count) =
              lintegral (kernel input) (fun state =>
                lintegral (entranceBy kernel event eventMeasurable horizon state)
                  (runningEnvelope bound count)) := by
          rw [entranceBy, Kernel.add_apply, lintegral_add_measure, exitInside,
            piecewise_apply_of_not_mem _ _ _ _ _ member, Kernel.zero_apply,
            lintegral_zero_measure, ENNReal.zero_add, Kernel.comp_apply,
            Measure.lintegral_bind _ _ envelopeMeasurable, continueOutside,
            piecewise_apply_of_not_mem _ _ _ _ _ member]
        have next := survival_succ kernel event eventMeasurable horizon input
        rw [continueOutside, piecewise_apply_of_not_mem _ _ _ _ _ member] at next
        have survivalMeasurable : ENNRealMeasurable space
            (survival kernel event eventMeasurable horizon) :=
          (iterate (continueOutside kernel event eventMeasurable) horizon).measurable
            space.univ
        rw [entrance, next, ← lintegral_add _
          ((entranceBy kernel event eventMeasurable horizon).lintegral_measurable
            envelopeMeasurable) survivalMeasurable]
        exact ENNReal.le_trans mix (lintegral_mono _ (fun state => induction state))

/-- Positive Harris recurrence carries almost-everywhere convergence to every
initial law. -/
public theorem converges_of_harris_and_ae {law : Giry.Law space}
    (harris : PositiveHarris kernel law)
    (ae : ConvergesAlmostEverywhere kernel law) :
    ConvergesFromEveryLaw kernel law := by
  classical
  rcases ae.envelope with ⟨bound, measurable, bounds, vanishes⟩
  have markov := harris.markov
  let envelope := runningEnvelope bound
  have envelopeMeasurable := runningEnvelope_measurable measurable
  let good : Set α := fun input =>
    ENNReal.iInf (fun count => envelope count input) = ENNReal.zero
  have infimumMeasurable : ENNRealMeasurable space (fun input =>
      ENNReal.iInf (fun count => envelope count input)) :=
    ENNRealMeasurable.iInf envelopeMeasurable
  have goodMeasurable : space.Measurable good :=
    ENNRealMeasurable.singleton infimumMeasurable ENNReal.zero
  have goodAE : law.val.AE good := vanishes.mono (fun input zero => by
    apply ENNReal.eq_zero_of_le_zero
    rw [← zero]
    exact ENNReal.le_iInf (fun count => ENNReal.le_trans
      (ENNReal.iInf_le _ count) (runningEnvelope_le_bound bound input count)))
  have goodPositive : ENNReal.lt ENNReal.zero (law.val good) := by
    apply ENNReal.zero_lt_iff_ne_zero.mpr
    intro goodNull
    have whole := (Measure.NullSet.union (measure := law.val) goodNull goodAE).mono
      (left := Set.univ) (fun {value} _ => by
        by_cases member : good value
        · exact Or.inl member
        · exact Or.inr member)
    have one := law.property.univ_eq_one
    rw [show law.val Set.univ = ENNReal.zero from whole] at one
    exact ENNReal.one_ne_zero one.symm
  have hits : ∀ input, hitKernel kernel good goodMeasurable input Set.univ =
      ENNReal.one := fun input => by
    rcases harris.harris good goodMeasurable goodPositive input with ⟨_, certain⟩
    exact certain
  refine ⟨markov, fun start => ?_⟩
  let entered := start.val.bind (hitKernel kernel good goodMeasurable)
  let distance := fun count => Giry.Law.totalVariation
    (iterateLaw kernel markov start count) law
  let entranceTerm := fun count => lintegral entered (envelope count)
  let survivalTerm := fun horizon =>
    lintegral start.val (survival kernel good goodMeasurable horizon)
  have split : ∀ count horizon, ENNReal.le (distance (count + horizon))
      (ENNReal.add (entranceTerm count) (survivalTerm horizon)) := by
    intro count horizon
    have mix := Giry.Law.totalVariation_bind_le start
      (iterate kernel (count + horizon))
      (iterate_isProbability kernel markov (count + horizon)) law
    have peel := lintegral_mono start.val (entrance_bound markov law harris.invariant
      measurable bounds good goodMeasurable count horizon)
    have widen := lintegral_mono start.val (fun input => ENNReal.add_le_add_right
      (lintegral_mono_measure (envelope count)
        (entranceBy kernel good goodMeasurable horizon input)
        (hitKernel kernel good goodMeasurable input)
        (entranceBy_le_hitKernel kernel good goodMeasurable horizon input))
      (survival kernel good goodMeasurable horizon input))
    have survivalMeasurable : ENNRealMeasurable space
        (survival kernel good goodMeasurable horizon) :=
      (iterate (continueOutside kernel good goodMeasurable) horizon).measurable
        space.univ
    rw [lintegral_add _
      ((hitKernel kernel good goodMeasurable).lintegral_measurable
        (envelopeMeasurable count)) survivalMeasurable,
      ← Measure.lintegral_bind _ _ (envelopeMeasurable count)] at widen
    exact ENNReal.le_trans mix (ENNReal.le_trans peel widen)
  have enteredMass : entered Set.univ = ENNReal.one := by
    change start.val.bind (hitKernel kernel good goodMeasurable) Set.univ = ENNReal.one
    rw [Measure.bind_apply _ _ space.univ, lintegral_congr _ hits, lintegral_const,
      ENNReal.one_mul, start.property.univ_eq_one]
  have entranceVanishes : ENNReal.iInf entranceTerm = ENNReal.zero := by
    have exchange := lintegral_iInf entered envelope envelopeMeasurable
      (fun count input => ENNReal.min_le_left _ _)
      ⟨0, by
        have below := lintegral_mono entered
          (fun input => runningEnvelope_le_one bound input 0)
        rw [lintegral_const, enteredMass, ENNReal.one_mul] at below
        exact ENNReal.finite_of_le below True.intro⟩
    change ENNReal.iInf (fun count => lintegral entered (envelope count)) = ENNReal.zero
    rw [← exchange]
    apply (lintegral_eq_zero_iff infimumMeasurable).mpr
    change entered (Set.complement good) = ENNReal.zero
    change start.val.bind (hitKernel kernel good goodMeasurable)
      (Set.complement good) = ENNReal.zero
    rw [Measure.bind_apply _ _ (space.complement goodMeasurable),
      lintegral_congr _ (hitKernel_concentrated kernel good goodMeasurable),
      lintegral_zero]
  have survivalVanishes : ENNReal.iInf survivalTerm = ENNReal.zero := by
    let T := continueOutside kernel good goodMeasurable
    have Tbound : ∀ state, ENNReal.le (T state Set.univ) ENNReal.one := by
      intro state
      have balance := hitting_conservative kernel good goodMeasurable markov state
      have below := ENNReal.add_le_add_left
        (ENNReal.zero_le (exitInside good goodMeasurable state Set.univ))
        (T state Set.univ)
      rw [ENNReal.add_zero, balance] at below
      exact below
    have exchange := lintegral_iInf start.val
      (fun horizon => survival kernel good goodMeasurable horizon)
      (fun horizon => (iterate T horizon).measurable space.univ)
      (fun horizon input => iterate_mass_antitone T Tbound (Nat.le_succ horizon) input)
      ⟨0, by
        have initial : ∀ state, survival kernel good goodMeasurable 0 state =
            ENNReal.one := by
          intro state
          rw [survival, iterate_zero, Kernel.deterministic_apply,
            Measure.dirac_apply_univ]
        rw [lintegral_congr _ initial, lintegral_const, ENNReal.one_mul,
          start.property.univ_eq_one]
        exact True.intro⟩
    change ENNReal.iInf (fun horizon => lintegral start.val
      (survival kernel good goodMeasurable horizon)) = ENNReal.zero
    rw [← exchange, lintegral_congr _ (fun input =>
      (hit_mass_eq_one_iff_survival_vanishes kernel good goodMeasurable markov
        input).mp (hits input)), lintegral_zero]
  have distanceVanishes : ENNReal.iInf distance = ENNReal.zero := by
    have bySurvival : ∀ horizon,
        ENNReal.le (ENNReal.iInf distance) (survivalTerm horizon) := by
      intro horizon
      have difference : ENNReal.le
          (ENNReal.sub (ENNReal.iInf distance) (survivalTerm horizon))
          ENNReal.zero := by
        rw [← entranceVanishes]
        apply ENNReal.le_iInf
        intro count
        apply ENNReal.sub_le_iff_le_add.mpr
        exact ENNReal.le_trans (ENNReal.iInf_le distance (count + horizon))
          (split count horizon)
      exact ENNReal.sub_eq_zero_iff_le.mp (ENNReal.eq_zero_of_le_zero difference)
    apply ENNReal.eq_zero_of_le_zero
    rw [← survivalVanishes]
    exact ENNReal.le_iInf bySurvival
  have distanceAntitone : ∀ {first second : Nat}, first ≤ second →
      ENNReal.le (distance second) (distance first) := by
    intro first second included
    induction included with
    | refl => exact ENNReal.le_refl _
    | @step later _ induction =>
        apply ENNReal.le_trans _ induction
        have contraction := totalVariation_bind kernel markov
          (iterateLaw kernel markov start later) law
        have next : (⟨(iterateLaw kernel markov start later).val.bind kernel,
            (iterateLaw kernel markov start later).property.bind kernel markov⟩ :
              Giry.Law space) = iterateLaw kernel markov start (later + 1) :=
          Subtype.ext (by
            change (start.val.bind (iterate kernel later)).bind kernel =
              start.val.bind (iterate kernel (later + 1))
            rw [iterate_succ_right, Measure.bind_assoc])
        have fixed : (⟨law.val.bind kernel, law.property.bind kernel markov⟩ :
            Giry.Law space) = law := Subtype.ext harris.invariant
        rw [next, fixed] at contraction
        exact contraction
  open Problib.Real.Construction.Dedekind in
    intro tolerance tolerancePositive
  have toleranceNonnegative :=
    Problib.Real.Construction.Dedekind.le_of_lt tolerancePositive
  let threshold := ENNReal.ofReal tolerance
  have thresholdPositive : ENNReal.lt ENNReal.zero threshold := by
    rw [← ENNReal.ofReal_zero]
    exact (ENNReal.ofReal_lt_ofReal_iff
      (Problib.Real.Construction.Dedekind.le_refl _)
      toleranceNonnegative).mpr tolerancePositive
  rw [← distanceVanishes] at thresholdPositive
  rcases ENNReal.exists_less_of_infimum_lt thresholdPositive with
    ⟨value, ⟨stage, rfl⟩, small⟩
  refine ⟨stage, fun index later => ?_⟩
  have tvSmall : ENNReal.lt (distance index) threshold :=
    ⟨ENNReal.le_trans (distanceAntitone later) small.left,
      fun reverse => small.right
        (ENNReal.le_trans reverse (distanceAntitone later))⟩
  have tvFinite : ENNReal.Finite (distance index) :=
    ENNReal.finite_of_le (Giry.Law.totalVariation_le_one _ _) True.intro
  have realSmall := (ENNReal.toReal_lt_toReal_iff tvFinite
    (ENNReal.ofReal_finite tolerance)).mpr tvSmall
  rw [ENNReal.toReal_ofReal toleranceNonnegative] at realSmall
  change Problib.Real.Construction.Dedekind.lt
    (Problib.Analysis.Real.abs
      (Problib.Real.Construction.Dedekind.sub
        (ENNReal.toReal (distance index))
        Problib.Real.Construction.Dedekind.zero)) tolerance
  rw [Problib.Real.Construction.Dedekind.sub_zero,
    Problib.Analysis.Real.abs_of_nonnegative
      (ENNReal.toReal_nonnegative _)]
  exact realSmall

/-- Positive Harris recurrence and strong aperiodicity give total-variation
convergence from every initial law. -/
public theorem strong_aperiodic_converges {law : Giry.Law space}
    (harris : PositiveHarris kernel law)
    (strong : StrongAperiodic kernel law.val) :
    ConvergesFromEveryLaw kernel law := by
  rcases strong with ⟨region, weight, minorant, measurable, minor, lawCharged,
    charged⟩
  have reach : law.val.AE (fun input =>
      ∃ count, ENNReal.lt ENNReal.zero (iterate kernel count input region)) :=
    Measure.ae_of_forall (fun input => by
      rcases harris.harris region measurable lawCharged input with ⟨_, certain⟩
      have positive : ENNReal.lt ENNReal.zero
          (hitKernel kernel region measurable input Set.univ) := by
        rw [certain]
        exact ENNReal.one_positive
      exact (hit_positive_iff_reaches kernel region measurable harris.markov
        input).mp positive)
  exact converges_of_harris_and_ae harris
    (strong_small_set_converges_ae minor measurable charged law
      harris.invariant reach)

end EveryStart

end Problib.Measure.Kernel
