module

public import Problib.Inference.MetropolisHastings
public import Problib.Inference.Presented
public import Problib.Inference.Weighting
public import Problib.Measure.Integral.Density.AlmostEverywhere
public import Problib.Measure.Real.Arithmetic

set_option autoImplicit false

/-! # Clamping a Metropolis–Hastings weight, one start at a time

A Metropolis–Hastings chain whose weight is unbounded over its states has no
minorization that holds uniformly: from a state of weight `w₀`, a proposal of
weight at most `b` is accepted with probability at most `b / w₀`. A
pseudo-marginal chain is one such chain, since its state carries any estimate.

When every proposal lands at weight at most `level` almost surely, the chain
never leaves the states below `level` once it starts there. On those states the
chain and the chain with its weight capped at `level` accept alike, so their
iterates agree from every start below `level` (`mh_iterates_agree`). The
proposal can be any kernel.

For the independence chain, the capped weight is bounded, so the capped chain
is minorized (`independence_minorizes`), and it keeps the reference weighted by
the original weight invariant, because the two weights agree almost surely under
the reference. Taking the level above both the bound and the start, every start
approaches every law proportional to that weighted reference
(`independence_approaches`).
-/

namespace Problib.Inference

open Problib.Measure Problib.Measure.Real Problib.Real Problib.Real.Construction

universe u

variable {σ : Type u} {space : Space σ}

public section

/-! ### The capped weight -/

/-- The weight, read as a real. -/
@[expose] noncomputable def realWeight (weight : σ → NNReal) (state : σ) : Carrier :=
  NNReal.toReal (weight state)

/-- The weight, capped at `level`. -/
@[expose] noncomputable def cappedWeight (weight : σ → NNReal) (level : NNReal) (state : σ) :
    Carrier :=
  @ite Carrier (NNReal.le (weight state) level) (Classical.propDecidable _)
    (NNReal.toReal (weight state)) (NNReal.toReal level)

theorem cappedWeight_of_le {weight : σ → NNReal} {level : NNReal} {state : σ}
    (below : NNReal.le (weight state) level) :
    cappedWeight weight level state = realWeight weight state :=
  ite_eq_left below

theorem cappedWeight_le (weight : σ → NNReal) (level : NNReal) (state : σ) :
    Dedekind.le (cappedWeight weight level state) (NNReal.toReal level) := by
  unfold cappedWeight
  split
  next below => exact below
  next => exact Dedekind.le_refl _

variable {weight : σ → NNReal} (measurable : MeasurableMap space weightSpace weight)
include measurable

/-- The states at or below a level form a measurable set. -/
theorem weightBelow_measurable (level : NNReal) :
    space.Measurable fun state => NNReal.le (weight state) level := by
  have pair : MeasurableMap space (Space.product space weightSpace)
      (fun state => (state, weight state)) :=
    Space.pair_measurable (MeasurableMap.identity space) measurable
  have same : (fun state => NNReal.le (weight state) level) =
      Set.preimage (fun state => (state, weight state)) (Set.complement (weightAbove level)) := by
    apply Set.ext
    intro state
    exact ⟨not_weightAbove (draw := (state, weight state)),
      le_of_not_weightAbove (draw := (state, weight state))⟩
  rw [same]
  exact pair ((Space.product space weightSpace).complement (weightAbove_measurable space level))

theorem realWeight_measurable : MeasurableMap space borel (realWeight weight) :=
  MeasurableMap.comp weight_toReal_measurable measurable

theorem cappedWeight_measurable (level : NNReal) :
    MeasurableMap space borel (cappedWeight weight level) :=
  measurable_piecewise (weightBelow_measurable measurable level) (realWeight_measurable measurable)
    (MeasurableMap.constant _ borel _)

/-! ### The carried and capped chains agree below the level -/

variable (proposal : Kernel space space) (proposalFinite : Kernel.IsSFinite proposal)

/-- The Metropolis–Hastings chain on the weight. -/
@[expose] noncomputable def carriedChain : Kernel space space :=
  mhKernel proposal proposalFinite (metropolisAccept (realWeight weight))
    (metropolisAccept_measurable (realWeight_measurable measurable))

/-- The Metropolis–Hastings chain on the weight capped at `level`. -/
@[expose] noncomputable def cappedChain (level : NNReal) : Kernel space space :=
  mhKernel proposal proposalFinite (metropolisAccept (cappedWeight weight level))
    (metropolisAccept_measurable (cappedWeight_measurable measurable level))

variable {proposal} {level : NNReal}
  (light : ∀ state, (proposal state).AE fun next => NNReal.le (weight next) level)
include light

/-- From below the level, the two chains take one step alike: their
acceptances agree wherever the proposal lands. -/
theorem mh_steps_agree {state : σ} (below : NNReal.le (weight state) level) :
    carriedChain measurable proposal proposalFinite state =
      cappedChain measurable proposal proposalFinite level state := by
  refine (Measure.eq_iff_lintegral _ _).mpr fun function functionMeasurable => ?_
  rw [carriedChain, cappedChain, lintegral_mhKernel _ _ _ _ _ functionMeasurable,
    lintegral_mhKernel _ _ _ _ _ functionMeasurable]
  refine lintegral_congr_ae ((light state).mono fun proposed proposedBelow => ?_)
  have accept : metropolisAccept (realWeight weight) (state, proposed) =
      metropolisAccept (cappedWeight weight level) (state, proposed) := by
    unfold metropolisAccept
    rw [cappedWeight_of_le below, cappedWeight_of_le proposedBelow]
  simp only [accept]

/-- From below the level, the carried chain stays below it. -/
theorem mh_stays_below {state : σ} (below : NNReal.le (weight state) level) :
    (carriedChain measurable proposal proposalFinite state).AE fun next =>
      NNReal.le (weight next) level := by
  have outside := space.complement (weightBelow_measurable measurable level)
  show carriedChain measurable proposal proposalFinite state (Set.complement _) = ENNReal.zero
  rw [apply_eq_lintegral_indicator _ outside, carriedChain,
    lintegral_mhKernel _ _ _ _ _ (ENNRealMeasurable.indicator outside
      (ENNRealMeasurable.constant _ _))]
  refine lintegral_eq_zero_of_ae_zero ((light state).mono fun proposed proposedBelow => ?_)
  simp [ennrealIndicator, ennrealPiecewise, Set.complement, proposedBelow, below,
    ENNReal.mul_zero, ENNReal.add_zero]

/-- From below the level, the carried and capped chains' iterates agree. -/
theorem mh_iterates_agree (count : Nat) :
    ∀ state : σ, NNReal.le (weight state) level →
      Kernel.iterate (carriedChain measurable proposal proposalFinite) count state =
        Kernel.iterate (cappedChain measurable proposal proposalFinite level) count state := by
  induction count with
  | zero => intro state _; rfl
  | succ count previous =>
      intro state below
      show (carriedChain measurable proposal proposalFinite state).bind
          (Kernel.iterate (carriedChain measurable proposal proposalFinite) count) =
        (cappedChain measurable proposal proposalFinite level state).bind
          (Kernel.iterate (cappedChain measurable proposal proposalFinite level) count)
      rw [← mh_steps_agree measurable proposalFinite light below]
      exact Measure.bind_congr_ae _
        ((mh_stays_below measurable proposalFinite light below).mono fun next nextBelow =>
          previous next nextBelow)

end

/-! ### The independence chain -/

public section

variable {weight : σ → NNReal} (measurable : MeasurableMap space weightSpace weight)
  {reference : Measure space} (referenceFinite : Measure.SFinite reference)

/-- The independence chain on the weight: every proposal is drawn from the
reference. -/
noncomputable abbrev independenceChain : Kernel space space :=
  carriedChain measurable (Kernel.const _ reference) (Kernel.IsSFinite.const _ referenceFinite)

/-- The capped independence chain keeps the reference weighted by the weight
invariant, when the reference puts the weight below the level. -/
theorem capped_invariant (probability : Measure.IsProbability reference) {level : NNReal}
    (light : reference.AE fun state => NNReal.le (weight state) level) :
    KernelInvariant (reference.withDensity fun state => ENNReal.finite (weight state))
      (cappedChain measurable (Kernel.const _ reference)
        (Kernel.IsSFinite.const _ referenceFinite) level) := by
  have same : reference.withDensity (fun state => ENNReal.ofReal (cappedWeight weight level state)) =
      reference.withDensity fun state => ENNReal.finite (weight state) :=
    Measure.withDensity_congr_ae (light.mono fun state below => by
      show ENNReal.ofReal (cappedWeight weight level state) = ENNReal.finite (weight state)
      rw [cappedWeight_of_le below]
      exact ENNReal.ofReal_toReal_finite _)
  rw [← same]
  exact metropolis_invariant reference (Kernel.IsSFinite.const _ referenceFinite)
    (fun _ => probability) (independence_reversible reference referenceFinite)
    (cappedWeight_measurable measurable level)

/-- From every start, the independence chain approaches each probability law
proportional to the reference weighted by the weight, when the reference bounds
the weight almost surely. -/
theorem independence_approaches (probability : Measure.IsProbability reference)
    {bound : NNReal} (light : reference.AE fun state => NNReal.le (weight state) bound)
    (start : σ) (stationary : Giry.Law space) (factor : ENNReal)
    (proportional : stationary.val = Measure.smul factor
      (reference.withDensity fun state => ENNReal.finite (weight state)))
    (law : Nat → Giry.Law space)
    (iterated : ∀ count, (law count).val = (Measure.dirac _ start).bind
      (Kernel.iterate (independenceChain measurable referenceFinite) count)) :
    Vanishes fun count => Giry.Law.totalVariation (law count) stationary := by
  obtain ⟨level, boundBelow, startBelow⟩ : ∃ level,
      NNReal.le bound level ∧ NNReal.le (weight start) level := by
    rcases NNReal.le_total bound (weight start) with below | above
    · exact ⟨weight start, below, NNReal.le_refl _⟩
    · exact ⟨bound, NNReal.le_refl _, above⟩
  have lightLevel : reference.AE fun state => NNReal.le (weight state) level :=
    light.mono fun _ below => NNReal.le_trans below boundBelow
  have normalizable : Measure.IsNormalizable
      (reference.withDensity fun state => ENNReal.ofReal (cappedWeight weight level state)) := by
    have same : reference.withDensity
          (fun state => ENNReal.ofReal (cappedWeight weight level state)) =
        reference.withDensity fun state => ENNReal.finite (weight state) :=
      Measure.withDensity_congr_ae (lightLevel.mono fun state below => by
        show ENNReal.ofReal (cappedWeight weight level state) = ENNReal.finite (weight state)
        rw [cappedWeight_of_le below]
        exact ENNReal.ofReal_toReal_finite _)
    rw [same]
    exact Measure.IsNormalizable.of_proportional stationary.property factor proportional
  obtain ⟨scale, minor⟩ := independence_minorizes reference referenceFinite probability
    (cappedWeight_measurable measurable level) (cappedWeight_le weight level) normalizable
  have invariant : stationary.val.bind (cappedChain measurable (Kernel.const _ reference)
      (Kernel.IsSFinite.const _ referenceFinite) level) = stationary.val := by
    rw [proportional]
    exact kernel_invariant_smul factor
      (capped_invariant measurable referenceFinite probability lightLevel)
  have vanishes := minorization_vanishes minor stationary
    ⟨Measure.dirac _ start, Measure.IsProbability.dirac _ start⟩ invariant
  refine vanishes_of_le (fun count => ?_) vanishes
  have same : law count = ⟨(Measure.dirac _ start).bind
      (Kernel.iterate (cappedChain measurable (Kernel.const _ reference)
        (Kernel.IsSFinite.const _ referenceFinite) level) count),
      (Measure.IsProbability.dirac _ start).bind _
        (Kernel.iterate_isProbability _ minor.markov count)⟩ := by
    apply Subtype.ext
    show (law count).val = (Measure.dirac _ start).bind
      (Kernel.iterate (cappedChain measurable (Kernel.const _ reference)
        (Kernel.IsSFinite.const _ referenceFinite) level) count)
    rw [iterated count, Measure.dirac_bind, Measure.dirac_bind]
    exact mh_iterates_agree measurable (Kernel.IsSFinite.const _ referenceFinite)
      (fun _ => by rw [Kernel.const_apply]; exact lightLevel) count start startBelow
  rw [same]
  exact ENNReal.le_refl _

end

end Problib.Inference
