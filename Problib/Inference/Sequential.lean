module

public import Problib.Inference.Population
public import Problib.Measure.Integral.Density.Ratio
public import Problib.Measure.Integral.Density.AlmostEverywhere
public import Problib.Measure.Decomposition.ZeroInfinity.Density
public import Problib.Measure.Integral.Lebesgue.Zero
public import Problib.Measure.Kernel.RadonNikodym.StandardBorel
set_option autoImplicit false

/-! Sequential extension of calibrated draws.

A stage moves a source measure `μ` on one space to a target `μ'` on another. It
draws `y` from a proposal kernel `q(x, ·)` and multiplies the weight by an
increment `ω(x, y)`. The stage is sound when
`∫ μ(dx) ∫ q(x, dy) ω(x, y) f(y) = ∫ f dμ'` for every nonnegative measurable
`f` (`SeqRN`). That is the same statement as `μ'` being `μ` bound through the
barycenters of the weighted proposal (`seq_rn_iff_bind`). So a stage extends a
calibrated draw (`weighted_extend`), extends it with an unbiased estimate of the
increment (`weighted_extend_estimated`), and moves an invariant population
(`step_invariant_of_seq_rn`). A stage can only reach targets that the proposal
charges (`seq_rn_absolutely_continuous`).

A proposal with density `q` against a reference, and a target with density `p`
against the same reference, give a stage with increment `p/q`
(`seq_rn_of_density_ratio`).

An SMCP3 stage draws `u` from a forward kernel `Q(x, ·)`, applies a measurable
map `(y, v) = F(x, u)`, and weighs the result by a density `ρ(y, v)`. It is
sound when `μ' ⊗ L = ρ · F∗(μ ⊗ Q)` for a Markov reverse kernel `L`. The stage
is then a `SeqRN` stage onto the extended target `μ' ⊗ L`
(`seq_rn_of_extended_density`), and forgetting `v` gives `μ'`
(`smcp3_weighted`, `step_invariant_of_smcp3`). The equation needs the reverse
law to be zero-infinity absolutely continuous against the forward law
(`StageSupport`, `stage_support_of_answer`).

A supplied target sequence chains invariant population steps across stage
spaces that may all differ (`TargetSequence`). Running it keeps invariance from
the first target to the last (`target_sequence_invariant`), and mapping the last
stage's values returns invariance for the output measure
(`sequential_targets_sound`). -/

namespace Problib.Inference

open Problib.Real Problib.Measure

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

public section

/-! ### The sequential equation -/

/-- SeqRN: `∫ μ(dx) ∫ q(x, dy) ω(x, y) f(y) = ∫ f dμ'` for every nonnegative
measurable `f`. -/
@[expose] def SeqRN {space : Space α} {result : Space β} (source : Measure space)
    (target : Measure result) (proposal : Kernel space result)
    (increment : α × β → NNReal) : Prop :=
  ∀ function : β → ENNReal, ENNRealMeasurable result function →
    lintegral source (fun input => lintegral (proposal input) (fun value =>
      ENNReal.mul (ENNReal.finite (increment (input, value))) (function value))) =
      lintegral target function

/-- The proposal's draw, paired with the increment. -/
theorem increment_pair_measurable {space : Space α} {result : Space β}
    {increment : α × β → NNReal}
    (incrementMeasurable : MeasurableMap (Space.product space result) weightSpace increment) :
    MeasurableMap (Space.product space result) (Space.product result weightSpace)
      (fun pair => (pair.2, increment pair)) :=
  Space.pair_measurable (Space.second_measurable space result) incrementMeasurable

/-- The proposal's draw at one input, paired with the increment. -/
theorem increment_value_measurable {space : Space α} {result : Space β}
    {increment : α × β → NNReal}
    (incrementMeasurable : MeasurableMap (Space.product space result) weightSpace increment)
    (input : α) :
    MeasurableMap result (Space.product result weightSpace)
      (fun value => (value, increment (input, value))) :=
  MeasurableMap.comp (increment_pair_measurable incrementMeasurable)
    (Kernel.pair_left_measurable input)

/-- Draw from the proposal and carry the increment as the weight. -/
@[expose] noncomputable def incrementKernel {space : Space α} {result : Space β}
    (proposal : Kernel space result) (proposalFinite : Kernel.IsSFinite proposal)
    (increment : α × β → NNReal)
    (incrementMeasurable : MeasurableMap (Space.product space result) weightSpace increment) :
    Kernel space (Space.product result weightSpace) :=
  (proposal.attach proposalFinite).map (fun pair => (pair.2, increment pair))
    (increment_pair_measurable incrementMeasurable)

theorem incrementKernel_apply {space : Space α} {result : Space β}
    (proposal : Kernel space result) (proposalFinite : Kernel.IsSFinite proposal)
    (increment : α × β → NNReal)
    (incrementMeasurable : MeasurableMap (Space.product space result) weightSpace increment)
    (input : α) :
    incrementKernel proposal proposalFinite increment incrementMeasurable input =
      (proposal input).map (fun value => (value, increment (input, value)))
        (increment_value_measurable incrementMeasurable input) := by
  rw [incrementKernel, Kernel.map_apply, Kernel.attach_apply, Measure.map_comp]
  exact increment_pair_measurable incrementMeasurable

/-- The increment kernel is s-finite when the proposal is. -/
@[expose] noncomputable def incrementKernelFinite {space : Space α} {result : Space β}
    {proposal : Kernel space result} (proposalFinite : Kernel.IsSFinite proposal)
    {increment : α × β → NNReal}
    (incrementMeasurable : MeasurableMap (Space.product space result) weightSpace increment) :
    Kernel.IsSFinite (incrementKernel proposal proposalFinite increment incrementMeasurable) :=
  (Kernel.IsSFinite.attach proposalFinite).map _ (increment_pair_measurable incrementMeasurable)

theorem incrementKernel_markov {space : Space α} {result : Space β}
    {proposal : Kernel space result} (markov : ∀ input, Measure.IsProbability (proposal input))
    (proposalFinite : Kernel.IsSFinite proposal) {increment : α × β → NNReal}
    (incrementMeasurable : MeasurableMap (Space.product space result) weightSpace increment)
    (input : α) :
    Measure.IsProbability
      (incrementKernel proposal proposalFinite increment incrementMeasurable input) := by
  rw [incrementKernel_apply]
  exact (markov input).map _ _

/-- The barycenter of the increment kernel weighs the proposal by the increment. -/
theorem lintegral_barycenter_increment {space : Space α} {result : Space β}
    (proposal : Kernel space result) (proposalFinite : Kernel.IsSFinite proposal)
    (increment : α × β → NNReal)
    (incrementMeasurable : MeasurableMap (Space.product space result) weightSpace increment)
    (input : α) {function : β → ENNReal} (measurable : ENNRealMeasurable result function) :
    lintegral (barycenterKernel
        (incrementKernel proposal proposalFinite increment incrementMeasurable) input) function =
      lintegral (proposal input) (fun value =>
        ENNReal.mul (ENNReal.finite (increment (input, value))) (function value)) := by
  rw [barycenterKernel_apply, lintegral_barycenter _ measurable, incrementKernel_apply,
    lintegral_map _ _ _ (weighted_integrand_measurable measurable)]
  rfl

/-- SeqRN says exactly that the target is the source bound through the
increment kernel's barycenters. -/
theorem seq_rn_iff_bind {space : Space α} {result : Space β} {source : Measure space}
    {target : Measure result} {proposal : Kernel space result}
    (proposalFinite : Kernel.IsSFinite proposal) {increment : α × β → NNReal}
    (incrementMeasurable : MeasurableMap (Space.product space result) weightSpace increment) :
    SeqRN source target proposal increment ↔
      source.bind (barycenterKernel
        (incrementKernel proposal proposalFinite increment incrementMeasurable)) = target := by
  constructor
  · intro rn
    refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
    rw [Measure.lintegral_bind _ _ measurable, ← rn function measurable]
    apply lintegral_congr
    intro input
    exact lintegral_barycenter_increment proposal proposalFinite increment incrementMeasurable
      input measurable
  · intro bound function measurable
    rw [← bound, Measure.lintegral_bind _ _ measurable]
    apply lintegral_congr
    intro input
    exact (lintegral_barycenter_increment proposal proposalFinite increment incrementMeasurable
      input measurable).symm

/-! ### Extending calibrated draws -/

/-- A SeqRN stage extends a calibrated draw: draw from the proposal and multiply
the weight by the increment. -/
theorem weighted_extend {space : Space α} {result : Space β} {source : Measure space}
    {target : Measure result} {weighted : Measure (Space.product space weightSpace)}
    {proposal : Kernel space result} {increment : α × β → NNReal}
    (markov : ∀ input, Measure.IsProbability (proposal input))
    (proposalFinite : Kernel.IsSFinite proposal)
    (incrementMeasurable : MeasurableMap (Space.product space result) weightSpace increment)
    (rn : SeqRN source target proposal increment) (calibrated : Calibrated source weighted) :
    Calibrated target (weighted.bind (reweight
      (incrementKernel proposal proposalFinite increment incrementMeasurable)
      (incrementKernelFinite proposalFinite incrementMeasurable))) := by
  have bound := weighted_bind
    (incrementKernel_markov markov proposalFinite incrementMeasurable)
    (incrementKernelFinite proposalFinite incrementMeasurable) calibrated
  rw [(seq_rn_iff_bind proposalFinite incrementMeasurable).mp rn] at bound
  exact bound

/-- The attached draw with its estimate, as a weighted draw of the value. -/
theorem estimated_value_measurable (space : Space α) (result : Space β) :
    MeasurableMap (Space.product (Space.product space result) weightSpace)
      (Space.product result weightSpace) (fun draw => (draw.1.2, draw.2)) :=
  Space.pair_measurable
    (MeasurableMap.comp (Space.second_measurable space result)
      (Space.first_measurable _ weightSpace))
    (Space.second_measurable _ weightSpace)

/-- Draw from the proposal, then draw an estimate of the increment at the pair,
and carry the estimate as the weight. -/
@[expose] noncomputable def estimatedIncrementKernel {space : Space α} {result : Space β}
    (proposal : Kernel space result) (proposalFinite : Kernel.IsSFinite proposal)
    (estimate : Kernel (Space.product space result) weightSpace)
    (estimateFinite : Kernel.IsSFinite estimate) :
    Kernel space (Space.product result weightSpace) :=
  (proposal.attach proposalFinite).comp
    ((estimate.attach estimateFinite).map (fun draw => (draw.1.2, draw.2))
      (estimated_value_measurable space result))

@[expose] noncomputable def estimatedIncrementKernelFinite {space : Space α} {result : Space β}
    {proposal : Kernel space result} (proposalFinite : Kernel.IsSFinite proposal)
    {estimate : Kernel (Space.product space result) weightSpace}
    (estimateFinite : Kernel.IsSFinite estimate) :
    Kernel.IsSFinite (estimatedIncrementKernel proposal proposalFinite estimate estimateFinite) :=
  (Kernel.IsSFinite.attach proposalFinite).comp
    ((Kernel.IsSFinite.attach estimateFinite).map _ (estimated_value_measurable space result))

/-- An unbiased increment estimate has the exact increment kernel's barycenters. -/
theorem barycenterKernel_estimated {space : Space α} {result : Space β}
    {proposal : Kernel space result} (proposalFinite : Kernel.IsSFinite proposal)
    {increment : α × β → NNReal}
    (incrementMeasurable : MeasurableMap (Space.product space result) weightSpace increment)
    {estimate : Kernel (Space.product space result) weightSpace}
    (estimateFinite : Kernel.IsSFinite estimate)
    (unbiased : UnbiasedEstimate (fun pair => ENNReal.finite (increment pair)) estimate) :
    barycenterKernel (estimatedIncrementKernel proposal proposalFinite estimate estimateFinite) =
      barycenterKernel (incrementKernel proposal proposalFinite increment incrementMeasurable) := by
  apply Kernel.ext
  intro input
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  have integrand := weighted_integrand_measurable measurable
  rw [lintegral_barycenter_increment _ _ _ _ _ measurable, barycenterKernel_apply,
    lintegral_barycenter _ measurable, estimatedIncrementKernel,
    Kernel.lintegral_comp _ _ _ integrand, Kernel.attach_apply,
    lintegral_map _ _ _
      (Kernel.lintegral_measurable _ integrand)]
  apply lintegral_congr
  intro value
  -- The inner integral is ∫ estimate (input, value) (w · f value), which is
  -- (∫ w) · f value = increment (input, value) · f value by `mean_eq`.
  rw [Kernel.map_apply, Kernel.attach_apply, Measure.map_comp,
    lintegral_map _ _ _ integrand]
  have scaled := lintegral_smul (estimate (input, value)) (function value)
    (finite_weight_measurable (MeasurableMap.identity weightSpace))
  rw [unbiased.mean_eq (input, value)] at scaled
  rw [ENNReal.mul_comm _ (function value), ← scaled]
  apply lintegral_congr
  intro weight
  exact ENNReal.mul_comm _ _

/-- A SeqRN stage whose increment is drawn as an unbiased estimate extends a
calibrated draw. The increment need not be computable, only its estimate. -/
theorem weighted_extend_estimated {space : Space α} {result : Space β}
    {source : Measure space} {target : Measure result}
    {weighted : Measure (Space.product space weightSpace)}
    {proposal : Kernel space result} {increment : α × β → NNReal}
    {estimate : Kernel (Space.product space result) weightSpace}
    (markov : ∀ input, Measure.IsProbability (proposal input))
    (proposalFinite : Kernel.IsSFinite proposal) (estimateFinite : Kernel.IsSFinite estimate)
    (unbiased : UnbiasedEstimate (fun pair => ENNReal.finite (increment pair)) estimate)
    (rn : SeqRN source target proposal increment) (calibrated : Calibrated source weighted) :
    Calibrated target (weighted.bind (reweight
      (estimatedIncrementKernel proposal proposalFinite estimate estimateFinite)
      (estimatedIncrementKernelFinite proposalFinite estimateFinite))) := by
  have incrementMeasurable : MeasurableMap (Space.product space result) weightSpace increment :=
    weight_measurable_of_finite unbiased.mean_measurable
  have stepMarkov : ∀ input, Measure.IsProbability
      (estimatedIncrementKernel proposal proposalFinite estimate estimateFinite input) := by
    intro input
    rw [estimatedIncrementKernel, Kernel.comp_apply]
    refine ((markov input).map _ (Kernel.pair_left_measurable input)).bind _ fun pair => ?_
    rw [Kernel.map_apply, Kernel.attach_apply, Measure.map_comp]
    exact (unbiased.probability pair).map _ _
  have bound := weighted_bind stepMarkov
    (estimatedIncrementKernelFinite proposalFinite estimateFinite) calibrated
  rw [barycenterKernel_estimated proposalFinite incrementMeasurable estimateFinite unbiased,
    (seq_rn_iff_bind proposalFinite incrementMeasurable).mp rn] at bound
  exact bound

/-- A SeqRN stage moves an invariant population: continue every lane by the
increment kernel, with the lane marginals the step's law must have. -/
theorem step_invariant_of_seq_rn {ι : Type} {lanes : Lanes ι} {space : Space α}
    {result : Space β} {source : Measure space} {target : Measure result}
    {proposal : Kernel space result} {increment : α × β → NNReal}
    {step : Kernel (populationSpace ι space) (populationSpace ι result)}
    (proposalFinite : Kernel.IsSFinite proposal)
    (incrementMeasurable : MeasurableMap (Space.product space result) weightSpace increment)
    (rn : SeqRN source target proposal increment)
    (stepMarkov : ∀ draws, Measure.IsProbability (step draws))
    (marginals : LaneMarginals step (reweight
      (incrementKernel proposal proposalFinite increment incrementMeasurable)
      (incrementKernelFinite proposalFinite incrementMeasurable))) :
    StepInvariant lanes lanes source target step := by
  have propagated := empirical_propagate (lanes := lanes) (source := source) stepMarkov marginals
  rw [(seq_rn_iff_bind proposalFinite incrementMeasurable).mp rn] at propagated
  exact propagated

/-- The barycenters of the increment kernel are the proposal reweighted by the
increment. -/
theorem barycenterKernel_increment {space : Space α} {result : Space β}
    (proposal : Kernel space result) (proposalFinite : Kernel.IsSFinite proposal)
    (increment : α × β → NNReal)
    (incrementMeasurable : MeasurableMap (Space.product space result) weightSpace increment)
    (input : α) :
    barycenterKernel (incrementKernel proposal proposalFinite increment incrementMeasurable)
        input =
      (proposal input).withDensity
        (fun value => ENNReal.finite (increment (input, value))) := by
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  rw [lintegral_barycenter_increment _ _ _ _ _ measurable,
    lintegral_withDensity _
      (finite_weight_measurable (MeasurableMap.comp incrementMeasurable
        (Kernel.pair_left_measurable input))) measurable]

/-- A SeqRN target is absolutely continuous against the source bound through the
proposal. A stage cannot put mass where the proposal puts none. -/
theorem seq_rn_absolutely_continuous {space : Space α} {result : Space β}
    {source : Measure space} {target : Measure result} {proposal : Kernel space result}
    (proposalFinite : Kernel.IsSFinite proposal) {increment : α × β → NNReal}
    (incrementMeasurable : MeasurableMap (Space.product space result) weightSpace increment)
    (rn : SeqRN source target proposal increment) :
    Measure.AbsolutelyContinuous target (source.bind proposal) := by
  intro set setMeasurable null
  rw [← (seq_rn_iff_bind proposalFinite incrementMeasurable).mp rn,
    Measure.bind_apply _ _ setMeasurable]
  rw [Measure.bind_apply _ _ setMeasurable] at null
  -- `null` says ∫ proposal x A = 0, so proposal x A = 0 for source-a.e. x, and at
  -- every such x the reweighted proposal also gives A zero mass.
  have almost := (lintegral_eq_zero_iff (proposal.measurable setMeasurable)).mp null
  refine lintegral_eq_zero_of_ae_zero (almost.mono fun input zero => ?_)
  dsimp only at zero ⊢
  rw [barycenterKernel_increment]
  exact Measure.absolutelyContinuous_withDensity _ _ setMeasurable zero

/-! ### Proposals with a density ratio -/

/-- A proposal with density `q` against a reference, and a target with density
`p` against the same reference, give a SeqRN stage whose increment is `p/q`.
The target must vanish where the proposal density does, and the proposal must
have finite mass at every input. -/
theorem seq_rn_of_density_ratio {space : Space α} {result : Space β}
    {source : Measure space} {target : Measure result}
    {proposal reference : Kernel space result} {p q : α → β → ENNReal}
    (numeratorMeasurable : ∀ input, ENNRealMeasurable result (p input))
    (denominatorMeasurable : ∀ input, ENNRealMeasurable result (q input))
    (proposalDensity : ∀ input, Measure.IsDensity (proposal input) (reference input) (q input))
    (proposalFinite : ∀ input, proposal input Set.univ ≠ ENNReal.top)
    (finite : ∀ input value, p input value ≠ ENNReal.top)
    (support : ∀ input, (reference input)
      (fun value => q input value = ENNReal.zero ∧ p input value ≠ ENNReal.zero) = ENNReal.zero)
    (target_eq : ∀ function : β → ENNReal, ENNRealMeasurable result function →
      lintegral target function = lintegral source (fun input =>
        lintegral (reference input) (fun value => ENNReal.mul (p input value) (function value)))) :
    SeqRN source target proposal
      (fun pair => densityRatio (p pair.1) (q pair.1) pair.2) := by
  intro function measurable
  rw [target_eq function measurable]
  apply lintegral_congr
  intro input
  have ratio := isDensity_densityRatio (numeratorMeasurable input) (denominatorMeasurable input)
    (Measure.isDensity_withDensity (reference input) (p input)) (proposalDensity input)
    (proposalFinite input) (finite input) (support input)
  -- ∫ proposal (ratio · f) = ∫ (proposal.withDensity ratio) f = ∫ (reference.withDensity p) f.
  rw [← lintegral_withDensity _
      (densityRatio_measurable (numeratorMeasurable input) (denominatorMeasurable input))
      measurable,
    ← ratio.eq_withDensity,
    lintegral_withDensity _ (numeratorMeasurable input) measurable]

/-! ### SMCP3 stages -/

/-- Draw `u ~ Q(x)` and return `F(x, u)`. -/
@[expose] noncomputable def smcp3Proposal {space : Space α} {auxiliary : Space γ}
    {result : Space β} {reverseSpace : Space δ}
    (forward : Kernel space auxiliary) (forwardFinite : Kernel.IsSFinite forward)
    (transform : α × γ → β × δ)
    (transformMeasurable : MeasurableMap (Space.product space auxiliary)
      (Space.product result reverseSpace) transform) :
    Kernel space (Space.product result reverseSpace) :=
  (forward.attach forwardFinite).map transform transformMeasurable

theorem smcp3Proposal_apply {space : Space α} {auxiliary : Space γ}
    {result : Space β} {reverseSpace : Space δ}
    (forward : Kernel space auxiliary) (forwardFinite : Kernel.IsSFinite forward)
    (transform : α × γ → β × δ)
    (transformMeasurable : MeasurableMap (Space.product space auxiliary)
      (Space.product result reverseSpace) transform) (input : α) :
    smcp3Proposal forward forwardFinite transform transformMeasurable input =
      (forward input).map (fun draw => transform (input, draw))
        (MeasurableMap.comp transformMeasurable (Kernel.pair_left_measurable input)) := by
  rw [smcp3Proposal, Kernel.map_apply, Kernel.attach_apply, Measure.map_comp]

@[expose] noncomputable def smcp3ProposalFinite {space : Space α} {auxiliary : Space γ}
    {result : Space β} {reverseSpace : Space δ}
    {forward : Kernel space auxiliary} (forwardFinite : Kernel.IsSFinite forward)
    {transform : α × γ → β × δ}
    (transformMeasurable : MeasurableMap (Space.product space auxiliary)
      (Space.product result reverseSpace) transform) :
    Kernel.IsSFinite (smcp3Proposal forward forwardFinite transform transformMeasurable) :=
  (Kernel.IsSFinite.attach forwardFinite).map _ transformMeasurable

theorem smcp3Proposal_markov {space : Space α} {auxiliary : Space γ}
    {result : Space β} {reverseSpace : Space δ} {forward : Kernel space auxiliary}
    (forwardMarkov : ∀ input, Measure.IsProbability (forward input))
    (forwardFinite : Kernel.IsSFinite forward) {transform : α × γ → β × δ}
    (transformMeasurable : MeasurableMap (Space.product space auxiliary)
      (Space.product result reverseSpace) transform) (input : α) :
    Measure.IsProbability (smcp3Proposal forward forwardFinite transform transformMeasurable input) := by
  rw [smcp3Proposal_apply]
  exact (forwardMarkov input).map _ _

/-- The stage density, read as an increment of the source value and the
extended draw. It ignores the source value. -/
theorem stage_density_measurable {space : Space α} {result : Space β} {reverseSpace : Space δ}
    {density : β × δ → NNReal}
    (densityMeasurable : MeasurableMap (Space.product result reverseSpace) weightSpace density) :
    MeasurableMap (Space.product space (Space.product result reverseSpace)) weightSpace
      (fun pair => density pair.2) :=
  MeasurableMap.comp densityMeasurable (Space.second_measurable _ _)

/-- An SMCP3 stage whose density answers the extended equation
`μ' ⊗ L = ρ · F∗(μ ⊗ Q)` is a SeqRN stage onto the extended target. -/
theorem seq_rn_of_extended_density {space : Space α} {auxiliary : Space γ}
    {result : Space β} {reverseSpace : Space δ}
    {source : Measure space} {target : Measure result}
    {forward : Kernel space auxiliary} {reverse : Kernel result reverseSpace}
    {transform : α × γ → β × δ} {density : β × δ → NNReal}
    (forwardFinite : Kernel.IsSFinite forward) (reverseFinite : Kernel.IsSFinite reverse)
    (transformMeasurable : MeasurableMap (Space.product space auxiliary)
      (Space.product result reverseSpace) transform)
    (densityMeasurable : MeasurableMap (Space.product result reverseSpace) weightSpace density)
    (answer : target.semiproduct reverse reverseFinite =
      ((source.semiproduct forward forwardFinite).map transform transformMeasurable).withDensity
        (fun pair => ENNReal.finite (density pair))) :
    SeqRN source (target.semiproduct reverse reverseFinite)
      (smcp3Proposal forward forwardFinite transform transformMeasurable)
      (fun pair => density pair.2) := by
  intro function measurable
  have weightedIntegrand := ENNRealMeasurable.mul (finite_weight_measurable densityMeasurable)
    measurable
  rw [answer, lintegral_withDensity _ (finite_weight_measurable densityMeasurable) measurable,
    lintegral_map _ _ _ weightedIntegrand,
    lintegral_semiproduct _ _ _ (weightedIntegrand.comp transformMeasurable)]
  apply lintegral_congr
  intro input
  rw [smcp3Proposal_apply, lintegral_map _ _ _ weightedIntegrand]

/-- Forgetting the second coordinate of a semiproduct with a Markov kernel gives
the first measure. -/
theorem semiproduct_map_fst {source : Space γ} {result : Space β} (measure : Measure source)
    {kernel : Kernel source result} (kernelFinite : Kernel.IsSFinite kernel)
    (markov : ∀ input, Measure.IsProbability (kernel input)) :
    (measure.semiproduct kernel kernelFinite).map Prod.fst (Space.first_measurable source result) =
      measure := by
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  rw [lintegral_map _ _ _ measurable,
    lintegral_semiproduct _ _ _ (measurable.comp (Space.first_measurable source result))]
  apply lintegral_congr
  intro input
  show lintegral (kernel input) (fun _ => function input) = function input
  rw [lintegral_const, (markov input).univ_eq_one, ENNReal.mul_one]

/-- One SMCP3 step on a weighted draw: `u ~ Q(x)`, `(y, v) = F(x, u)`, and
return `y` with weight `w · ρ(y, v)`. -/
@[expose] noncomputable def smcp3Step {space : Space α} {auxiliary : Space γ}
    {result : Space β} {reverseSpace : Space δ}
    (forward : Kernel space auxiliary) (forwardFinite : Kernel.IsSFinite forward)
    (transform : α × γ → β × δ)
    (transformMeasurable : MeasurableMap (Space.product space auxiliary)
      (Space.product result reverseSpace) transform)
    (density : β × δ → NNReal)
    (densityMeasurable : MeasurableMap (Space.product result reverseSpace) weightSpace density) :
    Kernel (Space.product space weightSpace) (Space.product result weightSpace) :=
  (reweight (incrementKernel (smcp3Proposal forward forwardFinite transform transformMeasurable)
      (smcp3ProposalFinite forwardFinite transformMeasurable) (fun pair => density pair.2)
      (stage_density_measurable densityMeasurable))
    (incrementKernelFinite _ _)).map (fun draw => (draw.1.1, draw.2))
    (value_map_measurable (Space.first_measurable result reverseSpace))

/-- An SMCP3 stage extends a calibrated draw to the stage target. The reverse
kernel is Markov, so forgetting its coordinate loses no mass. -/
theorem smcp3_weighted {space : Space α} {auxiliary : Space γ}
    {result : Space β} {reverseSpace : Space δ}
    {source : Measure space} {target : Measure result}
    {weighted : Measure (Space.product space weightSpace)}
    {forward : Kernel space auxiliary} {reverse : Kernel result reverseSpace}
    {transform : α × γ → β × δ} {density : β × δ → NNReal}
    (forwardMarkov : ∀ input, Measure.IsProbability (forward input))
    (reverseMarkov : ∀ value, Measure.IsProbability (reverse value))
    (forwardFinite : Kernel.IsSFinite forward) (reverseFinite : Kernel.IsSFinite reverse)
    (transformMeasurable : MeasurableMap (Space.product space auxiliary)
      (Space.product result reverseSpace) transform)
    (densityMeasurable : MeasurableMap (Space.product result reverseSpace) weightSpace density)
    (answer : target.semiproduct reverse reverseFinite =
      ((source.semiproduct forward forwardFinite).map transform transformMeasurable).withDensity
        (fun pair => ENNReal.finite (density pair)))
    (calibrated : Calibrated source weighted) :
    Calibrated target (weighted.bind
      (smcp3Step forward forwardFinite transform transformMeasurable density densityMeasurable)) := by
  have extended := weighted_extend
    (smcp3Proposal_markov forwardMarkov forwardFinite transformMeasurable)
    (smcp3ProposalFinite forwardFinite transformMeasurable)
    (stage_density_measurable densityMeasurable)
    (seq_rn_of_extended_density forwardFinite reverseFinite transformMeasurable
      densityMeasurable answer)
    calibrated
  have mapped := weighted_map (Space.first_measurable result reverseSpace) extended
  rw [semiproduct_map_fst target reverseFinite reverseMarkov] at mapped
  rw [smcp3Step, ← Kernel.comp_deterministic, ← Measure.bind_assoc,
    Measure.bind_deterministic]
  exact mapped

/-- The lane form of an SMCP3 stage: continue every lane by the extended
increment kernel, then forget every lane's reverse coordinate. -/
theorem step_invariant_of_smcp3 {ι : Type} {lanes : Lanes ι} {space : Space α}
    {auxiliary : Space γ} {result : Space β} {reverseSpace : Space δ}
    {source : Measure space} {target : Measure result}
    {forward : Kernel space auxiliary} {reverse : Kernel result reverseSpace}
    {transform : α × γ → β × δ} {density : β × δ → NNReal}
    {step : Kernel (populationSpace ι space) (populationSpace ι (Space.product result reverseSpace))}
    (reverseMarkov : ∀ value, Measure.IsProbability (reverse value))
    (forwardFinite : Kernel.IsSFinite forward) (reverseFinite : Kernel.IsSFinite reverse)
    (transformMeasurable : MeasurableMap (Space.product space auxiliary)
      (Space.product result reverseSpace) transform)
    (densityMeasurable : MeasurableMap (Space.product result reverseSpace) weightSpace density)
    (answer : target.semiproduct reverse reverseFinite =
      ((source.semiproduct forward forwardFinite).map transform transformMeasurable).withDensity
        (fun pair => ENNReal.finite (density pair)))
    (stepMarkov : ∀ draws, Measure.IsProbability (step draws))
    (marginals : LaneMarginals step (reweight
      (incrementKernel (smcp3Proposal forward forwardFinite transform transformMeasurable)
        (smcp3ProposalFinite forwardFinite transformMeasurable) (fun pair => density pair.2)
        (stage_density_measurable densityMeasurable))
      (incrementKernelFinite _ _))) :
    StepInvariant lanes lanes source target
      (step.comp (Kernel.deterministic (lanewise Prod.fst)
        (lanewise_measurable (Space.first_measurable result reverseSpace)))) := by
  have extended := step_invariant_of_seq_rn (lanes := lanes)
    (smcp3ProposalFinite forwardFinite transformMeasurable)
    (stage_density_measurable densityMeasurable)
    (seq_rn_of_extended_density forwardFinite reverseFinite transformMeasurable
      densityMeasurable answer)
    stepMarkov marginals
  have forgotten := step_invariant_lanewise (lanes := lanes)
    (source := target.semiproduct reverse reverseFinite)
    (Space.first_measurable result reverseSpace)
  rw [semiproduct_map_fst target reverseFinite reverseMarkov] at forgotten
  exact step_invariant_comp extended forgotten

/-! ### Stage support -/

/-- The support obligation for an SMCP3 stage's density answer: the backward law
`μ' ⊗ L` is zero-infinity absolutely continuous against the forward law
`F∗(μ ⊗ Q)`. -/
@[expose] def StageSupport {extended : Space γ} (backward forward : Measure extended) : Prop :=
  Measure.ZeroInfinityAbsolutelyContinuous backward forward

/-- A density answer discharges the stage's support obligation. -/
theorem stage_support_of_answer {extended : Space γ} {backward forward : Measure extended}
    {density : γ → NNReal} (densityMeasurable : MeasurableMap extended weightSpace density)
    (answer : backward = forward.withDensity (fun pair => ENNReal.finite (density pair))) :
    StageSupport backward forward :=
  Measure.IsDensity.zeroInfinityAbsolutelyContinuous answer (finite_weight_measurable densityMeasurable)

/-- On a standard Borel extended space, support gives an extended-valued density
answer. A finite runtime weight also needs the density finite where the forward
law charges, which the stage's producer proves.

Route: `Kernel.RadonNikodymDerivative.nonempty_iff_of_standardBorel` at the
constant kernels of `backward` and `forward` on `Space.discrete Unit`, with
`Kernel.IsSFinite.const` for both certificates, then `reconstruct` at `()`. -/
theorem stage_answer_of_support {extended : Space γ} {backward forward : Measure extended}
    (presentation : StandardBorel extended)
    (backwardFinite : Measure.SFinite backward) (forwardFinite : Measure.SFinite forward)
    (support : StageSupport backward forward) :
    ∃ density : γ → ENNReal, ENNRealMeasurable extended density ∧
      backward = forward.withDensity density := by
  let derivative := Kernel.RadonNikodymDerivative.ofStandardBorel presentation
    (Kernel.IsSFinite.const (Space.discrete Unit) backwardFinite)
    (Kernel.IsSFinite.const (Space.discrete Unit) forwardFinite) fun _ => support
  exact ⟨(derivative.fiber ()).density, (derivative.fiber ()).density_measurable,
    (derivative.fiber ()).reconstruct⟩

/-! ### Supplied target sequences -/

/-- A chain of invariant population steps from a first target to a last. The
stage spaces may all differ, and no stage need be a cut of another. -/
inductive TargetSequence {ι : Type} (lanes : Lanes ι) :
    {first last : Type u} → {firstSpace : Space first} → {lastSpace : Space last} →
      Measure firstSpace → Measure lastSpace → Type (u + 1)
  | final {current : Type u} {space : Space current} (target : Measure space) :
      TargetSequence lanes target target
  | stage {current middle last : Type u} {space : Space current} {middleSpace : Space middle}
      {lastSpace : Space last} {source : Measure space} {next : Measure middleSpace}
      {target : Measure lastSpace}
      (step : Kernel (populationSpace ι space) (populationSpace ι middleSpace))
      (invariant : StepInvariant lanes lanes source next step)
      (rest : TargetSequence lanes next target) : TargetSequence lanes source target

namespace TargetSequence

variable {ι : Type} {lanes : Lanes ι}

/-- Run every stage in order. -/
noncomputable def run : {first last : Type u} → {firstSpace : Space first} →
    {lastSpace : Space last} → {source : Measure firstSpace} → {target : Measure lastSpace} →
    TargetSequence lanes source target →
      Kernel (populationSpace ι firstSpace) (populationSpace ι lastSpace)
  | _, _, _, _, _, _, final _ =>
      Kernel.deterministic (fun draws => draws) (MeasurableMap.identity _)
  | _, _, _, _, _, _, stage step _ rest => step.comp rest.run

/-- The number of stages. -/
def length : {first last : Type u} → {firstSpace : Space first} →
    {lastSpace : Space last} → {source : Measure firstSpace} → {target : Measure lastSpace} →
    TargetSequence lanes source target → Nat
  | _, _, _, _, _, _, final _ => 0
  | _, _, _, _, _, _, stage _ _ rest => rest.length + 1

end TargetSequence

/-- Running a target sequence carries invariance from its first target to its
last, by induction over the stages. -/
theorem target_sequence_invariant {ι : Type} {lanes : Lanes ι} :
    {first last : Type u} → {firstSpace : Space first} → {lastSpace : Space last} →
    {source : Measure firstSpace} → {target : Measure lastSpace} →
    (sequence : TargetSequence lanes source target) →
      StepInvariant lanes lanes source target sequence.run
  | _, _, _, _, _, _, .final _ => by
      intro population invariant
      rw [TargetSequence.run, Measure.bind_deterministic, Measure.map_id]
      · exact invariant
      · exact MeasurableMap.identity _
  | _, _, _, _, _, _, .stage _ invariant rest => by
      rw [TargetSequence.run]
      exact step_invariant_comp invariant (target_sequence_invariant rest)

/-- A supplied target sequence answers for the output measure: start from a
population invariant for the first target, run the stages, and map every lane
of the last stage by the return map. -/
theorem sequential_targets_sound {ι : Type} {lanes : Lanes ι} {first last : Type u}
    {firstSpace : Space first} {lastSpace : Space last} {result : Space γ}
    {source : Measure firstSpace} {terminal : Measure lastSpace} {output : Measure result}
    (sequence : TargetSequence lanes source terminal)
    {start : Measure (populationSpace ι firstSpace)}
    (initial : EmpiricalInvariant lanes source start)
    {ret : last → γ} (retMeasurable : MeasurableMap lastSpace result ret)
    (presents : terminal.map ret retMeasurable = output) :
    EmpiricalInvariant lanes output
      ((start.bind sequence.run).map (lanewise ret) (lanewise_measurable retMeasurable)) := by
  rw [← presents]
  exact empirical_map retMeasurable (target_sequence_invariant sequence start initial)

end

end Problib.Inference
