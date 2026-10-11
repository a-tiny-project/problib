module

public import Problib.Inference.Weighting
public import Problib.Inference.MetropolisHastings
set_option autoImplicit false

/-! Pseudo-marginal Metropolis–Hastings.

A pseudo-marginal chain cannot evaluate its target's density `p(x)` against a
reference `ξ`, but it can draw an auxiliary `u` from an estimator kernel `m` at
`x` and read an estimate `p̂(x, u)` off it. The chain runs Metropolis–Hastings
on the pair `(x, u)`. It proposes `x'` and then a fresh `u'` from `m` at `x'`
(`extendedProposal`), and it keeps the estimate of the current state until a
move is accepted (`pseudoMarginalKernel`).

The extended target `ξ(dx) m(x, du) p̂(x, u)` (`extendedTarget`) is invariant
for the chain whenever the proposal on values is reversible for `ξ`
(`pseudoMarginalKernel_invariant`). No property of the estimate enters: the
refreshed auxiliary makes the extended proposal reversible for `ξ ⊗ m`
(`extended_reversible`), and the chain is the Metropolis step on that
reference with weight `p̂`. Unbiasedness enters only the marginal. When `p̂`
read off `m` is unbiased for `p`, the extended target's value marginal is
`ξ` weighted by `p` (`pseudo_marginal_marginal`), so the chain targets the
exact posterior. The Hastings form, for proposals with a density and no
reversibility, is `PseudoMarginal.Hastings`. -/

namespace Problib.Inference

open Problib.Real Problib.Measure

universe u v

variable {α : Type u} {υ : Type v} {space : Space α} {extra : Space υ}

public section

/-! ### The extended target -/

/-- The extended target `ξ(dx) m(x, du) p̂(x, u)`. -/
@[expose] noncomputable def extendedTarget (reference : Measure space)
    (estimator : Kernel space extra) (estimatorFinite : Kernel.IsSFinite estimator)
    (estimate : α × υ → NNReal) : Measure (Space.product space extra) :=
  (reference.semiproduct estimator estimatorFinite).withDensity
    (fun point => ENNReal.finite (estimate point))

/-- An estimate unbiased for `p` makes the extended target's value marginal the
reference weighted by `p`. -/
theorem pseudo_marginal_marginal {reference : Measure space} {estimator : Kernel space extra}
    (estimatorFinite : Kernel.IsSFinite estimator) {estimate : α × υ → NNReal}
    (estimateMeasurable : MeasurableMap (Space.product space extra) weightSpace estimate)
    {density : α → ENNReal}
    (unbiased : UnbiasedEstimate density
      (readEstimate estimator estimatorFinite estimate estimateMeasurable)) :
    (extendedTarget reference estimator estimatorFinite estimate).map Prod.fst
        (Space.first_measurable space extra) =
      reference.withDensity density := by
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  have estimateFinite := finite_weight_measurable estimateMeasurable
  have firstMeasurable := measurable.comp (Space.first_measurable space extra)
  rw [lintegral_map _ _ _ measurable, extendedTarget,
    lintegral_withDensity _ estimateFinite firstMeasurable,
    lintegral_semiproduct _ _ _ (ENNRealMeasurable.mul estimateFinite firstMeasurable),
    lintegral_withDensity _ unbiased.mean_measurable measurable]
  apply lintegral_congr
  intro input
  have mean := unbiased.mean_eq input
  rw [readEstimate_apply,
    lintegral_map _ _ _ (finite_weight_measurable (MeasurableMap.identity weightSpace))] at mean
  have scaled := lintegral_smul (estimator input) (function input)
    (finite_weight_measurable (Kernel.section_measurable estimateMeasurable input))
  rw [mean] at scaled
  rw [ENNReal.mul_comm (density input), ← scaled]
  apply lintegral_congr
  intro point
  exact ENNReal.mul_comm _ _

/-! ### The extended proposal -/

/-- Propose `x'` from `proposal` at `x`, then draw a fresh auxiliary `u'` from
the estimator at `x'`. The current auxiliary is discarded. -/
@[expose] noncomputable def extendedProposal (proposal : Kernel space space)
    (estimator : Kernel space extra) (estimatorFinite : Kernel.IsSFinite estimator) :
    Kernel (Space.product space extra) (Space.product space extra) :=
  (proposal.comp (estimator.attach estimatorFinite)).precomp Prod.fst
    (Space.first_measurable space extra)

/-- The extended proposal from `(x, u)` is the proposal at `x` joined with the
estimator. -/
theorem extendedProposal_apply (proposal : Kernel space space)
    (estimator : Kernel space extra) (estimatorFinite : Kernel.IsSFinite estimator)
    (point : α × υ) :
    extendedProposal proposal estimator estimatorFinite point =
      (proposal point.1).semiproduct estimator estimatorFinite :=
  rfl

/-- The extended proposal of s-finite kernels is s-finite. -/
@[expose] noncomputable def extendedProposalFinite {proposal : Kernel space space}
    (proposalFinite : Kernel.IsSFinite proposal) {estimator : Kernel space extra}
    (estimatorFinite : Kernel.IsSFinite estimator) :
    Kernel.IsSFinite (extendedProposal proposal estimator estimatorFinite) :=
  (Kernel.IsSFinite.comp proposalFinite (Kernel.IsSFinite.attach estimatorFinite)).precomp
    Prod.fst (Space.first_measurable space extra)

/-- The extended proposal of Markov kernels is Markov. -/
theorem extendedProposal_markov {proposal : Kernel space space}
    (proposalMarkov : ∀ input, Measure.IsProbability (proposal input))
    {estimator : Kernel space extra} (estimatorFinite : Kernel.IsSFinite estimator)
    (estimatorMarkov : ∀ input, Measure.IsProbability (estimator input)) (point : α × υ) :
    Measure.IsProbability (extendedProposal proposal estimator estimatorFinite point) :=
  semiproduct_isProbability (proposalMarkov point.1) estimatorFinite estimatorMarkov

/-- Two estimator draws, at the two values of a pair, integrated in either
order. -/
private theorem estimator_pair_measurable {estimator : Kernel space extra}
    (estimatorFinite : Kernel.IsSFinite estimator)
    {function : (α × υ) × (α × υ) → ENNReal}
    (measurable : ENNRealMeasurable (Space.product (Space.product space extra)
      (Space.product space extra)) function) :
    ENNRealMeasurable (Space.product space space) (fun pair =>
      lintegral (estimator pair.1) fun current =>
        lintegral (estimator pair.2) fun next => function ((pair.1, current), (pair.2, next))) := by
  have innerMeasurable : ENNRealMeasurable (Space.product (Space.product space space) extra)
      (fun point => lintegral (estimator point.1.2) fun next =>
        function ((point.1.1, point.2), (point.1.2, next))) :=
    Kernel.lintegral_measurable_joint
      (estimator.precomp (fun point : (α × α) × υ => point.1.2)
        (MeasurableMap.comp (Space.second_measurable space space)
          (Space.first_measurable _ extra)))
      (estimatorFinite.precomp _ _)
      (function := fun point next => function ((point.1.1, point.2), (point.1.2, next)))
      (measurable.comp
        (Space.pair_measurable
          (Space.pair_measurable
            (MeasurableMap.comp (Space.first_measurable space space)
              (MeasurableMap.comp (Space.first_measurable _ extra)
                (Space.first_measurable _ extra)))
            (MeasurableMap.comp (Space.second_measurable _ extra)
              (Space.first_measurable _ extra)))
          (Space.pair_measurable
            (MeasurableMap.comp (Space.second_measurable space space)
              (MeasurableMap.comp (Space.first_measurable _ extra)
                (Space.first_measurable _ extra)))
            (Space.second_measurable _ extra))))
  exact Kernel.lintegral_measurable_joint
    (estimator.precomp Prod.fst (Space.first_measurable space space))
    (estimatorFinite.precomp _ _)
    (function := fun pair current => lintegral (estimator pair.2) fun next =>
      function ((pair.1, current), (pair.2, next)))
    innerMeasurable

/-- Integrating against the extended joint is integrating against the value
joint `ξ ⊗ q`, then against the estimator at each of the pair's two values. -/
private theorem lintegral_extended_joint {reference : Measure space}
    {proposal : Kernel space space} (proposalFinite : Kernel.IsSFinite proposal)
    {estimator : Kernel space extra} (estimatorFinite : Kernel.IsSFinite estimator)
    {function : (α × υ) × (α × υ) → ENNReal}
    (measurable : ENNRealMeasurable (Space.product (Space.product space extra)
      (Space.product space extra)) function) :
    lintegral ((reference.semiproduct estimator estimatorFinite).semiproduct
        (extendedProposal proposal estimator estimatorFinite)
        (extendedProposalFinite proposalFinite estimatorFinite)) function =
      lintegral (reference.semiproduct proposal proposalFinite) (fun pair =>
        lintegral (estimator pair.1) fun current =>
          lintegral (estimator pair.2) fun next =>
            function ((pair.1, current), (pair.2, next))) := by
  rw [lintegral_semiproduct _ _ _ measurable,
    lintegral_semiproduct _ _ _
      (Kernel.lintegral_measurable_joint _ (extendedProposalFinite proposalFinite estimatorFinite)
        (function := fun point next => function (point, next)) measurable),
    lintegral_semiproduct _ _ _ (estimator_pair_measurable estimatorFinite measurable)]
  apply lintegral_congr
  intro value
  have proposed : ∀ current,
      lintegral (extendedProposal proposal estimator estimatorFinite (value, current))
          (fun next => function ((value, current), next)) =
        lintegral (proposal value) fun target =>
          lintegral (estimator target) fun next => function ((value, current), (target, next)) := by
    intro current
    rw [extendedProposal_apply, lintegral_semiproduct _ _ _
      (measurable.comp (Kernel.pair_left_measurable (value, current)))]
  rw [lintegral_congr _ proposed]
  have rowMeasurable : ENNRealMeasurable (Space.product extra space) (fun point =>
      lintegral (estimator point.2) fun next => function ((value, point.1), (point.2, next))) :=
    Kernel.lintegral_measurable_joint
      (estimator.precomp Prod.snd (Space.second_measurable extra space))
      (estimatorFinite.precomp _ _)
      (function := fun point next => function ((value, point.1), (point.2, next)))
      (measurable.comp
        (Space.pair_measurable
          (Space.pair_measurable (MeasurableMap.constant _ space value)
            (MeasurableMap.comp (Space.first_measurable extra space)
              (Space.first_measurable _ extra)))
          (Space.pair_measurable
            (MeasurableMap.comp (Space.second_measurable extra space)
              (Space.first_measurable _ extra))
            (Space.second_measurable _ extra))))
  exact (lintegral_prod (estimator value) (proposal value) (proposalFinite.measure value)
      rowMeasurable).symm.trans
    (lintegral_prod_symm (estimator value) (proposal value) (estimatorFinite.measure value)
      (proposalFinite.measure value) rowMeasurable)

/-- A proposal reversible for `ξ`, followed by a fresh estimator draw, is
reversible for `ξ ⊗ m`. The estimator draws at the pair's two values enter the
joint symmetrically, so the swap moves only the value pair. -/
theorem extended_reversible {reference : Measure space} {proposal : Kernel space space}
    {proposalFinite : Kernel.IsSFinite proposal}
    (reversible : DetailedBalance reference proposal proposalFinite)
    {estimator : Kernel space extra} (estimatorFinite : Kernel.IsSFinite estimator) :
    DetailedBalance (reference.semiproduct estimator estimatorFinite)
      (extendedProposal proposal estimator estimatorFinite)
      (extendedProposalFinite proposalFinite estimatorFinite) := by
  unfold DetailedBalance
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  have swappedMeasurable := measurable.comp
    (Space.swap_measurable (Space.product space extra) (Space.product space extra))
  have pairMeasurable := estimator_pair_measurable estimatorFinite measurable
  rw [lintegral_map _ _ _ measurable,
    lintegral_extended_joint proposalFinite estimatorFinite swappedMeasurable,
    lintegral_extended_joint proposalFinite estimatorFinite measurable]
  have exchanged : ∀ pair : α × α,
      (lintegral (estimator pair.1) fun current =>
        lintegral (estimator pair.2) fun next =>
          function ((pair.2, next), (pair.1, current))) =
        lintegral (estimator pair.2) fun next =>
          lintegral (estimator pair.1) fun current =>
            function ((pair.2, next), (pair.1, current)) := by
    intro pair
    have rowMeasurable : ENNRealMeasurable (Space.product extra extra)
        (fun point => function ((pair.2, point.2), (pair.1, point.1))) :=
      measurable.comp
        (Space.pair_measurable
          (Space.pair_measurable (MeasurableMap.constant _ space pair.2)
            (Space.second_measurable extra extra))
          (Space.pair_measurable (MeasurableMap.constant _ space pair.1)
            (Space.first_measurable extra extra)))
    exact (lintegral_prod (estimator pair.1) (estimator pair.2)
        (estimatorFinite.measure pair.2) rowMeasurable).symm.trans
      (lintegral_prod_symm (estimator pair.1) (estimator pair.2)
        (estimatorFinite.measure pair.1) (estimatorFinite.measure pair.2) rowMeasurable)
  rw [lintegral_congr _ exchanged,
    ← lintegral_map _ (fun pair : α × α => (pair.2, pair.1))
      (Space.swap_measurable space space) pairMeasurable,
    reversible]

/-! ### The pseudo-marginal chain -/

/-- Pseudo-marginal Metropolis–Hastings: propose a value and a fresh auxiliary,
and accept by the Metropolis test on the estimates read at the two states. -/
@[expose] noncomputable def pseudoMarginalKernel (proposal : Kernel space space)
    (proposalFinite : Kernel.IsSFinite proposal) (estimator : Kernel space extra)
    (estimatorFinite : Kernel.IsSFinite estimator) (estimate : α × υ → NNReal)
    (estimateMeasurable : MeasurableMap (Space.product space extra) weightSpace estimate) :
    Kernel (Space.product space extra) (Space.product space extra) :=
  mhKernel (extendedProposal proposal estimator estimatorFinite)
    (extendedProposalFinite proposalFinite estimatorFinite)
    (metropolisAccept fun point => NNReal.toReal (estimate point))
    (metropolisAccept_measurable (MeasurableMap.comp weight_toReal_measurable estimateMeasurable))

/-- The pseudo-marginal chain leaves the extended target invariant, for any
Markov proposal reversible for the reference and any Markov estimator. The
estimate needs no mean. -/
theorem pseudoMarginalKernel_invariant {reference : Measure space} {proposal : Kernel space space}
    {proposalFinite : Kernel.IsSFinite proposal}
    (proposalMarkov : ∀ input, Measure.IsProbability (proposal input))
    (reversible : DetailedBalance reference proposal proposalFinite)
    {estimator : Kernel space extra} {estimatorFinite : Kernel.IsSFinite estimator}
    (estimatorMarkov : ∀ input, Measure.IsProbability (estimator input))
    {estimate : α × υ → NNReal}
    (estimateMeasurable : MeasurableMap (Space.product space extra) weightSpace estimate) :
    KernelInvariant (extendedTarget reference estimator estimatorFinite estimate)
      (pseudoMarginalKernel proposal proposalFinite estimator estimatorFinite estimate
        estimateMeasurable) := by
  have target : extendedTarget reference estimator estimatorFinite estimate =
      (reference.semiproduct estimator estimatorFinite).withDensity
        (fun point => ENNReal.ofReal (NNReal.toReal (estimate point))) := by
    rw [extendedTarget]
    congr 1
    funext point
    exact (ENNReal.ofReal_toReal_finite (estimate point)).symm
  rw [target]
  exact metropolis_invariant (reference.semiproduct estimator estimatorFinite)
    (extendedProposalFinite proposalFinite estimatorFinite)
    (extendedProposal_markov proposalMarkov estimatorFinite estimatorMarkov)
    (extended_reversible reversible estimatorFinite)
    (MeasurableMap.comp weight_toReal_measurable estimateMeasurable)

end

end Problib.Inference
