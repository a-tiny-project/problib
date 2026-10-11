module

public import Problib.Inference.PseudoMarginal
public import Problib.Inference.MetropolisHastings.Flux
set_option autoImplicit false

/-! The Hastings form of pseudo-marginal Metropolis–Hastings.

A proposal with a density `q(x, x')` against the reference needs no
reversibility. The extended proposal then has density `q(x, x')` against
`ξ ⊗ m`, because the fresh auxiliary is drawn from `m` itself
(`extendedProposal_represents`). The Hastings test on the extended space, with
forward flux `q(x, x') p̂(x, u)`, leaves the extended target invariant
(`pseudo_marginal_hastings_invariant`). This is `hastings_invariant` read on
the pair `(x, u)`. -/

namespace Problib.Inference

open Problib.Real Problib.Measure
open Problib.Measure.Real (Carrier borel)

universe u v

variable {α : Type u} {υ : Type v} {space : Space α} {extra : Space υ}

public section

/-- A proposal with density `q(x, x')` against the reference makes the extended
proposal from `(x, u)` have density `q(x, x')` against `ξ ⊗ m`. -/
theorem extendedProposal_represents {reference : Measure space}
    {proposal : Kernel space space} {proposalDensity : α × α → ENNReal}
    (proposalDensityMeasurable :
      ENNRealMeasurable (Space.product space space) proposalDensity)
    (proposalRepresents : ∀ input, proposal input =
      reference.withDensity (fun output => proposalDensity (input, output)))
    (estimator : Kernel space extra) (estimatorFinite : Kernel.IsSFinite estimator)
    (point : α × υ) :
    extendedProposal proposal estimator estimatorFinite point =
      (reference.semiproduct estimator estimatorFinite).withDensity
        (fun output => proposalDensity (point.1, output.1)) := by
  rw [extendedProposal_apply, proposalRepresents point.1,
    Measure.semiproduct_withDensity_left _
      (proposalDensityMeasurable.comp (Kernel.pair_left_measurable point.1))]

/-- Pseudo-marginal Metropolis–Hastings with the Hastings test leaves the
extended target invariant, for any Markov proposal with a density against the
s-finite reference and any Markov estimator. -/
theorem pseudo_marginal_hastings_invariant {reference : Measure space}
    (referenceFinite : Measure.SFinite reference) {proposal : Kernel space space}
    {proposalFinite : Kernel.IsSFinite proposal}
    (proposalMarkov : ∀ input, Measure.IsProbability (proposal input))
    {proposalDensity : α × α → ENNReal}
    (proposalDensityMeasurable :
      ENNRealMeasurable (Space.product space space) proposalDensity)
    (proposalRepresents : ∀ input, proposal input =
      reference.withDensity (fun output => proposalDensity (input, output)))
    {estimator : Kernel space extra} {estimatorFinite : Kernel.IsSFinite estimator}
    (estimatorMarkov : ∀ input, Measure.IsProbability (estimator input))
    {estimate : α × υ → NNReal}
    (estimateMeasurable : MeasurableMap (Space.product space extra) weightSpace estimate)
    {flux : (α × υ) × (α × υ) → Carrier}
    (fluxMeasurable : MeasurableMap
      (Space.product (Space.product space extra) (Space.product space extra)) borel flux)
    (fluxEquation : ∀ pair, ENNReal.ofReal (flux pair) =
      ENNReal.mul (proposalDensity (pair.1.1, pair.2.1)) (ENNReal.finite (estimate pair.1))) :
    KernelInvariant (extendedTarget reference estimator estimatorFinite estimate)
      (mhKernel (extendedProposal proposal estimator estimatorFinite)
        (extendedProposalFinite proposalFinite estimatorFinite) (involutiveAccept swap flux)
        (involutiveAccept_measurable swap
          (Space.swap_measurable (Space.product space extra) (Space.product space extra))
          fluxMeasurable)) :=
  hastings_invariant (reference.semiproduct estimator estimatorFinite)
    (referenceFinite.semiproduct estimatorFinite)
    (finite_weight_measurable estimateMeasurable)
    (extendedProposal proposal estimator estimatorFinite)
    (extendedProposalFinite proposalFinite estimatorFinite)
    (extendedProposal_markov proposalMarkov estimatorFinite estimatorMarkov)
    (proposalDensityMeasurable.comp
      (Space.pair_measurable
        (MeasurableMap.comp (Space.first_measurable space extra) (Space.first_measurable _ _))
        (MeasurableMap.comp (Space.first_measurable space extra) (Space.second_measurable _ _))))
    (extendedProposal_represents proposalDensityMeasurable proposalRepresents estimator
      estimatorFinite)
    fluxMeasurable fluxEquation

end

end Problib.Inference
