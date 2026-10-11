module

public import Problib.Inference.Involutive
public import Problib.Inference.MetropolisHastings

set_option autoImplicit false

/-! Metropolis–Hastings balance from the symmetrized forward flux.

The strict test on the pair and its swap balances any step whose joint law has
a density against its own symmetrization (`mh_flux_invariant`). A target and
proposal with densities against one reference give the Hastings ratio as that
test (`hastings_invariant`). Neither needs a reversible proposal. -/

namespace Problib.Inference

open Problib.Measure Problib.Real Problib.Real.Construction
open Problib.Measure.Real (Carrier borel ofReal_measurable)

universe u
variable {α : Type u} {space : Space α}

public section

/-- Metropolis–Hastings balances the target against the symmetrized forward
flux. The proposal need not be reversible. -/
theorem mh_flux_detailed_balance
    (target : Measure space) (proposal : Kernel space space)
    (proposalFinite : Kernel.IsSFinite proposal)
    {density : α × α → Carrier}
    (densityMeasurable : MeasurableMap (Space.product space space) borel density)
    (represents : Measure.IsDensity
      (target.semiproduct proposal proposalFinite)
      (Measure.add (target.semiproduct proposal proposalFinite)
        ((target.semiproduct proposal proposalFinite).map swap
          (Space.swap_measurable space space)))
      (fun pair => ENNReal.ofReal (density pair))) :
    DetailedBalance target
      (mhKernel proposal proposalFinite (involutiveAccept swap density)
        (involutiveAccept_measurable swap
          (Space.swap_measurable space space) densityMeasurable))
      (mhKernelSFinite proposalFinite
        (involutiveAccept_measurable swap
          (Space.swap_measurable space space) densityMeasurable)) := by
  apply mh_detailed_balance target proposalFinite
    (involutiveAccept_measurable swap
      (Space.swap_measurable space space) densityMeasurable)
  have referenceInvariant := symmetrized_map_involution
    (target.semiproduct proposal proposalFinite) swap
    (Space.swap_measurable space space) (by intro pair; cases pair; rfl)
  exact accepted_symmetric_of_balance _ _ swap
    (Space.swap_measurable space space) referenceInvariant
    (ofReal_measurable.comp densityMeasurable)
    (involutiveAccept_measurable swap
      (Space.swap_measurable space space) densityMeasurable)
    represents.eq_withDensity
    (involutiveAccept_balanced swap
      (by intro pair; cases pair; rfl) density)

/-- The Metropolis–Hastings step leaves the target invariant without a
reversible-proposal premise. -/
theorem mh_flux_invariant
    (target : Measure space) (proposal : Kernel space space)
    (proposalFinite : Kernel.IsSFinite proposal)
    (proposalMarkov : ∀ input, Measure.IsProbability (proposal input))
    {density : α × α → Carrier}
    (densityMeasurable : MeasurableMap (Space.product space space) borel density)
    (represents : Measure.IsDensity
      (target.semiproduct proposal proposalFinite)
      (Measure.add (target.semiproduct proposal proposalFinite)
        ((target.semiproduct proposal proposalFinite).map swap
          (Space.swap_measurable space space)))
      (fun pair => ENNReal.ofReal (density pair))) :
    KernelInvariant target
      (mhKernel proposal proposalFinite (involutiveAccept swap density)
        (involutiveAccept_measurable swap
          (Space.swap_measurable space space) densityMeasurable)) := by
  exact detailed_balance_invariant
    (mhKernel_markov proposalFinite proposalMarkov
      (involutiveAccept_measurable swap
        (Space.swap_measurable space space) densityMeasurable)
      (involutiveAccept_le_one swap density))
    (mh_flux_detailed_balance target proposal proposalFinite
      densityMeasurable represents)

/-- A target and a proposal with densities against one reference have a joint
law with density `weight x · proposalDensity (x, y)` against the reference's
product with itself. -/
private theorem semiproduct_density
    (reference : Measure space) (referenceFinite : Measure.SFinite reference)
    {weight : α → ENNReal} (weightMeasurable : ENNRealMeasurable space weight)
    (proposal : Kernel space space) (proposalFinite : Kernel.IsSFinite proposal)
    {proposalDensity : α × α → ENNReal}
    (proposalDensityMeasurable :
      ENNRealMeasurable (Space.product space space) proposalDensity)
    (proposalRepresents : ∀ input, proposal input =
      reference.withDensity (fun output => proposalDensity (input, output))) :
    (reference.withDensity weight).semiproduct proposal proposalFinite =
      (Measure.prod reference reference referenceFinite).withDensity
        (fun pair => ENNReal.mul (proposalDensity pair) (weight pair.1)) := by
  have joint : reference.semiproduct proposal proposalFinite =
      (Measure.prod reference reference referenceFinite).withDensity
        proposalDensity := by
    apply Measure.ext
    intro set setMeasurable
    let indicator : α × α → ENNReal := ennrealIndicator set fun _ => ENNReal.one
    have indicatorMeasurable :
        ENNRealMeasurable (Space.product space space) indicator :=
      ENNRealMeasurable.indicator setMeasurable (ENNRealMeasurable.constant _ _)
    rw [apply_eq_lintegral_indicator _ setMeasurable,
      apply_eq_lintegral_indicator _ setMeasurable,
      lintegral_semiproduct _ _ _ indicatorMeasurable,
      lintegral_withDensity _ proposalDensityMeasurable indicatorMeasurable,
      lintegral_prod _ _ _
        (ENNRealMeasurable.mul proposalDensityMeasurable indicatorMeasurable)]
    apply lintegral_congr
    intro input
    rw [proposalRepresents input,
      lintegral_withDensity _
        (proposalDensityMeasurable.comp (Kernel.pair_left_measurable input))
        (indicatorMeasurable.comp (Kernel.pair_left_measurable input))]
  rw [Measure.semiproduct_withDensity_left _ weightMeasurable, joint,
    Measure.withDensity_withDensity _ proposalDensityMeasurable
      (weightMeasurable.comp (Space.first_measurable _ _))]

/-- The Hastings test. When the target has density `weight` and the proposal
has density `proposalDensity` against one s-finite reference, the strict test
on the forward flux `weight x · proposalDensity (x, y)` puts the step in
detailed balance with the target. The proposal need not be reversible. -/
theorem hastings_detailed_balance
    (reference : Measure space) (referenceFinite : Measure.SFinite reference)
    {weight : α → ENNReal} (weightMeasurable : ENNRealMeasurable space weight)
    (proposal : Kernel space space) (proposalFinite : Kernel.IsSFinite proposal)
    {proposalDensity : α × α → ENNReal}
    (proposalDensityMeasurable :
      ENNRealMeasurable (Space.product space space) proposalDensity)
    (proposalRepresents : ∀ input, proposal input =
      reference.withDensity (fun output => proposalDensity (input, output)))
    {flux : α × α → Carrier}
    (fluxMeasurable : MeasurableMap (Space.product space space) borel flux)
    (fluxEquation : ∀ pair, ENNReal.ofReal (flux pair) =
      ENNReal.mul (proposalDensity pair) (weight pair.1)) :
    DetailedBalance (reference.withDensity weight)
      (mhKernel proposal proposalFinite (involutiveAccept swap flux)
        (involutiveAccept_measurable swap
          (Space.swap_measurable space space) fluxMeasurable))
      (mhKernelSFinite proposalFinite
        (involutiveAccept_measurable swap
          (Space.swap_measurable space space) fluxMeasurable)) := by
  apply mh_detailed_balance _ proposalFinite
    (involutiveAccept_measurable swap
      (Space.swap_measurable space space) fluxMeasurable)
  have represents : (reference.withDensity weight).semiproduct proposal
      proposalFinite =
      (Measure.prod reference reference referenceFinite).withDensity
        (fun pair => ENNReal.ofReal (flux pair)) := by
    rw [semiproduct_density reference referenceFinite weightMeasurable
      proposal proposalFinite proposalDensityMeasurable proposalRepresents]
    exact congrArg _ (funext fun pair => (fluxEquation pair).symm)
  exact accepted_symmetric_of_balance _ _ swap
    (Space.swap_measurable space space)
    (Measure.prod_swap referenceFinite referenceFinite)
    (ofReal_measurable.comp fluxMeasurable)
    (involutiveAccept_measurable swap
      (Space.swap_measurable space space) fluxMeasurable)
    represents
    (involutiveAccept_balanced swap (by intro pair; cases pair; rfl) flux)

/-- The Hastings step leaves its target invariant for any Markov proposal with
a reference density. -/
theorem hastings_invariant
    (reference : Measure space) (referenceFinite : Measure.SFinite reference)
    {weight : α → ENNReal} (weightMeasurable : ENNRealMeasurable space weight)
    (proposal : Kernel space space) (proposalFinite : Kernel.IsSFinite proposal)
    (proposalMarkov : ∀ input, Measure.IsProbability (proposal input))
    {proposalDensity : α × α → ENNReal}
    (proposalDensityMeasurable :
      ENNRealMeasurable (Space.product space space) proposalDensity)
    (proposalRepresents : ∀ input, proposal input =
      reference.withDensity (fun output => proposalDensity (input, output)))
    {flux : α × α → Carrier}
    (fluxMeasurable : MeasurableMap (Space.product space space) borel flux)
    (fluxEquation : ∀ pair, ENNReal.ofReal (flux pair) =
      ENNReal.mul (proposalDensity pair) (weight pair.1)) :
    KernelInvariant (reference.withDensity weight)
      (mhKernel proposal proposalFinite (involutiveAccept swap flux)
        (involutiveAccept_measurable swap
          (Space.swap_measurable space space) fluxMeasurable)) :=
  detailed_balance_invariant
    (mhKernel_markov proposalFinite proposalMarkov
      (involutiveAccept_measurable swap
        (Space.swap_measurable space space) fluxMeasurable)
      (involutiveAccept_le_one swap flux))
    (hastings_detailed_balance reference referenceFinite weightMeasurable
      proposal proposalFinite proposalDensityMeasurable proposalRepresents
      fluxMeasurable fluxEquation)

end

end Problib.Inference
