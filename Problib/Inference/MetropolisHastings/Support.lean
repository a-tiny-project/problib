module

public import Problib.Inference.MetropolisHastings
public import Problib.Measure.Additive.AbsoluteContinuity
public import Problib.Measure.Integral.Lebesgue.Zero

set_option autoImplicit false

/-! Dominated moves.

A step has dominated moves for a target when, from every state, it splits into
an accepted part that the target dominates and a holding probability at that
state (`DominatedMoves`). The split is asked of every state, not of almost every
state, because a chain started anywhere must reach the target's support.

A Metropolis–Hastings step always splits into its accepted proposals and its
rejected mass (`mh_decomposition`). With a proposal density and a target
density, the accepted part is dominated as soon as acceptance times proposal
density vanishes wherever the target density does, from every state
(`accepted_dominated_of_density`). The strict Metropolis test meets that premise
pointwise for a nonnegative weight: `u·c(x) < c(y)` fails whenever `c(y) ≤ 0 ≤
c(x)` (`metropolisAccept_eq_zero`, `metropolis_dominated`). A negative current
weight can accept a move to a zero-weight state, so the sign premise stays. -/

namespace Problib.Inference

open Problib.Real Problib.Measure

universe u

variable {α : Type u} {space : Space α}

public section

/-- From every state, the step splits into an accepted part that the target
dominates and a holding probability at that state. The existential keeps the
witnesses out of a Prop-valued structure. -/
@[expose] def DominatedMoves (kernel : Kernel space space) (target : Measure space) : Prop :=
  ∃ (accepted : Kernel space space) (holding : α → ENNReal),
    ENNRealMeasurable space holding ∧
    (∀ input, ENNReal.le (holding input) ENNReal.one) ∧
    (∀ input, kernel input =
      Measure.add (accepted input)
        (Measure.smul (holding input) (Measure.dirac space input))) ∧
    (∀ input, Measure.AbsolutelyContinuous (accepted input) target)

/-- The accepted part of a Metropolis–Hastings step: the proposal reweighted by
its acceptance. -/
@[expose] noncomputable def mhAccepted (proposal : Kernel space space)
    (proposalFinite : Kernel.IsSFinite proposal) (accept : α × α → ENNReal)
    (acceptMeasurable : ENNRealMeasurable (Space.product space space) accept) :
    Kernel space space :=
  proposal.withDensity proposalFinite (fun input output => accept (input, output))
    acceptMeasurable

/-- The probability that a Metropolis–Hastings step rejects its proposal. -/
@[expose] noncomputable def mhHolding (proposal : Kernel space space)
    (accept : α × α → ENNReal) (input : α) : ENNReal :=
  lintegral (proposal input) (fun output => ENNReal.sub ENNReal.one (accept (input, output)))

theorem mhHolding_measurable (proposal : Kernel space space)
    (proposalFinite : Kernel.IsSFinite proposal) (accept : α × α → ENNReal)
    (acceptMeasurable : ENNRealMeasurable (Space.product space space) accept) :
    ENNRealMeasurable space (mhHolding proposal accept) :=
  Kernel.lintegral_measurable_joint proposal proposalFinite
    (function := fun input output => ENNReal.sub ENNReal.one (accept (input, output)))
    (ENNRealMeasurable.sub (ENNRealMeasurable.constant _ _) acceptMeasurable)

/-- Against a probability proposal, the rejected mass is at most one. -/
theorem mhHolding_le_one {proposal : Kernel space space}
    (markov : ∀ input, Measure.IsProbability (proposal input))
    (accept : α × α → ENNReal) (input : α) :
    ENNReal.le (mhHolding proposal accept input) ENNReal.one := by
  have bound := lintegral_mono (proposal input)
    (lower := fun output => ENNReal.sub ENNReal.one (accept (input, output)))
    (upper := fun _ => ENNReal.one) (fun _ => ENNReal.sub_le_self _ _)
  rwa [lintegral_const, (markov input).univ_eq_one, ENNReal.one_mul] at bound

/-- The accepted part of an event is the acceptance integrated over proposals
into it. -/
theorem mhAccepted_apply (proposal : Kernel space space)
    (proposalFinite : Kernel.IsSFinite proposal) (accept : α × α → ENNReal)
    (acceptMeasurable : ENNRealMeasurable (Space.product space space) accept)
    (input : α) {event : Set α} (eventMeasurable : space.Measurable event) :
    mhAccepted proposal proposalFinite accept acceptMeasurable input event =
      lintegral (proposal input) (fun proposed =>
        ENNReal.mul (accept (input, proposed))
          (ennrealIndicator event (fun _ => ENNReal.one) proposed)) := by
  rw [apply_eq_lintegral_indicator _ eventMeasurable, mhAccepted,
    Kernel.lintegral_withDensity _ _ _ _
      (ENNRealMeasurable.indicator eventMeasurable (ENNRealMeasurable.constant _ _))]

/-- A Metropolis–Hastings step is its accepted proposals plus its rejected mass
at the current state. -/
theorem mh_decomposition (proposal : Kernel space space)
    (proposalFinite : Kernel.IsSFinite proposal) (accept : α × α → ENNReal)
    (acceptMeasurable : ENNRealMeasurable (Space.product space space) accept)
    (input : α) :
    mhKernel proposal proposalFinite accept acceptMeasurable input =
      Measure.add (mhAccepted proposal proposalFinite accept acceptMeasurable input)
        (Measure.smul (mhHolding proposal accept input) (Measure.dirac space input)) := by
  apply Measure.ext
  intro event eventMeasurable
  have indicatorMeasurable : ENNRealMeasurable space
      (ennrealIndicator event fun _ => ENNReal.one) :=
    ENNRealMeasurable.indicator eventMeasurable (ENNRealMeasurable.constant _ _)
  have acceptSection : ENNRealMeasurable space (fun proposed => accept (input, proposed)) :=
    acceptMeasurable.comp (Kernel.pair_left_measurable input)
  have rejectSection : ENNRealMeasurable space
      (fun proposed => ENNReal.sub ENNReal.one (accept (input, proposed))) :=
    (ENNRealMeasurable.sub (ENNRealMeasurable.constant _ ENNReal.one) acceptMeasurable).comp
      (Kernel.pair_left_measurable input)
  rw [Measure.add_apply_measurable _ _ eventMeasurable,
    Measure.smul_apply_measurable _ _ eventMeasurable,
    mhAccepted_apply _ _ _ _ _ eventMeasurable,
    apply_eq_lintegral_indicator (Measure.dirac space input) eventMeasurable,
    lintegral_dirac _ _ indicatorMeasurable,
    apply_eq_lintegral_indicator (mhKernel proposal proposalFinite accept acceptMeasurable input)
      eventMeasurable,
    lintegral_mhKernel _ _ _ _ _ indicatorMeasurable,
    lintegral_add _ (ENNRealMeasurable.mul acceptSection indicatorMeasurable)
      (ENNRealMeasurable.mul rejectSection (ENNRealMeasurable.constant _ _))]
  congr 1
  unfold mhHolding
  rw [ENNReal.mul_comm, ← lintegral_smul _ _ rejectSection]
  apply lintegral_congr
  intro proposed
  exact ENNReal.mul_comm _ _

/-- Densities make the accepted part dominated. The proposal from each state
has a density against a reference, the target has a density against the same
reference, and from every state acceptance times proposal density vanishes
reference-almost everywhere on the target's zero set. -/
theorem accepted_dominated_of_density (proposal : Kernel space space)
    (proposalFinite : Kernel.IsSFinite proposal)
    (proposalMarkov : ∀ input, Measure.IsProbability (proposal input))
    (reference : Measure space) (proposalDensity : α → α → ENNReal)
    (proposalDensityMeasurable : ∀ input, ENNRealMeasurable space (proposalDensity input))
    (proposalRepresents : ∀ input,
      proposal input = reference.withDensity (proposalDensity input))
    (weight : α → ENNReal) (weightMeasurable : ENNRealMeasurable space weight)
    (target : Measure space) (targetRepresents : target = reference.withDensity weight)
    (accept : α × α → ENNReal)
    (acceptMeasurable : ENNRealMeasurable (Space.product space space) accept)
    (zeroTarget : ∀ input, reference.AE (fun output =>
      weight output = ENNReal.zero →
        ENNReal.mul (accept (input, output)) (proposalDensity input output) = ENNReal.zero)) :
    DominatedMoves (mhKernel proposal proposalFinite accept acceptMeasurable) target := by
  refine ⟨mhAccepted proposal proposalFinite accept acceptMeasurable, mhHolding proposal accept,
    mhHolding_measurable proposal proposalFinite accept acceptMeasurable,
    mhHolding_le_one proposalMarkov accept,
    mh_decomposition proposal proposalFinite accept acceptMeasurable, ?_⟩
  intro input event eventMeasurable targetNull
  have indicatorMeasurable : ENNRealMeasurable space
      (ennrealIndicator event fun _ => ENNReal.one) :=
    ENNRealMeasurable.indicator eventMeasurable (ENNRealMeasurable.constant _ _)
  have acceptSection : ENNRealMeasurable space (fun proposed => accept (input, proposed)) :=
    acceptMeasurable.comp (Kernel.pair_left_measurable input)
  rw [targetRepresents, apply_eq_lintegral_indicator _ eventMeasurable,
    lintegral_withDensity _ weightMeasurable indicatorMeasurable] at targetNull
  have weightNull := ae_zero_of_lintegral_eq_zero
    (ENNRealMeasurable.mul weightMeasurable indicatorMeasurable) targetNull
  rw [mhAccepted_apply _ _ _ _ _ eventMeasurable, proposalRepresents input,
    lintegral_withDensity _ (proposalDensityMeasurable input)
      (ENNRealMeasurable.mul acceptSection indicatorMeasurable)]
  apply lintegral_eq_zero_of_ae_zero
  apply (weightNull.and (zeroTarget input)).mono
  intro output ⟨outsideSupport, acceptNull⟩
  classical
  by_cases member : event output
  · simp only [ennrealIndicator, ennrealPiecewise, member, ite_true, ENNReal.mul_one]
      at outsideSupport ⊢
    rw [ENNReal.mul_comm]
    exact acceptNull outsideSupport
  · simp only [ennrealIndicator, ennrealPiecewise, member, ite_false, ENNReal.mul_zero]

section Metropolis

open Problib.Real.Construction
open Problib.Measure.Real (Carrier UnitInterval borel ofReal_measurable uniform01)

/-- From a nonnegative weight, the strict test never accepts a move to a weight
at most zero. -/
theorem metropolisAccept_eq_zero {weight : α → Carrier} {pair : α × α}
    (current : Dedekind.le Dedekind.zero (weight pair.1))
    (proposed : Dedekind.le (weight pair.2) Dedekind.zero) :
    metropolisAccept weight pair = ENNReal.zero := by
  unfold metropolisAccept
  have empty : (fun u : UnitInterval =>
      Dedekind.lt (Dedekind.mul u.val (weight pair.1)) (weight pair.2)) = Set.empty := by
    apply Set.ext
    intro u
    refine ⟨fun less => ?_, fun member => False.elim member⟩
    have scaled := Dedekind.mul_le_mul_nonnegative_right u.property.1 current
    rw [Dedekind.zero_mul] at scaled
    exact Dedekind.lt_irrefl _
      (Dedekind.lt_of_le_of_lt scaled (Dedekind.lt_of_lt_of_le less proposed))
  rw [empty]
  exact uniform01.toOuterMeasure.empty

/-- Every Metropolis step with a proposal density and a nonnegative weight has
dominated moves for the weighted reference. -/
theorem metropolis_dominated (proposal : Kernel space space)
    (proposalFinite : Kernel.IsSFinite proposal)
    (proposalMarkov : ∀ input, Measure.IsProbability (proposal input))
    (reference : Measure space) (proposalDensity : α → α → ENNReal)
    (proposalDensityMeasurable : ∀ input, ENNRealMeasurable space (proposalDensity input))
    (proposalRepresents : ∀ input,
      proposal input = reference.withDensity (proposalDensity input))
    {weight : α → Carrier} (weightMeasurable : MeasurableMap space borel weight)
    (nonnegative : ∀ state, Dedekind.le Dedekind.zero (weight state)) :
    DominatedMoves
      (mhKernel proposal proposalFinite (metropolisAccept weight)
        (metropolisAccept_measurable weightMeasurable))
      (reference.withDensity fun state => ENNReal.ofReal (weight state)) := by
  apply accepted_dominated_of_density proposal proposalFinite proposalMarkov reference
    proposalDensity proposalDensityMeasurable proposalRepresents
    (fun state => ENNReal.ofReal (weight state)) (ofReal_measurable.comp weightMeasurable) _ rfl
  intro input
  apply Measure.ae_of_forall
  intro output zero
  rw [metropolisAccept_eq_zero (pair := (input, output)) (nonnegative input)
    (ENNReal.ofReal_eq_zero_iff.mp zero), ENNReal.zero_mul]

end Metropolis

end

end Problib.Inference
