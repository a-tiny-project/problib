import Problib.Inference.MetropolisHastings
import Problib.Measure.Kernel.Iteration.Finite

set_option autoImplicit false

/-! Minorization of a Metropolis–Hastings chain on a finite state space.

The finite theorem asks for one state that every state reaches and that is
aperiodic (`finite_accessible_aperiodic_minorization`). A Metropolis–Hastings
chain meets it from one-step facts about its proposal and weight. A target of
positive weight is aperiodic when the chain holds there, which the proposal
gives by holding itself or by proposing a smaller weight (`mh_hold_positive`).
Every state reaches the target when the proposal joins it to the target through
states of positive weight (`ProposalReach`), since each such proposal is
accepted with positive probability (`mh_move_positive`). The chain need not be
irreducible: a state of weight zero moves to any positive proposal, and no
positive state returns to it (`mh_finite_minorization`). -/

namespace Problib.Inference

open Problib.Real Problib.Measure
open Problib.Real.Construction
open Problib.Measure.Real (Carrier borel)

universe u

variable {α : Type u}

/-- The proposal joins `input` to `output` through proposals of positive
probability, each to a state of positive weight. -/
inductive ProposalReach {space : Space α} (proposal : Kernel space space)
    (weight : α → Carrier) : α → α → Prop
  | refl (point : α) : ProposalReach proposal weight point point
  | step {input middle output : α}
      (proposed : ENNReal.lt ENNReal.zero (proposal input (Set.singleton middle)))
      (positive : Dedekind.lt Dedekind.zero (weight middle))
      (rest : ProposalReach proposal weight middle output) :
      ProposalReach proposal weight input output

/-- A Metropolis–Hastings chain on a finite state space is minorized when a
target of positive weight holds and the proposal joins every state to it
through positive weights. -/
theorem mh_finite_minorization [DecidableEq α] (enumeration : List α)
    (listed : FiniteEnumeration enumeration)
    (proposal : Kernel (Space.discrete α) (Space.discrete α))
    (proposalFinite : Kernel.IsSFinite proposal)
    (proposalMarkov : ∀ state, Measure.IsProbability (proposal state))
    {weight : α → Carrier} (weightMeasurable : MeasurableMap (Space.discrete α) borel weight)
    (target : α) (positive : Dedekind.lt Dedekind.zero (weight target))
    (hold : ENNReal.lt ENNReal.zero (proposal target (Set.singleton target)) ∨
      ∃ point, ENNReal.lt ENNReal.zero (proposal target (Set.singleton point)) ∧
        Dedekind.lt (weight point) (weight target))
    (reach : ∀ input, ProposalReach proposal weight input target) :
    ∃ steps weight' reference,
      Kernel.Minorization
        (mhKernel proposal proposalFinite (metropolisAccept weight)
          (metropolisAccept_measurable weightMeasurable))
        steps weight' reference := by
  let kernel := mhKernel proposal proposalFinite (metropolisAccept weight)
    (metropolisAccept_measurable weightMeasurable)
  have markov : ∀ state, Measure.IsProbability (kernel state) :=
    mh_kernel_markov proposalFinite proposalMarkov (metropolisAccept_measurable weightMeasurable)
      (metropolisAccept_le_one weight)
  have path : ∀ {input output : α}, ProposalReach proposal weight input output →
      Kernel.Reaches kernel input output := by
    intro input output joined
    induction joined with
    | refl point => exact Kernel.reaches_refl kernel point
    | step proposed middlePositive _ rest =>
        exact Kernel.reaches_step kernel
          (mh_move_positive proposal proposalFinite weightMeasurable
            (Space.discrete_measurable _) proposed middlePositive) rest
  have accessible : ∀ input, Kernel.Reaches kernel input target :=
    fun input => path (reach input)
  have holds := mh_hold_positive proposal proposalFinite weightMeasurable
    (Space.discrete_measurable _) positive
    (hold.imp id fun ⟨point, proposed, smaller⟩ =>
      ⟨point, Space.discrete_measurable _, proposed, smaller⟩)
  exact Kernel.finite_accessible_aperiodic_minorization enumeration listed kernel markov target
    accessible (Kernel.aperiodicAt_of_hold kernel holds)

end Problib.Inference
