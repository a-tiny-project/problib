module

public import Problib.Inference.Invariance
public import Problib.Measure.Kernel.Presentation
public import Problib.Measure.Kernel.Iteration.Lumping
public import Problib.Measure.Kernel.Iteration.Minorization
public import Problib.Measure.Kernel.TotalVariation
public import Problib.Measure.Integral.Lebesgue.Dominated
import Problib.Measure.Additive.Dirac

set_option autoImplicit false

/-!
# Presented chains

A presented chain runs a Markov chain on hidden states at each input and reads
its output through a return. Its output need not be a Markov chain. The chain
is presented-invariant-convergent for a target when some invariant state law
returns the target and, from every start state, the output law converges to
the target in total variation.

Convergence of a distance sequence is `Vanishes`: its upper limit is zero.
Total variation is bounded by one, so this is ordinary convergence to zero.

Internal convergence projects to the output with no lumpability, because a
pushforward cannot increase total variation (`projected_chain_converges`).
Convergence from every start state gives convergence from any start law whose
per-state distances are measurable (`mixed_converges`). The lower integral
bounds a mixture's distance without measurability, but the reverse Fatou
step needs it. When the output is itself a Markov chain (`Lumpable`), the
output chain converges from every output (`lumped_chain_converges`).
-/

namespace Problib.Inference

open Problib.Real Problib.Measure

universe u v w t

variable {α : Type u} {β : Type v} {source : Space α} {result : Space β}

public section

/-- A distance sequence vanishes when its upper limit is zero. -/
@[expose] def Vanishes (distance : Nat → ENNReal) : Prop :=
  ENNReal.limsup distance = ENNReal.zero

/-- A sequence below a vanishing sequence vanishes. -/
theorem vanishes_of_le {small large : Nat → ENNReal}
    (bounded : ∀ index, ENNReal.le (small index) (large index)) (vanishes : Vanishes large) :
    Vanishes small := by
  unfold Vanishes at vanishes ⊢
  apply ENNReal.le_antisymm _ (ENNReal.zero_le _)
  rw [← vanishes]
  apply ENNReal.le_iInf
  intro stage
  refine ENNReal.le_trans (ENNReal.iInf_le _ stage) ?_
  apply ENNReal.iSup_le
  intro offset
  exact ENNReal.le_trans (bounded (stage + offset))
    (ENNReal.le_iSup (fun position => large (stage + position)) offset)

/-- A Markov chain on hidden states at each input, with an initial law and a
return that reads the output off a state. -/
structure PresentedChain (source : Space α) (result : Space β) : Type (max u v (t + 1)) where
  State : Type t
  space : Space State
  initial : Kernel source space
  step : Kernel (Space.product source space) space
  ret : α × State → β
  measurable : MeasurableMap (Space.product source space) result ret
  markov : ∀ point, Measure.IsProbability (step point)
  initial_markov : ∀ input, Measure.IsProbability (initial input)

namespace PresentedChain

variable (chain : PresentedChain.{u, v, t} source result)

/-- The step at one input. -/
@[expose] noncomputable def stepAt (input : α) : Kernel chain.space chain.space :=
  chain.step.precomp (fun state => (input, state))
    (Kernel.pair_left_measurable (source := source) (target := chain.space) input)

/-- The return at one input. -/
@[expose] def retAt (input : α) : chain.State → β :=
  fun state => chain.ret (input, state)

theorem retAt_measurable (input : α) : MeasurableMap chain.space result (chain.retAt input) :=
  Kernel.section_measurable chain.measurable input

theorem stepAt_markov (input : α) (state : chain.State) :
    Measure.IsProbability (chain.stepAt input state) :=
  chain.markov (input, state)

/-- The law of one start state. -/
@[expose] noncomputable def point (state : chain.State) : Giry.Law chain.space :=
  ⟨Measure.dirac chain.space state, Measure.IsProbability.dirac chain.space state⟩

/-- The initial law at one input. -/
@[expose] def initialLaw (input : α) : Giry.Law chain.space :=
  ⟨chain.initial input, chain.initial_markov input⟩

/-- The state law after `count` steps from a start law. -/
@[expose] noncomputable def stateLaw (input : α) (start : Giry.Law chain.space) (count : Nat) :
    Giry.Law chain.space :=
  ⟨start.val.bind (Kernel.iterate (chain.stepAt input) count),
    start.property.bind _ (Kernel.iterate_isProbability _ (chain.stepAt_markov input) count)⟩

/-- The output law of a state law. -/
@[expose] noncomputable def image (input : α) (law : Giry.Law chain.space) : Giry.Law result :=
  ⟨law.val.map (chain.retAt input) (chain.retAt_measurable input),
    law.property.map (chain.retAt input) (chain.retAt_measurable input)⟩

/-- The output law after `count` steps from a start law. -/
@[expose] noncomputable def outputLaw (input : α) (start : Giry.Law chain.space) (count : Nat) :
    Giry.Law result :=
  chain.image input (chain.stateLaw input start count)

/-- The output kernel after `count` steps: iterate the states, then return. -/
@[expose] noncomputable def outputKernel (input : α) (count : Nat) : Kernel chain.space result :=
  (Kernel.iterate (chain.stepAt input) count).map (chain.retAt input) (chain.retAt_measurable input)

theorem outputKernel_markov (input : α) (count : Nat) (state : chain.State) :
    Measure.IsProbability (chain.outputKernel input count state) :=
  (Kernel.iterate_isProbability _ (chain.stepAt_markov input) count state).map
    (chain.retAt input) (chain.retAt_measurable input)

/-- From a start law, the output law is the start law bound to the output kernel. -/
theorem outputLaw_eq_bind (input : α) (start : Giry.Law chain.space) (count : Nat) :
    chain.outputLaw input start count =
      ⟨start.val.bind (chain.outputKernel input count),
        start.property.bind _ (chain.outputKernel_markov input count)⟩ :=
  Subtype.ext (Measure.map_bind _ _ _ _)

/-- From one state, the output law is the output kernel at that state. -/
theorem outputLaw_point (input : α) (state : chain.State) (count : Nat) :
    chain.outputLaw input (chain.point state) count =
      ⟨chain.outputKernel input count state, chain.outputKernel_markov input count state⟩ := by
  rw [outputLaw_eq_bind]
  exact Subtype.ext (Measure.dirac_bind state _)

end PresentedChain

/-- At every input, some invariant state law returns the target, and from
every start state the output law converges to the target in total
variation. -/
@[expose] def PresentedInvariantConvergent (target : Kernel source result)
    (chain : PresentedChain.{u, v, t} source result) : Prop :=
  ∀ input, ∃ stationary : Giry.Law chain.space,
    KernelInvariant stationary.val (chain.stepAt input) ∧
      (chain.image input stationary).val = target input ∧
        ∀ start, Vanishes (fun count =>
          Giry.Law.totalVariation (chain.outputLaw input (chain.point start) count)
            (chain.image input stationary))

/-- State-level convergence to an invariant law that returns the target projects
to the output, with no lumpability: a pushforward cannot increase total
variation. -/
theorem projected_chain_converges (chain : PresentedChain.{u, v, t} source result)
    (target : Kernel source result) (stationary : α → Giry.Law chain.space)
    (invariant : ∀ input, KernelInvariant (stationary input).val (chain.stepAt input))
    (presents : ∀ input, (chain.image input (stationary input)).val = target input)
    (converges : ∀ input start, Vanishes (fun count =>
      Giry.Law.totalVariation (chain.stateLaw input (chain.point start) count) (stationary input))) :
    PresentedInvariantConvergent target chain := by
  intro input
  refine ⟨stationary input, invariant input, presents input, fun start => ?_⟩
  exact vanishes_of_le
    (fun count => Giry.Law.totalVariation_map (chain.retAt input) (chain.retAt_measurable input)
      (chain.stateLaw input (chain.point start) count) (stationary input))
    (converges input start)

/-- Under a uniform minorization, total variation to an invariant law
vanishes from every start law. The contraction bound decays geometrically
across blocks, so its upper limit is below every positive tolerance. -/
theorem minorization_vanishes {σ : Type t} {space : Space σ}
    {kernel : Kernel space space} {steps : Nat} {weight : NNReal}
    {reference : Giry.Law space}
    (minor : Kernel.Minorization kernel steps weight reference)
    (π μ : Giry.Law space) (invariant : π.val.bind kernel = π.val) :
    Vanishes (fun count => Giry.Law.totalVariation
      ⟨μ.val.bind (Kernel.iterate kernel count),
        μ.property.bind (Kernel.iterate kernel count)
          (Kernel.iterate_isProbability kernel minor.markov count)⟩ π) := by
  apply ENNReal.le_antisymm _ (ENNReal.zero_le _)
  apply ENNReal.le_of_forall_positive_le_add
  intro tolerance positive
  rw [ENNReal.zero_add]
  rcases ENNReal.pow_eventually_lt (Kernel.minorization_decay_base_lt_one minor) positive with
    ⟨stage, small⟩
  refine ENNReal.le_trans (ENNReal.iInf_le _ (stage * steps)) (ENNReal.iSup_le fun offset => ?_)
  have quotient : stage ≤ (stage * steps + offset) / steps :=
    (Nat.le_div_iff_mul_le minor.stepsPositive).mpr (Nat.le_add_right _ _)
  have rate := Kernel.minorization_contraction minor π μ invariant (stage * steps + offset)
  have scaled := ENNReal.mul_le_mul_left (Giry.Law.totalVariation_le_one μ π)
    (ENNReal.pow (ENNReal.sub ENNReal.one (ENNReal.finite weight))
      ((stage * steps + offset) / steps))
  rw [ENNReal.mul_one] at scaled
  exact ENNReal.le_trans (ENNReal.le_trans rate scaled) (small _ quotient).left

/-- The chain read through a further return. The states, steps and initial law
stay, and the output is the return applied to the chain's output at the same
input. -/
@[expose] def PresentedChain.through {γ : Type w} {target : Space γ}
    (chain : PresentedChain.{u, v, t} source result) (ret : α × β → γ)
    (measurable : MeasurableMap (Space.product source result) target ret) :
    PresentedChain.{u, w, t} source target where
  State := chain.State
  space := chain.space
  initial := chain.initial
  step := chain.step
  ret := fun pair => ret (pair.1, chain.ret pair)
  measurable := MeasurableMap.comp measurable
    (Space.pair_measurable (Space.first_measurable source chain.space) chain.measurable)
  markov := chain.markov
  initial_markov := chain.initial_markov

/-- A chain that converges to a presentation's joint converges, read through
the presentation's return, to the presented kernel. The invariant state law is
the same, and a pushforward cannot increase total variation. -/
theorem through_converges {γ : Type w} {target : Space γ} {kernel : Kernel source target}
    {joint : Kernel source result} {ret : α × β → γ}
    {measurable : MeasurableMap (Space.product source result) target ret}
    (presents : Kernel.Presents kernel joint ret measurable)
    (chain : PresentedChain.{u, v, t} source result)
    (convergent : PresentedInvariantConvergent joint chain) :
    PresentedInvariantConvergent kernel (chain.through ret measurable) := by
  intro input
  obtain ⟨stationary, invariant, image, converges⟩ := convergent input
  have outer : MeasurableMap result target (fun point => ret (input, point)) :=
    Kernel.section_measurable measurable input
  have through : ∀ law : Giry.Law chain.space,
      (chain.through ret measurable).image input law =
        ⟨(chain.image input law).val.map (fun point => ret (input, point)) outer,
          (chain.image input law).property.map _ outer⟩ := fun law =>
    Subtype.ext (Measure.map_comp law.val (chain.retAt input) (fun point => ret (input, point))
      (chain.retAt_measurable input) outer).symm
  refine ⟨stationary, invariant, ?_, fun start => ?_⟩
  · rw [through]
    change (chain.image input stationary).val.map _ outer = kernel input
    rw [image]
    exact presents input
  · refine vanishes_of_le (fun count => ?_) (converges start)
    change ENNReal.le (Giry.Law.totalVariation
      ((chain.through ret measurable).image input (chain.stateLaw input (chain.point start) count))
      ((chain.through ret measurable).image input stationary)) _
    rw [through, through]
    exact Giry.Law.totalVariation_map _ outer _ _

/-- Convergence from every start state gives convergence from a start law,
once the per-state distances are measurable. The mixture's distance is at most
the average distance (`totalVariation_bind_le`), and the average vanishes by
the reverse Fatou lemma, bounded by one. -/
theorem mixed_converges (chain : PresentedChain.{u, v, t} source result)
    (target : Kernel source result) (targetMarkov : ∀ input, Measure.IsProbability (target input))
    (convergent : PresentedInvariantConvergent target chain) (input : α)
    (start : Giry.Law chain.space)
    (measurable : ∀ count, ENNRealMeasurable chain.space (fun state =>
      Giry.Law.totalVariation (chain.outputLaw input (chain.point state) count)
        ⟨target input, targetMarkov input⟩)) :
    Vanishes (fun count =>
      Giry.Law.totalVariation (chain.outputLaw input start count) ⟨target input, targetMarkov input⟩) := by
  obtain ⟨stationary, _, presents, converges⟩ := convergent input
  have same : chain.image input stationary = ⟨target input, targetMarkov input⟩ :=
    Subtype.ext presents
  rw [same] at converges
  let distance := fun count state =>
    Giry.Law.totalVariation (chain.outputLaw input (chain.point state) count)
      ⟨target input, targetMarkov input⟩
  have bound : ∀ count, ENNReal.le
      (Giry.Law.totalVariation (chain.outputLaw input start count) ⟨target input, targetMarkov input⟩)
      (lintegral start.val (distance count)) := by
    intro count
    rw [chain.outputLaw_eq_bind input start count]
    refine ENNReal.le_trans
      (Giry.Law.totalVariation_bind_le start (chain.outputKernel input count)
        (chain.outputKernel_markov input count) _)
      (lintegral_mono _ fun state => ?_)
    show ENNReal.le _ (Giry.Law.totalVariation (chain.outputLaw input (chain.point state) count) _)
    rw [chain.outputLaw_point input state count]
    exact ENNReal.le_refl _
  have fatou := limsup_le_lintegral_limsup start.val distance (fun _ => ENNReal.one)
    measurable (fun _ _ => Giry.Law.totalVariation_le_one _ _)
    (by
      rw [lintegral_const, start.property.univ_eq_one, ENNReal.one_mul]
      exact True.intro)
  have limits : (fun state => ENNReal.limsup (fun count => distance count state)) =
      fun _ => ENNReal.zero :=
    funext fun state => converges state
  rw [limits, lintegral_zero] at fatou
  exact vanishes_of_le bound (ENNReal.le_antisymm fatou (ENNReal.zero_le _))

/-- The chain converges from its initial law, under the same measurability. -/
theorem initialized_converges (chain : PresentedChain.{u, v, t} source result)
    (target : Kernel source result) (targetMarkov : ∀ input, Measure.IsProbability (target input))
    (convergent : PresentedInvariantConvergent target chain) (input : α)
    (measurable : ∀ count, ENNRealMeasurable chain.space (fun state =>
      Giry.Law.totalVariation (chain.outputLaw input (chain.point state) count)
        ⟨target input, targetMarkov input⟩)) :
    Vanishes (fun count =>
      Giry.Law.totalVariation (chain.outputLaw input (chain.initialLaw input) count)
        ⟨target input, targetMarkov input⟩) :=
  mixed_converges chain target targetMarkov convergent input (chain.initialLaw input) measurable

/-- The output of a presented chain is itself a Markov chain: one output step
depends on the state only through its output, and every output has a state law
that returns it. -/
structure Lumpable (chain : PresentedChain.{u, v, t} source result) : Type (max u v t) where
  outputStep : Kernel (Space.product source result) result
  output_markov : ∀ point, Measure.IsProbability (outputStep point)
  lumps : ∀ input, Kernel.Lumps (chain.stepAt input) (chain.retAt input)
    (chain.retAt_measurable input)
    (outputStep.precomp (fun output => (input, output))
      (Kernel.pair_left_measurable (source := source) (target := result) input))
  lift : Kernel (Space.product source result) chain.space
  lift_markov : ∀ point, Measure.IsProbability (lift point)
  lift_returns : ∀ input output,
    (lift (input, output)).map (chain.retAt input) (chain.retAt_measurable input) =
      Measure.dirac result output

namespace Lumpable

variable {chain : PresentedChain.{u, v, t} source result} (lumpable : Lumpable chain)

/-- The output step at one input. -/
@[expose] noncomputable def outputStepAt (input : α) : Kernel result result :=
  lumpable.outputStep.precomp (fun output => (input, output))
    (Kernel.pair_left_measurable (source := source) (target := result) input)

/-- The output chain's law after `count` steps from one output. -/
@[expose] noncomputable def outputChainLaw (input : α) (output : β) (count : Nat) :
    Giry.Law result :=
  ⟨Kernel.iterate (lumpable.outputStepAt input) count output,
    Kernel.iterate_isProbability _ (fun point => lumpable.output_markov (input, point)) count output⟩

/-- From one state, the presented chain's output law is the output chain's law
from that state's output. -/
theorem lumped_iterate (input : α) (state : chain.State) (count : Nat) :
    chain.outputLaw input (chain.point state) count =
      lumpable.outputChainLaw input (chain.retAt input state) count := by
  rw [chain.outputLaw_point input state count]
  exact Subtype.ext (Kernel.iterate_map_of_lumps (lumpable.lumps input) count state)

/-- Started from the lift of an output, the presented chain's output law is the
output chain's law from that output. -/
theorem lifted_output (input : α) (output : β) (count : Nat) :
    chain.outputLaw input ⟨lumpable.lift (input, output), lumpable.lift_markov (input, output)⟩ count =
      lumpable.outputChainLaw input output count := by
  rw [chain.outputLaw_eq_bind]
  apply Subtype.ext
  have kernels : chain.outputKernel input count =
      (Kernel.iterate (lumpable.outputStepAt input) count).precomp (chain.retAt input)
        (chain.retAt_measurable input) := by
    apply Kernel.ext
    intro state
    exact Kernel.iterate_map_of_lumps (lumpable.lumps input) count state
  show (lumpable.lift (input, output)).bind (chain.outputKernel input count) =
    Kernel.iterate (lumpable.outputStepAt input) count output
  rw [kernels, ← Measure.bind_map, lumpable.lift_returns input output, Measure.dirac_bind]

/-- A presented-invariant-convergent chain whose output lumps converges as an
output chain from every output, under the measurability of `mixed_converges`. -/
theorem lumped_chain_converges (target : Kernel source result)
    (targetMarkov : ∀ input, Measure.IsProbability (target input))
    (convergent : PresentedInvariantConvergent target chain) (input : α) (output : β)
    (measurable : ∀ count, ENNRealMeasurable chain.space (fun state =>
      Giry.Law.totalVariation (chain.outputLaw input (chain.point state) count)
        ⟨target input, targetMarkov input⟩)) :
    Vanishes (fun count =>
      Giry.Law.totalVariation (lumpable.outputChainLaw input output count)
        ⟨target input, targetMarkov input⟩) := by
  have mixed := mixed_converges chain target targetMarkov convergent input
    ⟨lumpable.lift (input, output), lumpable.lift_markov (input, output)⟩ measurable
  simpa only [lumpable.lifted_output input output] using mixed

end Lumpable

/-- A Markov chain on the output presents itself, with the output as the state. -/
@[expose] def PresentedChain.ofOutput (initial : Kernel source result)
    (step : Kernel (Space.product source result) result)
    (markov : ∀ point, Measure.IsProbability (step point))
    (initialMarkov : ∀ input, Measure.IsProbability (initial input)) :
    PresentedChain.{u, v, v} source result where
  State := β
  space := result
  initial := initial
  step := step
  ret := Prod.snd
  measurable := Space.second_measurable source result
  markov := markov
  initial_markov := initialMarkov

/-- A chain on the output lumps along its identity return. -/
@[expose] noncomputable def Lumpable.identity (initial : Kernel source result)
    (step : Kernel (Space.product source result) result)
    (markov : ∀ point, Measure.IsProbability (step point))
    (initialMarkov : ∀ input, Measure.IsProbability (initial input)) :
    Lumpable (PresentedChain.ofOutput initial step markov initialMarkov) where
  outputStep := step
  output_markov := markov
  lumps := fun _ _ => Measure.map_id _
  lift := Kernel.deterministic Prod.snd (Space.second_measurable source result)
  lift_markov := fun point => Measure.IsProbability.dirac result point.2
  lift_returns := fun _ _ => Measure.map_id _

end

end Problib.Inference
