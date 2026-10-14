module

public import Problib.Inference.Presented
public import Problib.Measure.Kernel.Lumping
public import Problib.Measure.Kernel.Finite
public import Problib.Measure.Configuration.Shuffle

set_option autoImplicit false

/-!
# Lumping presented chains through a quotient

When each input's return is a quotient map and each input's step lumps along
it, the output of a presented chain is a Markov chain (`Lumpable.ofQuotient`).
The output step runs the lift, then one state step, then the return. It is
built as one composite kernel, so it is measurable jointly in the input and
the output. `Kernel.lumped` picks a representative per input and appears only
in the proof that the composite lumps.

For unordered outputs of a chain on lists, the lift is `symmetrize`: a
uniformly random ordering of the configuration. Forgetting the order returns
the configuration (`symmetrize_unorder`), so a chain on lists whose step lumps
along `unorder` is lumpable (`Lumpable.unordered`), and state-level
convergence projects to the unordered output (`unordered_chain_converges`).
-/

namespace Problib.Inference

open Problib.Real Problib.Measure

universe u v w t

variable {α : Type u} {β : Type v} {source : Space α} {result : Space β}

public section

namespace Lumpable

variable (chain : PresentedChain.{u, v, t} source result)

/-- Draw a state from the lift and keep the input beside it. -/
@[expose] noncomputable def liftStep (lift : Kernel (Space.product source result) chain.space)
    (liftMarkov : ∀ point, Measure.IsProbability (lift point)) :
    Kernel (Space.product source result) (Space.product source chain.space) :=
  (Kernel.attach lift (Kernel.IsSFinite.ofFiniteFibers fun point =>
    (liftMarkov point).to_finite)).map
    (fun pair => (pair.1.1, pair.2))
    (Space.pair_measurable
      (MeasurableMap.comp (Space.first_measurable _ _) (Space.first_measurable _ _))
      (Space.second_measurable _ _))

/-- One state step at the kept input, read through the return. -/
@[expose] noncomputable def returnStep :
    Kernel (Space.product source chain.space) result :=
  (Kernel.attach chain.step (Kernel.IsSFinite.ofFiniteFibers fun point =>
    (chain.markov point).to_finite)).map
    (fun pair => chain.ret (pair.1.1, pair.2))
    (MeasurableMap.comp chain.measurable
      (Space.pair_measurable
        (MeasurableMap.comp (Space.first_measurable _ _) (Space.first_measurable _ _))
        (Space.second_measurable _ _)))

theorem returnStep_apply (point : α × chain.State) :
    returnStep chain point = (chain.step point).map (fun state => chain.ret (point.1, state))
      (MeasurableMap.comp chain.measurable
        (Kernel.pair_left_measurable (source := source) (target := chain.space) point.1)) := by
  change ((chain.step point).map (fun state => (point, state))
      (Kernel.pair_left_measurable (source := Space.product source chain.space)
        (target := chain.space) point)).map
      (fun pair => chain.ret (pair.1.1, pair.2)) _ = _
  rw [Measure.map_comp]

theorem returnStep_at (input : α) :
    (returnStep chain).precomp (fun state => (input, state))
        (Kernel.pair_left_measurable (source := source) (target := chain.space) input) =
      (chain.stepAt input).map (chain.retAt input) (chain.retAt_measurable input) := by
  apply Kernel.ext
  intro state
  rw [Kernel.precomp_apply, Kernel.map_apply, returnStep_apply]
  rfl

theorem liftStep_apply (lift : Kernel (Space.product source result) chain.space)
    (liftMarkov : ∀ point, Measure.IsProbability (lift point)) (point : α × β) :
    liftStep chain lift liftMarkov point =
      (lift point).map (fun state => (point.1, state))
        (Kernel.pair_left_measurable (source := source) (target := chain.space) point.1) := by
  change ((lift point).map (fun state => (point, state))
      (Kernel.pair_left_measurable (source := Space.product source result)
        (target := chain.space) point)).map
      (fun pair => (pair.1.1, pair.2)) _ = _
  rw [Measure.map_comp]

theorem liftStep_bind (lift : Kernel (Space.product source result) chain.space)
    (liftMarkov : ∀ point, Measure.IsProbability (lift point)) (input : α) (output : β) :
    (liftStep chain lift liftMarkov (input, output)).bind (returnStep chain) =
      (lift (input, output)).bind
        ((chain.stepAt input).map (chain.retAt input) (chain.retAt_measurable input)) := by
  rw [liftStep_apply]
  dsimp only
  rw [Measure.bind_map, returnStep_at]

/-- A presented chain whose returns are quotient maps and whose steps lump
along them is lumpable, given a lift that each return undoes. -/
@[expose] noncomputable def ofQuotient
    (quotient : ∀ input, QuotientMap chain.space result (chain.retAt input))
    (lumps : ∀ input, (chain.stepAt input).LumpsAlong (chain.retAt input)
      (chain.retAt_measurable input))
    (lift : Kernel (Space.product source result) chain.space)
    (liftMarkov : ∀ point, Measure.IsProbability (lift point))
    (lifted : ∀ input output,
      (lift (input, output)).map (chain.retAt input) (chain.retAt_measurable input) =
        Measure.dirac result output) :
    Lumpable chain where
  outputStep := (liftStep chain lift liftMarkov).comp (returnStep chain)
  output_markov := by
    intro point
    rw [Kernel.comp_apply]
    apply Measure.IsProbability.bind
    · rw [liftStep_apply]
      exact (liftMarkov point).map _ _
    · intro pair
      rw [returnStep_apply]
      exact (chain.markov pair).map _ _
  lumps := by
    intro input state
    have lumped := Kernel.lumps_of_lumpsAlong (chain.stepAt input) (quotient input)
      (lumps input)
    have kernels : (chain.stepAt input).map (chain.retAt input)
        (chain.retAt_measurable input) =
        (Kernel.lumped (chain.stepAt input) (quotient input) (lumps input)).precomp
          (chain.retAt input) (chain.retAt_measurable input) := by
      apply Kernel.ext
      intro other
      rw [Kernel.map_apply, Kernel.precomp_apply]
      exact lumped other
    rw [Kernel.precomp_apply, Kernel.comp_apply, liftStep_bind, kernels,
      ← Measure.bind_map, lifted, Measure.dirac_bind]
    exact lumped state
  lift := lift
  lift_markov := liftMarkov
  lift_returns := lifted

end Lumpable

section Unordered

variable {γ : Type t} {element : Space γ}

/-- A chain on lists whose output forgets the order. -/
@[expose] def PresentedChain.unordered (element : Space γ)
    (initial : Kernel source (Space.list element))
    (step : Kernel (Space.product source (Space.list element)) (Space.list element))
    (markov : ∀ point, Measure.IsProbability (step point))
    (initialMarkov : ∀ input, Measure.IsProbability (initial input)) :
    PresentedChain.{u, t, t} source (Space.unordered element) where
  State := List γ
  space := Space.list element
  initial := initial
  step := step
  ret := fun point => unorder point.2
  measurable := MeasurableMap.comp (unorder_quotient_map element).measurable
    (Space.second_measurable _ _)
  markov := markov
  initial_markov := initialMarkov

theorem symmetrize_isProbability (configuration : Unordered γ) :
    Measure.IsProbability (symmetrize element configuration) := by
  refine Quotient.inductionOn configuration ?_
  intro values
  change Measure.IsProbability (shuffle element values)
  rw [shuffle_apply]
  exact (Measure.codeLaw_probability values.length).map _ _

/-- A chain on lists whose steps lump along `unorder` is lumpable, with a
uniformly random ordering as the lift. -/
@[expose] noncomputable def Lumpable.unordered
    (initial : Kernel source (Space.list element))
    (step : Kernel (Space.product source (Space.list element)) (Space.list element))
    (markov : ∀ point, Measure.IsProbability (step point))
    (initialMarkov : ∀ input, Measure.IsProbability (initial input))
    (lumps : ∀ input,
      ((PresentedChain.unordered element initial step markov initialMarkov).stepAt input).LumpsAlong
        unorder (unorder_quotient_map element).measurable) :
    Lumpable (PresentedChain.unordered element initial step markov initialMarkov) :=
  Lumpable.ofQuotient _ (fun _ => unorder_quotient_map element) lumps
    ((symmetrize element).precomp Prod.snd (Space.second_measurable _ _))
    (fun point => symmetrize_isProbability point.2)
    (fun _ output => symmetrize_unorder output)

/-- State-level convergence of a chain on lists to invariant laws that return
the target projects to its unordered output, with no lumpability. -/
theorem unordered_chain_converges
    (initial : Kernel source (Space.list element))
    (step : Kernel (Space.product source (Space.list element)) (Space.list element))
    (markov : ∀ point, Measure.IsProbability (step point))
    (initialMarkov : ∀ input, Measure.IsProbability (initial input))
    (target : Kernel source (Space.unordered element))
    (stationary : α → Giry.Law (Space.list element))
    (invariant : ∀ input, KernelInvariant (stationary input).val
      ((PresentedChain.unordered element initial step markov initialMarkov).stepAt input))
    (presents : ∀ input, (stationary input).val.map unorder
      (unorder_quotient_map element).measurable = target input)
    (converges : ∀ input start, Vanishes (fun count =>
      Giry.Law.totalVariation
        ((PresentedChain.unordered element initial step markov initialMarkov).stateLaw input
          ((PresentedChain.unordered element initial step markov initialMarkov).point start)
          count)
        (stationary input))) :
    PresentedInvariantConvergent target
      (PresentedChain.unordered element initial step markov initialMarkov) :=
  projected_chain_converges _ target stationary invariant presents converges

end Unordered

end
end Problib.Inference
