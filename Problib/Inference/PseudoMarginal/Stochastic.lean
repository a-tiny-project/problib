module

public import Problib.Inference.SPI
public import Problib.Inference.Involutive
public import Problib.Inference.Population
public import Problib.Measure.Measurability.Extended
set_option autoImplicit false

/-! Metropolis–Hastings with a stochastic proposal density.

Lew's Algorithm 2 runs Metropolis–Hastings on the pseudo-marginal extended
target `χP = (ν ⊗ ξP) · p`, the extended target read at the retained estimate
`p`. The proposal has no density to evaluate. A sampler `χQ(x)` draws a proposed
value `y` with a forward weight `wf`, and an estimator `ξQ` estimates the
proposal density in the reverse direction. From the state `(x, p)` the step draws
`(y, wf)` from `χQ(x)`, then `p'` from `ξP(y)` and `wb` from `ξQ(y, x)`
(`stochasticAuxiliary`). It moves to `(y, p')` exactly when `u · p · wf < p' · wb`
for a uniform `u`, and otherwise keeps `(x, p)` (`stochasticKernel`). The test
needs no division, and a rejected step never refreshes `p`.

Pairing alone gives invariance. When each `χQ(x)` is the extended target of
`ν ⊗ ξQ(x, ·)` read at its own estimate, the joint equation of `Paired`, the step
leaves `χP` invariant (`stochastic_mh_invariant`). No density of the proposal, no
unbiasedness of either estimator and no property of the target enters. The joint
law of a state and its auxiliary draws is the reference
`ν(dx) ν(dy) ξP(x, dp) ξQ(x, y, dwf) ξP(y, dp') ξQ(y, x, dwb)` weighted by
`p · wf` (`stochastic_joint`). Exchanging `(x, p, wf)` with `(y, p', wb)`
preserves that reference (`stochasticReference_swap`), and the involutive
accept/reject theorem gives invariance. Unbiasedness of `ξP` enters only the
value marginal (`stochastic_mh_marginal`). Ordinary Metropolis–Hastings is the
exact case: exact densities read as Dirac estimates are paired, and the test
becomes the Hastings test (`stochastic_mh_exact`).

Counterexample B in `Necessity.Reciprocal` shows the joint equation is needed.
Strict reciprocal samplers with an exact reverse density break invariance. -/

namespace Problib.Inference

open Problib.Real Problib.Measure
open Problib.Measure.Real (Carrier borel)

universe u v w

public section

/-! ### Chained draws -/

section Chained

variable {σ : Type u} {β : Type v} {γ : Type w}
  {source : Space σ} {first : Space β} {second : Space γ}

theorem chained_measurable :
    MeasurableMap (Space.product (Space.product source first) second)
      (Space.product first second) (fun draw => (draw.1.2, draw.2)) := by
  measurability

/-- Draw from `head` at the input, then from `tail` at the input and that draw,
and return both draws. -/
@[expose] noncomputable def chained (head : Kernel source first)
    (headFinite : Kernel.IsSFinite head) (tail : Kernel (Space.product source first) second)
    (tailFinite : Kernel.IsSFinite tail) : Kernel source (Space.product first second) :=
  (head.attach headFinite).comp
    ((tail.attach tailFinite).map (fun draw => (draw.1.2, draw.2)) chained_measurable)

@[expose] noncomputable def chainedFinite {head : Kernel source first}
    (headFinite : Kernel.IsSFinite head) {tail : Kernel (Space.product source first) second}
    (tailFinite : Kernel.IsSFinite tail) :
    Kernel.IsSFinite (chained head headFinite tail tailFinite) :=
  (Kernel.IsSFinite.attach headFinite).comp
    ((Kernel.IsSFinite.attach tailFinite).map _ chained_measurable)

/-- Integrating against chained draws integrates the tail inside the head. -/
theorem lintegral_chained (head : Kernel source first) (headFinite : Kernel.IsSFinite head)
    (tail : Kernel (Space.product source first) second) (tailFinite : Kernel.IsSFinite tail)
    (input : σ) {function : β × γ → ENNReal}
    (measurable : ENNRealMeasurable (Space.product first second) function) :
    lintegral (chained head headFinite tail tailFinite input) function =
      lintegral (head input) fun value =>
        lintegral (tail (input, value)) fun next => function (value, next) := by
  rw [chained, Kernel.lintegral_comp _ _ _ measurable, Kernel.attach_apply,
    lintegral_map _ _ _ (Kernel.lintegral_measurable _ measurable)]
  apply lintegral_congr
  intro value
  rw [Kernel.map_apply, Kernel.attach_apply, Measure.map_comp]
  exact lintegral_map _ _ _ measurable

/-- Chained Markov kernels are Markov. -/
theorem chained_markov {head : Kernel source first}
    (headMarkov : ∀ input, Measure.IsProbability (head input)) (headFinite : Kernel.IsSFinite head)
    {tail : Kernel (Space.product source first) second}
    (tailMarkov : ∀ point, Measure.IsProbability (tail point)) (tailFinite : Kernel.IsSFinite tail)
    (input : σ) : Measure.IsProbability (chained head headFinite tail tailFinite input) := by
  rw [chained, Kernel.comp_apply]
  refine ((headMarkov input).map _ (Kernel.pair_left_measurable input)).bind _ fun draw => ?_
  rw [Kernel.map_apply, Kernel.attach_apply, Measure.map_comp]
  exact (tailMarkov _).map _ _

end Chained

section Stochastic

variable {α : Type u} {space : Space α}

/-! ### The two sides of a move -/

theorem flip_pair_measurable (space : Space α) :
    MeasurableMap
      (Space.product (Space.product space space) (Space.product weightSpace weightSpace))
      (Space.product space space) (fun draw => (draw.1.2, draw.1.1)) := by
  measurability

/-- The estimates on one side of a move from `x` to `y`: the target estimate
`p ~ ξP(x)`, then the proposal estimate `w ~ ξQ(x, y)`. -/
@[expose] noncomputable def sideEstimates (targetEstimator : Kernel space weightSpace)
    (targetFinite : Kernel.IsSFinite targetEstimator)
    (proposalEstimator : Kernel (Space.product space space) weightSpace)
    (proposalFinite : Kernel.IsSFinite proposalEstimator) :
    Kernel (Space.product space space) (Space.product weightSpace weightSpace) :=
  chained (targetEstimator.precomp Prod.fst (Space.first_measurable space space))
    (targetFinite.precomp _ (Space.first_measurable space space))
    (proposalEstimator.precomp Prod.fst
      (Space.first_measurable (Space.product space space) weightSpace))
    (proposalFinite.precomp _ (Space.first_measurable (Space.product space space) weightSpace))

@[expose] noncomputable def sideEstimatesFinite {targetEstimator : Kernel space weightSpace}
    (targetFinite : Kernel.IsSFinite targetEstimator)
    {proposalEstimator : Kernel (Space.product space space) weightSpace}
    (proposalFinite : Kernel.IsSFinite proposalEstimator) :
    Kernel.IsSFinite (sideEstimates targetEstimator targetFinite proposalEstimator proposalFinite) :=
  chainedFinite (targetFinite.precomp _ (Space.first_measurable space space))
    (proposalFinite.precomp _ (Space.first_measurable (Space.product space space) weightSpace))

theorem lintegral_sideEstimates (targetEstimator : Kernel space weightSpace)
    (targetFinite : Kernel.IsSFinite targetEstimator)
    (proposalEstimator : Kernel (Space.product space space) weightSpace)
    (proposalFinite : Kernel.IsSFinite proposalEstimator) (pair : α × α)
    {function : NNReal × NNReal → ENNReal}
    (measurable : ENNRealMeasurable (Space.product weightSpace weightSpace) function) :
    lintegral (sideEstimates targetEstimator targetFinite proposalEstimator proposalFinite pair)
        function =
      lintegral (targetEstimator pair.1) fun estimate =>
        lintegral (proposalEstimator pair) fun weight => function (estimate, weight) :=
  lintegral_chained _ _ _ _ pair measurable

theorem sideEstimates_markov {targetEstimator : Kernel space weightSpace}
    (targetMarkov : ∀ input, Measure.IsProbability (targetEstimator input))
    (targetFinite : Kernel.IsSFinite targetEstimator)
    {proposalEstimator : Kernel (Space.product space space) weightSpace}
    (proposalMarkov : ∀ pair, Measure.IsProbability (proposalEstimator pair))
    (proposalFinite : Kernel.IsSFinite proposalEstimator) (pair : α × α) :
    Measure.IsProbability
      (sideEstimates targetEstimator targetFinite proposalEstimator proposalFinite pair) :=
  chained_markov (fun point => targetMarkov point.1) _ (fun point => proposalMarkov point.1) _ pair

/-! ### The step -/

theorem reverse_pair_measurable (space : Space α) :
    MeasurableMap
      (Space.product (Space.product space weightSpace) (Space.product space weightSpace))
      (Space.product space space) (fun draw => (draw.2.1, draw.1.1)) := by
  measurability

/-- The auxiliary draws from the state `(x, p)`: the proposal `(y, wf) ~ χQ(x)`,
then the reverse side `(p', wb)` drawn by `side` at `(y, x)`. -/
@[expose] noncomputable def stochasticAuxiliary
    (sampler : Kernel space (Space.product space weightSpace))
    (samplerFinite : Kernel.IsSFinite sampler)
    (side : Kernel (Space.product space space) (Space.product weightSpace weightSpace))
    (sideFinite : Kernel.IsSFinite side) :
    Kernel (Space.product space weightSpace)
      (Space.product (Space.product space weightSpace) (Space.product weightSpace weightSpace)) :=
  chained (sampler.precomp Prod.fst (Space.first_measurable space weightSpace))
    (samplerFinite.precomp _ (Space.first_measurable space weightSpace))
    (side.precomp (fun draw => (draw.2.1, draw.1.1)) (reverse_pair_measurable space))
    (sideFinite.precomp _ (reverse_pair_measurable space))

@[expose] noncomputable def stochasticAuxiliaryFinite
    {sampler : Kernel space (Space.product space weightSpace)}
    (samplerFinite : Kernel.IsSFinite sampler)
    {side : Kernel (Space.product space space) (Space.product weightSpace weightSpace)}
    (sideFinite : Kernel.IsSFinite side) :
    Kernel.IsSFinite (stochasticAuxiliary sampler samplerFinite side sideFinite) :=
  chainedFinite (samplerFinite.precomp _ (Space.first_measurable space weightSpace))
    (sideFinite.precomp _ (reverse_pair_measurable space))

theorem lintegral_stochasticAuxiliary
    (sampler : Kernel space (Space.product space weightSpace))
    (samplerFinite : Kernel.IsSFinite sampler)
    (side : Kernel (Space.product space space) (Space.product weightSpace weightSpace))
    (sideFinite : Kernel.IsSFinite side) (state : α × NNReal)
    {function : (α × NNReal) × (NNReal × NNReal) → ENNReal}
    (measurable : ENNRealMeasurable
      (Space.product (Space.product space weightSpace) (Space.product weightSpace weightSpace))
      function) :
    lintegral (stochasticAuxiliary sampler samplerFinite side sideFinite state) function =
      lintegral (sampler state.1) fun proposed =>
        lintegral (side (proposed.1, state.1)) fun reverse => function (proposed, reverse) :=
  lintegral_chained _ _ _ _ state measurable

theorem stochasticAuxiliary_markov {sampler : Kernel space (Space.product space weightSpace)}
    (samplerMarkov : ∀ input, Measure.IsProbability (sampler input))
    (samplerFinite : Kernel.IsSFinite sampler)
    {side : Kernel (Space.product space space) (Space.product weightSpace weightSpace)}
    (sideMarkov : ∀ pair, Measure.IsProbability (side pair)) (sideFinite : Kernel.IsSFinite side)
    (state : α × NNReal) :
    Measure.IsProbability (stochasticAuxiliary sampler samplerFinite side sideFinite state) :=
  chained_markov (head := sampler.precomp Prod.fst (Space.first_measurable space weightSpace))
    (tail := side.precomp (fun draw => (draw.2.1, draw.1.1)) (reverse_pair_measurable space))
    (fun point => samplerMarkov point.1) _ (fun _ => sideMarkov _) _ state

/-- Exchange the current state and the forward weight with the proposed state
and the reverse weight: `((x, p), ((y, wf), (p', wb)))` goes to
`((y, p'), ((x, wb), (p, wf)))`. -/
@[expose] def stochasticSwap (point : (α × NNReal) × ((α × NNReal) × (NNReal × NNReal))) :
    (α × NNReal) × ((α × NNReal) × (NNReal × NNReal)) :=
  ((point.2.1.1, point.2.2.1), ((point.1.1, point.2.2.2), (point.1.2, point.2.1.2)))

theorem stochasticSwap_measurable (space : Space α) :
    MeasurableMap
      (Space.product (Space.product space weightSpace)
        (Space.product (Space.product space weightSpace) (Space.product weightSpace weightSpace)))
      (Space.product (Space.product space weightSpace)
        (Space.product (Space.product space weightSpace) (Space.product weightSpace weightSpace)))
      stochasticSwap := by
  unfold stochasticSwap
  measurability

/-- The flux `p · wf` of a state with its auxiliary draws. -/
@[expose] noncomputable def stochasticDensity
    (point : (α × NNReal) × ((α × NNReal) × (NNReal × NNReal))) :
    Carrier :=
  NNReal.toReal (NNReal.mul point.1.2 point.2.1.2)

theorem stochasticDensity_measurable (space : Space α) :
    MeasurableMap
      (Space.product (Space.product space weightSpace)
        (Space.product (Space.product space weightSpace) (Space.product weightSpace weightSpace)))
      borel stochasticDensity :=
  MeasurableMap.comp weight_toReal_measurable
    (weight_mul_measurable (by measurability) (by measurability))

/-- Lew's step with a stochastic proposal density. Draw the auxiliary values,
then move to `(y, p')` when `u · p · wf < p' · wb` and otherwise stay. -/
@[expose] noncomputable def stochasticKernel
    (sampler : Kernel space (Space.product space weightSpace))
    (samplerFinite : Kernel.IsSFinite sampler)
    (side : Kernel (Space.product space space) (Space.product weightSpace weightSpace))
    (sideFinite : Kernel.IsSFinite side) :
    Kernel (Space.product space weightSpace) (Space.product space weightSpace) :=
  involutiveKernel (stochasticAuxiliary sampler samplerFinite side sideFinite)
    (stochasticAuxiliaryFinite samplerFinite sideFinite) stochasticSwap
    (stochasticSwap_measurable space) (involutiveAccept stochasticSwap stochasticDensity)
    (involutiveAccept_measurable stochasticSwap (stochasticSwap_measurable space)
      (stochasticDensity_measurable space))

@[expose] noncomputable def stochasticKernelFinite
    {sampler : Kernel space (Space.product space weightSpace)}
    (samplerFinite : Kernel.IsSFinite sampler)
    {side : Kernel (Space.product space space) (Space.product weightSpace weightSpace)}
    (sideFinite : Kernel.IsSFinite side) :
    Kernel.IsSFinite (stochasticKernel sampler samplerFinite side sideFinite) :=
  involutiveKernelSFinite (stochasticAuxiliaryFinite samplerFinite sideFinite)
    (stochasticSwap_measurable space)
    (involutiveAccept_measurable stochasticSwap (stochasticSwap_measurable space)
      (stochasticDensity_measurable space))

theorem stochasticKernel_markov {sampler : Kernel space (Space.product space weightSpace)}
    (samplerMarkov : ∀ input, Measure.IsProbability (sampler input))
    (samplerFinite : Kernel.IsSFinite sampler)
    {side : Kernel (Space.product space space) (Space.product weightSpace weightSpace)}
    (sideMarkov : ∀ pair, Measure.IsProbability (side pair)) (sideFinite : Kernel.IsSFinite side)
    (state : α × NNReal) :
    Measure.IsProbability (stochasticKernel sampler samplerFinite side sideFinite state) :=
  involutiveKernel_markov (stochasticAuxiliaryFinite samplerFinite sideFinite)
    (stochasticAuxiliary_markov samplerMarkov samplerFinite sideMarkov sideFinite)
    (stochasticSwap_measurable space)
    (involutiveAccept_measurable stochasticSwap (stochasticSwap_measurable space)
      (stochasticDensity_measurable space))
    (involutiveAccept_le_one stochasticSwap stochasticDensity) state

/-! ### The reference -/

/-- Both sides of the move between `x` and `y`: `(p, wf)` from `x` toward `y`,
then `(p', wb)` from `y` toward `x`. -/
@[expose] noncomputable def bothSides
    (side : Kernel (Space.product space space) (Space.product weightSpace weightSpace))
    (sideFinite : Kernel.IsSFinite side) :
    Kernel (Space.product space space)
      (Space.product (Space.product weightSpace weightSpace) (Space.product weightSpace weightSpace)) :=
  chained side sideFinite (side.precomp (fun draw => (draw.1.2, draw.1.1)) (flip_pair_measurable space))
    (sideFinite.precomp _ (flip_pair_measurable space))

@[expose] noncomputable def bothSidesFinite
    {side : Kernel (Space.product space space) (Space.product weightSpace weightSpace)}
    (sideFinite : Kernel.IsSFinite side) : Kernel.IsSFinite (bothSides side sideFinite) :=
  chainedFinite sideFinite (sideFinite.precomp _ (flip_pair_measurable space))

/-- The reference `ν(dx) ν(dy)` with both sides' estimates. It is symmetric in
the two sides by construction. -/
@[expose] noncomputable def symmetricReference (reference : Measure space)
    (referenceFinite : Measure.SFinite reference)
    (side : Kernel (Space.product space space) (Space.product weightSpace weightSpace))
    (sideFinite : Kernel.IsSFinite side) :
    Measure (Space.product (Space.product space space)
      (Space.product (Space.product weightSpace weightSpace)
        (Space.product weightSpace weightSpace))) :=
  (Measure.prod reference reference referenceFinite).semiproduct (bothSides side sideFinite)
    (bothSidesFinite sideFinite)

theorem lintegral_symmetricReference (reference : Measure space)
    (referenceFinite : Measure.SFinite reference)
    (side : Kernel (Space.product space space) (Space.product weightSpace weightSpace))
    (sideFinite : Kernel.IsSFinite side)
    {function : (α × α) × ((NNReal × NNReal) × (NNReal × NNReal)) → ENNReal}
    (measurable : ENNRealMeasurable (Space.product (Space.product space space)
      (Space.product (Space.product weightSpace weightSpace)
        (Space.product weightSpace weightSpace))) function) :
    lintegral (symmetricReference reference referenceFinite side sideFinite) function =
      lintegral reference fun current => lintegral reference fun proposed =>
        lintegral (side (current, proposed)) fun near =>
          lintegral (side (proposed, current)) fun far =>
            function ((current, proposed), (near, far)) := by
  rw [symmetricReference, lintegral_semiproduct _ _ _ measurable,
    lintegral_prod _ _ _ (Kernel.lintegral_measurable_joint _ (bothSidesFinite sideFinite)
      (function := fun pair value => function (pair, value)) measurable)]
  apply lintegral_congr
  intro current
  apply lintegral_congr
  intro proposed
  exact lintegral_chained _ _ _ _ (current, proposed)
    (measurable.comp (Kernel.pair_left_measurable (current, proposed)))

theorem exchange_measurable (space : Space α) :
    MeasurableMap
      (Space.product (Space.product space space)
        (Space.product (Space.product weightSpace weightSpace)
          (Space.product weightSpace weightSpace)))
      (Space.product (Space.product space space)
        (Space.product (Space.product weightSpace weightSpace)
          (Space.product weightSpace weightSpace)))
      (fun point => ((point.1.2, point.1.1), (point.2.2, point.2.1))) := by
  measurability

/-- Exchanging the two values and the two sides preserves the symmetric
reference: s-finite Tonelli on `ν ⊗ ν` and on the two sides. -/
theorem symmetricReference_exchange (reference : Measure space)
    (referenceFinite : Measure.SFinite reference)
    (side : Kernel (Space.product space space) (Space.product weightSpace weightSpace))
    (sideMarkov : ∀ pair, Measure.IsProbability (side pair)) (sideFinite : Kernel.IsSFinite side) :
    (symmetricReference reference referenceFinite side sideFinite).map
        (fun point => ((point.1.2, point.1.1), (point.2.2, point.2.1)))
        (exchange_measurable space) =
      symmetricReference reference referenceFinite side sideFinite := by
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  have exchanged := measurable.comp (exchange_measurable space)
  rw [lintegral_map _ _ _ measurable,
    lintegral_symmetricReference _ _ _ _ exchanged,
    lintegral_symmetricReference _ _ _ _ measurable]
  have sideSFinite : ∀ pair, Measure.SFinite (side pair) := fun pair =>
    Measure.SFinite.ofFinite (sideMarkov pair).to_finite
  have inner : ENNRealMeasurable
      (Space.product (Space.product space space) (Space.product weightSpace weightSpace))
      (fun point => lintegral (side point.1) fun near =>
        function ((point.1.2, point.1.1), (point.2, near))) :=
    Kernel.lintegral_measurable_joint (side.precomp Prod.fst
        (Space.first_measurable (Space.product space space)
          (Space.product weightSpace weightSpace)))
      (sideFinite.precomp _ (Space.first_measurable (Space.product space space)
        (Space.product weightSpace weightSpace)))
      (function := fun point near => function ((point.1.2, point.1.1), (point.2, near)))
      (measurable.comp (by measurability))
  have outer : ENNRealMeasurable (Space.product space space)
      (fun pair => lintegral (side (pair.2, pair.1)) fun far =>
        lintegral (side pair) fun near => function ((pair.2, pair.1), (far, near))) :=
    Kernel.lintegral_measurable_joint (side.precomp (fun pair : α × α => (pair.2, pair.1))
        (Space.swap_measurable space space))
      (sideFinite.precomp _ (Space.swap_measurable space space))
      (function := fun pair far => lintegral (side pair) fun near =>
        function ((pair.2, pair.1), (far, near)))
      inner
  calc lintegral reference (fun current => lintegral reference fun proposed =>
        lintegral (side (current, proposed)) fun near =>
          lintegral (side (proposed, current)) fun far =>
            function ((proposed, current), (far, near)))
      = lintegral reference (fun current => lintegral reference fun proposed =>
          lintegral (side (proposed, current)) fun far =>
            lintegral (side (current, proposed)) fun near =>
              function ((proposed, current), (far, near))) := by
        apply lintegral_congr
        intro current
        apply lintegral_congr
        intro proposed
        exact lintegral_lintegral_swap _ _ (sideSFinite _) (sideSFinite _)
          (function := fun draws => function ((proposed, current), (draws.2, draws.1)))
          (measurable.comp (by measurability))
    _ = lintegral reference (fun proposed => lintegral reference fun current =>
          lintegral (side (proposed, current)) fun far =>
            lintegral (side (current, proposed)) fun near =>
              function ((proposed, current), (far, near))) :=
        lintegral_lintegral_swap _ _ referenceFinite referenceFinite
          (function := fun pair => lintegral (side (pair.2, pair.1)) fun far =>
            lintegral (side pair) fun near => function ((pair.2, pair.1), (far, near)))
          outer

/-- Arrange a point of the symmetric reference as a state with its auxiliary
draws: `((x, y), ((p, wf), (p', wb)))` goes to `((x, p), ((y, wf), (p', wb)))`. -/
@[expose] def stochasticArrange
    (point : (α × α) × ((NNReal × NNReal) × (NNReal × NNReal))) :
    (α × NNReal) × ((α × NNReal) × (NNReal × NNReal)) :=
  ((point.1.1, point.2.1.1), ((point.1.2, point.2.1.2), point.2.2))

theorem stochasticArrange_measurable (space : Space α) :
    MeasurableMap
      (Space.product (Space.product space space)
        (Space.product (Space.product weightSpace weightSpace)
          (Space.product weightSpace weightSpace)))
      (Space.product (Space.product space weightSpace)
        (Space.product (Space.product space weightSpace) (Space.product weightSpace weightSpace)))
      stochasticArrange := by
  unfold stochasticArrange
  measurability

/-- The reference on states with their auxiliary draws. -/
@[expose] noncomputable def stochasticReference (reference : Measure space)
    (referenceFinite : Measure.SFinite reference)
    (side : Kernel (Space.product space space) (Space.product weightSpace weightSpace))
    (sideFinite : Kernel.IsSFinite side) :
    Measure (Space.product (Space.product space weightSpace)
      (Space.product (Space.product space weightSpace) (Space.product weightSpace weightSpace))) :=
  (symmetricReference reference referenceFinite side sideFinite).map stochasticArrange
    (stochasticArrange_measurable space)

/-- The swap preserves the reference, because arranging then swapping is
exchanging then arranging. -/
theorem stochasticReference_swap (reference : Measure space)
    (referenceFinite : Measure.SFinite reference)
    (side : Kernel (Space.product space space) (Space.product weightSpace weightSpace))
    (sideMarkov : ∀ pair, Measure.IsProbability (side pair)) (sideFinite : Kernel.IsSFinite side) :
    (stochasticReference reference referenceFinite side sideFinite).map stochasticSwap
        (stochasticSwap_measurable space) =
      stochasticReference reference referenceFinite side sideFinite := by
  unfold stochasticReference
  calc ((symmetricReference reference referenceFinite side sideFinite).map stochasticArrange
          (stochasticArrange_measurable space)).map stochasticSwap (stochasticSwap_measurable space)
      = (symmetricReference reference referenceFinite side sideFinite).map
          (fun point => stochasticSwap (stochasticArrange point))
          (MeasurableMap.comp (stochasticSwap_measurable space)
            (stochasticArrange_measurable space)) :=
        Measure.map_comp _ stochasticArrange stochasticSwap (stochasticArrange_measurable space)
          (stochasticSwap_measurable space)
    _ = ((symmetricReference reference referenceFinite side sideFinite).map
          (fun point => ((point.1.2, point.1.1), (point.2.2, point.2.1)))
          (exchange_measurable space)).map stochasticArrange
          (stochasticArrange_measurable space) :=
        (Measure.map_comp _
          (fun point : (α × α) × ((NNReal × NNReal) × (NNReal × NNReal)) =>
            ((point.1.2, point.1.1), (point.2.2, point.2.1)))
          stochasticArrange (exchange_measurable space) (stochasticArrange_measurable space)).symm
    _ = (symmetricReference reference referenceFinite side sideFinite).map stochasticArrange
          (stochasticArrange_measurable space) := by
        rw [symmetricReference_exchange reference referenceFinite side sideMarkov sideFinite]

/-! ### The joint law -/

/-- The joint law of a state of `χP` and its auxiliary draws is the reference
weighted by `p · wf`. The sampler enters only through the joint equation of
`Paired` at each current value. -/
theorem stochastic_joint (reference : Measure space)
    (referenceFinite : Measure.SFinite reference)
    {targetEstimator : Kernel space weightSpace}
    (targetMarkov : ∀ input, Measure.IsProbability (targetEstimator input))
    (targetFinite : Kernel.IsSFinite targetEstimator)
    {proposalEstimator : Kernel (Space.product space space) weightSpace}
    (proposalMarkov : ∀ pair, Measure.IsProbability (proposalEstimator pair))
    (proposalFinite : Kernel.IsSFinite proposalEstimator)
    {sampler : Kernel space (Space.product space weightSpace)}
    (samplerFinite : Kernel.IsSFinite sampler)
    (joint : ∀ input, sampler input = extendedTarget reference
      (proposalEstimator.precomp (fun output => (input, output))
        (Kernel.pair_left_measurable input))
      (proposalFinite.precomp _ (Kernel.pair_left_measurable input)) Prod.snd) :
    (extendedTarget reference targetEstimator targetFinite Prod.snd).semiproduct
        (stochasticAuxiliary sampler samplerFinite
          (sideEstimates targetEstimator targetFinite proposalEstimator proposalFinite)
          (sideEstimatesFinite targetFinite proposalFinite))
        (stochasticAuxiliaryFinite samplerFinite (sideEstimatesFinite targetFinite proposalFinite)) =
      (stochasticReference reference referenceFinite
          (sideEstimates targetEstimator targetFinite proposalEstimator proposalFinite)
          (sideEstimatesFinite targetFinite proposalFinite)).withDensity
        (fun point => ENNReal.finite (NNReal.mul point.1.2 point.2.1.2)) := by
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  have weightMeasurable : ENNRealMeasurable
      (Space.product (Space.product space weightSpace)
        (Space.product (Space.product space weightSpace) (Space.product weightSpace weightSpace)))
      (fun point : (α × NNReal) × ((α × NNReal) × (NNReal × NNReal)) =>
        ENNReal.finite (NNReal.mul point.1.2 point.2.1.2)) :=
    finite_weight_measurable (weight_mul_measurable (by measurability) (by measurability))
  have auxiliaryMeasurable := Kernel.lintegral_measurable_joint _
    (stochasticAuxiliaryFinite samplerFinite (sideEstimatesFinite targetFinite proposalFinite))
    (function := fun state value => function (state, value)) measurable
  have retained := finite_weight_measurable (Space.second_measurable space weightSpace)
  have weighted := ENNRealMeasurable.mul weightMeasurable measurable
  rw [lintegral_semiproduct _ _ _ measurable, extendedTarget,
    lintegral_withDensity _ retained auxiliaryMeasurable,
    lintegral_semiproduct _ _ _ (ENNRealMeasurable.mul retained auxiliaryMeasurable),
    stochasticReference, lintegral_withDensity _ weightMeasurable measurable,
    lintegral_map _ _ _ weighted,
    lintegral_symmetricReference _ _ _ _ (weighted.comp (stochasticArrange_measurable space))]
  apply lintegral_congr
  intro current
  have targetSFinite : Measure.SFinite (targetEstimator current) :=
    Measure.SFinite.ofFinite (targetMarkov current).to_finite
  -- The reverse side's integral of the arranged integrand, at fixed `p` and `wf`.
  have reverseMeasurable : ∀ proposed estimate weight, ENNRealMeasurable
      (Space.product weightSpace weightSpace) (fun far =>
        ENNReal.mul (ENNReal.finite (NNReal.mul estimate weight))
          (function ((current, estimate), ((proposed, weight), far)))) :=
    fun proposed estimate weight => weighted.comp
      (before := fun far => ((current, estimate), ((proposed, weight), far))) (by measurability)
  -- The integrand after `ν(dy)`, as a function of `(y, p)`.
  have swapped : ENNRealMeasurable (Space.product space weightSpace)
      (fun point => lintegral (proposalEstimator (current, point.1)) fun weight =>
        lintegral (targetEstimator point.1) fun reverseEstimate =>
          lintegral (proposalEstimator (point.1, current)) fun reverse =>
            ENNReal.mul (ENNReal.finite (NNReal.mul point.2 weight))
              (function ((current, point.2), ((point.1, weight), (reverseEstimate, reverse))))) :=
    Kernel.lintegral_measurable_joint
      (proposalEstimator.precomp (fun point : α × NNReal => (current, point.1)) (by measurability))
      (proposalFinite.precomp _ (by measurability))
      (function := fun (point : α × NNReal) weight =>
        lintegral (targetEstimator point.1) fun reverseEstimate =>
          lintegral (proposalEstimator (point.1, current)) fun reverse =>
            ENNReal.mul (ENNReal.finite (NNReal.mul point.2 weight))
              (function ((current, point.2), ((point.1, weight), (reverseEstimate, reverse)))))
      (Kernel.lintegral_measurable_joint
        (targetEstimator.precomp (fun point : (α × NNReal) × NNReal => point.1.1) (by measurability))
        (targetFinite.precomp _ (by measurability))
        (function := fun (point : (α × NNReal) × NNReal) reverseEstimate =>
          lintegral (proposalEstimator (point.1.1, current)) fun reverse =>
            ENNReal.mul (ENNReal.finite (NNReal.mul point.1.2 point.2))
              (function ((current, point.1.2), ((point.1.1, point.2),
                (reverseEstimate, reverse)))))
        (Kernel.lintegral_measurable_joint
          (proposalEstimator.precomp
            (fun point : ((α × NNReal) × NNReal) × NNReal => (point.1.1.1, current))
            (by measurability))
          (proposalFinite.precomp _ (by measurability))
          (function := fun (point : ((α × NNReal) × NNReal) × NNReal) reverse =>
            ENNReal.mul (ENNReal.finite (NNReal.mul point.1.1.2 point.1.2))
              (function ((current, point.1.1.2), ((point.1.1.1, point.1.2),
                (point.2, reverse)))))
          (weighted.comp (before := fun point : (((α × NNReal) × NNReal) × NNReal) × NNReal =>
            ((current, point.1.1.1.2), ((point.1.1.1.1, point.1.1.2), (point.1.2, point.2))))
            (by measurability))))
  symm
  calc lintegral reference (fun proposed =>
        lintegral (sideEstimates targetEstimator targetFinite proposalEstimator proposalFinite
            (current, proposed)) fun near =>
          lintegral (sideEstimates targetEstimator targetFinite proposalEstimator proposalFinite
              (proposed, current)) fun far =>
            ENNReal.mul (ENNReal.finite (NNReal.mul near.1 near.2))
              (function ((current, near.1), ((proposed, near.2), far))))
      = lintegral reference (fun proposed => lintegral (targetEstimator current) fun estimate =>
          lintegral (proposalEstimator (current, proposed)) fun weight =>
            lintegral (targetEstimator proposed) fun reverseEstimate =>
              lintegral (proposalEstimator (proposed, current)) fun reverse =>
                ENNReal.mul (ENNReal.finite (NNReal.mul estimate weight))
                  (function ((current, estimate), ((proposed, weight),
                    (reverseEstimate, reverse))))) := by
        apply lintegral_congr
        intro proposed
        refine (lintegral_sideEstimates _ _ _ _ (current, proposed)
          (Kernel.lintegral_measurable_joint
            (Kernel.const (Space.product weightSpace weightSpace)
              (sideEstimates targetEstimator targetFinite proposalEstimator proposalFinite
                (proposed, current)))
            (Kernel.IsSFinite.const _ (Measure.SFinite.ofFinite
              (sideEstimates_markov targetMarkov targetFinite proposalMarkov proposalFinite
                (proposed, current)).to_finite))
            (function := fun near far => ENNReal.mul (ENNReal.finite (NNReal.mul near.1 near.2))
              (function ((current, near.1), ((proposed, near.2), far))))
            (weighted.comp (before := fun point : (NNReal × NNReal) × (NNReal × NNReal) =>
              ((current, point.1.1), ((proposed, point.1.2), point.2)))
              (by measurability)))).trans ?_
        apply lintegral_congr
        intro estimate
        apply lintegral_congr
        intro weight
        exact lintegral_sideEstimates _ _ _ _ (proposed, current)
          (reverseMeasurable proposed estimate weight)
    _ = lintegral (targetEstimator current) (fun estimate => lintegral reference fun proposed =>
          lintegral (proposalEstimator (current, proposed)) fun weight =>
            lintegral (targetEstimator proposed) fun reverseEstimate =>
              lintegral (proposalEstimator (proposed, current)) fun reverse =>
                ENNReal.mul (ENNReal.finite (NNReal.mul estimate weight))
                  (function ((current, estimate), ((proposed, weight),
                    (reverseEstimate, reverse))))) :=
        lintegral_lintegral_swap _ _ referenceFinite targetSFinite
          (function := fun point : α × NNReal =>
            lintegral (proposalEstimator (current, point.1)) fun weight =>
            lintegral (targetEstimator point.1) fun reverseEstimate =>
              lintegral (proposalEstimator (point.1, current)) fun reverse =>
                ENNReal.mul (ENNReal.finite (NNReal.mul point.2 weight))
                  (function ((current, point.2), ((point.1, weight),
                    (reverseEstimate, reverse)))))
          swapped
    _ = _ := by
        apply lintegral_congr
        intro estimate
        -- The forward weight and the retained estimate leave the inner integrals.
        have sampled : ENNRealMeasurable (Space.product space weightSpace) (fun point =>
            lintegral (targetEstimator point.1) fun reverseEstimate =>
              lintegral (proposalEstimator (point.1, current)) fun reverse =>
                function ((current, estimate), ((point.1, point.2), (reverseEstimate, reverse)))) :=
          Kernel.lintegral_measurable_joint
            (targetEstimator.precomp Prod.fst (Space.first_measurable space weightSpace))
            (targetFinite.precomp _ (Space.first_measurable space weightSpace))
            (function := fun (point : α × NNReal) reverseEstimate =>
              lintegral (proposalEstimator (point.1, current)) fun reverse =>
                function ((current, estimate), ((point.1, point.2), (reverseEstimate, reverse))))
            (Kernel.lintegral_measurable_joint
              (proposalEstimator.precomp (fun point : (α × NNReal) × NNReal => (point.1.1, current))
                (by measurability))
              (proposalFinite.precomp _ (by measurability))
              (function := fun (point : (α × NNReal) × NNReal) reverse =>
                function ((current, estimate), ((point.1.1, point.1.2), (point.2, reverse))))
              (measurable.comp (by measurability)))
        have forward := ENNRealMeasurable.mul retained sampled
        calc lintegral reference (fun proposed =>
              lintegral (proposalEstimator (current, proposed)) fun weight =>
                lintegral (targetEstimator proposed) fun reverseEstimate =>
                  lintegral (proposalEstimator (proposed, current)) fun reverse =>
                    ENNReal.mul (ENNReal.finite (NNReal.mul estimate weight))
                      (function ((current, estimate), ((proposed, weight),
                        (reverseEstimate, reverse)))))
            = lintegral reference (fun proposed =>
                lintegral (proposalEstimator (current, proposed)) fun weight =>
                  ENNReal.mul (ENNReal.finite estimate) (ENNReal.mul (ENNReal.finite weight)
                    (lintegral (targetEstimator proposed) fun reverseEstimate =>
                      lintegral (proposalEstimator (proposed, current)) fun reverse =>
                        function ((current, estimate), ((proposed, weight),
                          (reverseEstimate, reverse)))))) := by
              apply lintegral_congr
              intro proposed
              apply lintegral_congr
              intro weight
              have reverseSection : ENNRealMeasurable weightSpace (fun reverseEstimate =>
                  lintegral (proposalEstimator (proposed, current)) fun reverse =>
                    function ((current, estimate), ((proposed, weight),
                      (reverseEstimate, reverse)))) :=
                Kernel.lintegral_measurable_joint
                  (Kernel.const weightSpace (proposalEstimator (proposed, current)))
                  (Kernel.IsSFinite.const _ (Measure.SFinite.ofFinite
                    (proposalMarkov (proposed, current)).to_finite))
                  (function := fun reverseEstimate reverse =>
                    function ((current, estimate), ((proposed, weight),
                      (reverseEstimate, reverse))))
                  (measurable.comp (by measurability))
              rw [← ENNReal.mul_assoc, ENNReal.finite_mul_finite,
                ← lintegral_smul _ _ reverseSection]
              apply lintegral_congr
              intro reverseEstimate
              exact lintegral_smul _ _ (measurable.comp (by measurability))
          _ = lintegral reference (fun proposed => ENNReal.mul (ENNReal.finite estimate)
                (lintegral (proposalEstimator (current, proposed)) fun weight =>
                  ENNReal.mul (ENNReal.finite weight)
                    (lintegral (targetEstimator proposed) fun reverseEstimate =>
                      lintegral (proposalEstimator (proposed, current)) fun reverse =>
                        function ((current, estimate), ((proposed, weight),
                          (reverseEstimate, reverse)))))) := by
              apply lintegral_congr
              intro proposed
              exact lintegral_smul _ _ (forward.comp (Kernel.pair_left_measurable proposed))
          _ = ENNReal.mul (ENNReal.finite estimate) (lintegral reference fun proposed =>
                lintegral (proposalEstimator (current, proposed)) fun weight =>
                  ENNReal.mul (ENNReal.finite weight)
                    (lintegral (targetEstimator proposed) fun reverseEstimate =>
                      lintegral (proposalEstimator (proposed, current)) fun reverse =>
                        function ((current, estimate), ((proposed, weight),
                          (reverseEstimate, reverse))))) :=
              lintegral_smul _ _ (Kernel.lintegral_measurable_joint
                (proposalEstimator.precomp (fun proposed => (current, proposed))
                  (Kernel.pair_left_measurable current))
                (proposalFinite.precomp _ (Kernel.pair_left_measurable current))
                (function := fun proposed weight => ENNReal.mul (ENNReal.finite weight)
                  (lintegral (targetEstimator proposed) fun reverseEstimate =>
                    lintegral (proposalEstimator (proposed, current)) fun reverse =>
                      function ((current, estimate), ((proposed, weight),
                        (reverseEstimate, reverse)))))
                forward)
          _ = _ := by
              have reverseIntegral : ENNRealMeasurable (Space.product space weightSpace)
                  (fun proposed : α × NNReal => lintegral
                    (sideEstimates targetEstimator targetFinite proposalEstimator proposalFinite
                      (proposed.1, (current, estimate).1)) fun reverse =>
                        function ((current, estimate), (proposed, reverse))) :=
                Kernel.lintegral_measurable_joint
                  ((sideEstimates targetEstimator targetFinite proposalEstimator
                    proposalFinite).precomp (fun point : α × NNReal => (point.1, current))
                      (by measurability))
                  ((sideEstimatesFinite targetFinite proposalFinite).precomp _
                    (by measurability))
                  (function := fun (point : α × NNReal) reverse =>
                    function ((current, estimate), (point, reverse)))
                  (measurable.comp (by measurability))
              rw [lintegral_stochasticAuxiliary _ _ _ _ (current, estimate)
                  (measurable.comp (Kernel.pair_left_measurable (current, estimate))),
                joint current, extendedTarget, lintegral_withDensity _ retained reverseIntegral,
                lintegral_semiproduct _ _ _ (ENNRealMeasurable.mul retained reverseIntegral)]
              refine congrArg (ENNReal.mul (ENNReal.finite estimate)) ?_
              apply lintegral_congr
              intro proposed
              apply lintegral_congr
              intro weight
              refine congrArg (ENNReal.mul (ENNReal.finite weight)) ?_
              exact (lintegral_sideEstimates targetEstimator targetFinite proposalEstimator
                proposalFinite (proposed, current)
                (function := fun reverse => function ((current, estimate), ((proposed, weight),
                  reverse)))
                (measurable.comp (before := fun reverse =>
                  ((current, estimate), ((proposed, weight), reverse))) (by measurability))).symm

/-! ### Invariance -/

/-- Lew's step with a stochastic proposal density leaves the extended target
invariant when the sampler is paired with the proposal estimator at each current
value. Only the joint equation enters: no proposal density, no unbiasedness and
no property of the target. Callers pass `(paired input).joint`. -/
theorem stochastic_mh_invariant (reference : Measure space)
    (referenceFinite : Measure.SFinite reference)
    {targetEstimator : Kernel space weightSpace}
    (targetMarkov : ∀ input, Measure.IsProbability (targetEstimator input))
    (targetFinite : Kernel.IsSFinite targetEstimator)
    {proposalEstimator : Kernel (Space.product space space) weightSpace}
    (proposalMarkov : ∀ pair, Measure.IsProbability (proposalEstimator pair))
    (proposalFinite : Kernel.IsSFinite proposalEstimator)
    {sampler : Kernel space (Space.product space weightSpace)}
    (samplerMarkov : ∀ input, Measure.IsProbability (sampler input))
    (samplerFinite : Kernel.IsSFinite sampler)
    (joint : ∀ input, sampler input = extendedTarget reference
      (proposalEstimator.precomp (fun output => (input, output))
        (Kernel.pair_left_measurable input))
      (proposalFinite.precomp _ (Kernel.pair_left_measurable input)) Prod.snd) :
    KernelInvariant (extendedTarget reference targetEstimator targetFinite Prod.snd)
      (stochasticKernel sampler samplerFinite
        (sideEstimates targetEstimator targetFinite proposalEstimator proposalFinite)
        (sideEstimatesFinite targetFinite proposalFinite)) := by
  have sideMarkov := sideEstimates_markov targetMarkov targetFinite proposalMarkov proposalFinite
  have density : (fun point => ENNReal.ofReal (stochasticDensity point)) =
      fun point : (α × NNReal) × ((α × NNReal) × (NNReal × NNReal)) =>
        ENNReal.finite (NNReal.mul point.1.2 point.2.1.2) :=
    funext fun point => ENNReal.ofReal_toReal_finite _
  exact involutive_invariant_of_reference _ _ _
    (stochasticAuxiliary_markov samplerMarkov samplerFinite sideMarkov _) stochasticSwap
    (stochasticSwap_measurable space) (fun _ => rfl) _
    (stochasticReference_swap reference referenceFinite _ sideMarkov _)
    (stochasticDensity_measurable space)
    ((stochastic_joint reference referenceFinite targetMarkov targetFinite proposalMarkov
      proposalFinite samplerFinite joint).trans
      (congrArg (fun weight => Measure.withDensity _ weight) density.symm))

/-! ### Corollaries -/

/-- Started at the extended target, one step leaves the value distributed as the
reference weighted by the target estimator's mean. Unbiasedness enters here and
nowhere else. -/
theorem stochastic_mh_marginal (reference : Measure space)
    (referenceFinite : Measure.SFinite reference) {density : α → ENNReal}
    {targetEstimator : Kernel space weightSpace} (unbiased : UnbiasedEstimate density targetEstimator)
    (targetFinite : Kernel.IsSFinite targetEstimator)
    {proposalEstimator : Kernel (Space.product space space) weightSpace}
    (proposalMarkov : ∀ pair, Measure.IsProbability (proposalEstimator pair))
    (proposalFinite : Kernel.IsSFinite proposalEstimator)
    {sampler : Kernel space (Space.product space weightSpace)}
    (samplerMarkov : ∀ input, Measure.IsProbability (sampler input))
    (samplerFinite : Kernel.IsSFinite sampler)
    (joint : ∀ input, sampler input = extendedTarget reference
      (proposalEstimator.precomp (fun output => (input, output))
        (Kernel.pair_left_measurable input))
      (proposalFinite.precomp _ (Kernel.pair_left_measurable input)) Prod.snd) :
    ((extendedTarget reference targetEstimator targetFinite Prod.snd).bind
        (stochasticKernel sampler samplerFinite
          (sideEstimates targetEstimator targetFinite proposalEstimator proposalFinite)
          (sideEstimatesFinite targetFinite proposalFinite))).map Prod.fst
        (Space.first_measurable space weightSpace) =
      reference.withDensity density := by
  rw [kernel_invariant_step rfl (stochastic_mh_invariant reference referenceFinite
    unbiased.probability targetFinite proposalMarkov proposalFinite samplerMarkov samplerFinite
    joint)]
  have readable := unbiased
  rw [← readEstimate_snd targetEstimator targetFinite] at readable
  exact pseudo_marginal_marginal targetFinite (Space.second_measurable space weightSpace) readable

/-- Moving weighted draws properly weighted for the extended target by the step,
keeping their weights, keeps them properly weighted. -/
theorem stochastic_mh_properlyWeighted (reference : Measure space)
    (referenceFinite : Measure.SFinite reference)
    {targetEstimator : Kernel space weightSpace}
    (targetMarkov : ∀ input, Measure.IsProbability (targetEstimator input))
    (targetFinite : Kernel.IsSFinite targetEstimator)
    {proposalEstimator : Kernel (Space.product space space) weightSpace}
    (proposalMarkov : ∀ pair, Measure.IsProbability (proposalEstimator pair))
    (proposalFinite : Kernel.IsSFinite proposalEstimator)
    {sampler : Kernel space (Space.product space weightSpace)}
    (samplerMarkov : ∀ input, Measure.IsProbability (sampler input))
    (samplerFinite : Kernel.IsSFinite sampler)
    (joint : ∀ input, sampler input = extendedTarget reference
      (proposalEstimator.precomp (fun output => (input, output))
        (Kernel.pair_left_measurable input))
      (proposalFinite.precomp _ (Kernel.pair_left_measurable input)) Prod.snd)
    {weighted : Measure (Space.product (Space.product space weightSpace) weightSpace)}
    (properlyWeighted : ProperlyWeighted
      (extendedTarget reference targetEstimator targetFinite Prod.snd) weighted) :
    ProperlyWeighted (extendedTarget reference targetEstimator targetFinite Prod.snd)
      (weighted.bind (keepWeight
        (stochasticKernel sampler samplerFinite
          (sideEstimates targetEstimator targetFinite proposalEstimator proposalFinite)
          (sideEstimatesFinite targetFinite proposalFinite))
        (stochasticKernelFinite samplerFinite (sideEstimatesFinite targetFinite proposalFinite)))) :=
  weighted_rejuvenate
    (stochasticKernel_markov samplerMarkov samplerFinite
      (sideEstimates_markov targetMarkov targetFinite proposalMarkov proposalFinite) _)
    _
    (stochastic_mh_invariant reference referenceFinite targetMarkov targetFinite proposalMarkov
      proposalFinite samplerMarkov samplerFinite joint)
    properlyWeighted

/-! ### The exact case -/

/-- Draw `y` from the proposal at `x` and weigh it by the exact proposal density
`q (x, y)`. -/
@[expose] noncomputable def exactSampler (proposal : Kernel space space)
    (proposalFinite : Kernel.IsSFinite proposal) {density : α × α → NNReal}
    (measurable : MeasurableMap (Space.product space space) weightSpace density) :
    Kernel space (Space.product space weightSpace) :=
  (proposal.attach proposalFinite).map (fun draw => (draw.2, density draw))
    (Space.pair_measurable (Space.second_measurable space space) measurable)

@[expose] noncomputable def exactSamplerFinite {proposal : Kernel space space}
    (proposalFinite : Kernel.IsSFinite proposal) {density : α × α → NNReal}
    (measurable : MeasurableMap (Space.product space space) weightSpace density) :
    Kernel.IsSFinite (exactSampler proposal proposalFinite measurable) :=
  (Kernel.IsSFinite.attach proposalFinite).map _
    (Space.pair_measurable (Space.second_measurable space space) measurable)

theorem exactSampler_apply (proposal : Kernel space space)
    (proposalFinite : Kernel.IsSFinite proposal) {density : α × α → NNReal}
    (measurable : MeasurableMap (Space.product space space) weightSpace density) (input : α) :
    exactSampler proposal proposalFinite measurable input =
      (proposal input).map (fun output => (output, density (input, output)))
        (Space.pair_measurable (MeasurableMap.identity space)
          (measurable.comp (Kernel.pair_left_measurable input))) := by
  rw [exactSampler, Kernel.map_apply, Kernel.attach_apply]
  exact Measure.map_comp _ _ _ (Kernel.pair_left_measurable input)
    (Space.pair_measurable (Space.second_measurable space space) measurable)

/-- Ordinary Metropolis–Hastings is the exact case of the step. When the target
has density `w` and the proposal has density `q` against one reference, read each
as a Dirac estimate. The retained estimate is then `w x`, the forward weight
`q (x, y)` and the reverse side `(w y, q (y, x))`, so the test
`u · w x · q (x, y) < w y · q (y, x)` is the Hastings test. The draws `y ~ Q x`
weighted by `q (x, ·)` are paired with the Dirac estimator (`paired_exact`), and
the step leaves the target, carried along the graph of `w`, invariant. -/
theorem stochastic_mh_exact (reference : Measure space)
    (referenceFinite : Measure.SFinite reference) {target : Measure space}
    {density : α → NNReal} (densityMeasurable : MeasurableMap space weightSpace density)
    (targetDensity : Measure.IsDensity target reference
      (fun input => ENNReal.finite (density input)))
    {proposal : Kernel space space}
    (proposalMarkov : ∀ input, Measure.IsProbability (proposal input))
    (proposalFinite : Kernel.IsSFinite proposal) {proposalDensity : α × α → NNReal}
    (proposalMeasurable :
      MeasurableMap (Space.product space space) weightSpace proposalDensity)
    (proposalRepresents : ∀ input, proposal input = reference.withDensity
      (fun output => ENNReal.finite (proposalDensity (input, output)))) :
    KernelInvariant
      (target.map (fun input => (input, density input))
        (Space.pair_measurable (MeasurableMap.identity space) densityMeasurable))
      (stochasticKernel (exactSampler proposal proposalFinite proposalMeasurable)
        (exactSamplerFinite proposalFinite proposalMeasurable)
        (sideEstimates (Kernel.deterministic density densityMeasurable)
          (Kernel.IsSFinite.deterministic density densityMeasurable)
          (Kernel.deterministic proposalDensity proposalMeasurable)
          (Kernel.IsSFinite.deterministic proposalDensity proposalMeasurable))
        (sideEstimatesFinite (Kernel.IsSFinite.deterministic density densityMeasurable)
          (Kernel.IsSFinite.deterministic proposalDensity proposalMeasurable))) := by
  rw [(paired_exact densityMeasurable targetDensity).joint]
  refine stochastic_mh_invariant reference referenceFinite
    (fun input => Measure.IsProbability.dirac _ (density input)) _
    (fun pair => Measure.IsProbability.dirac _ (proposalDensity pair)) _
    (fun input => ?_) _ fun input => ?_
  · rw [exactSampler_apply]
    exact (proposalMarkov input).map _ _
  · rw [exactSampler_apply]
    exact (paired_exact (proposalMeasurable.comp (Kernel.pair_left_measurable input))
      (proposalRepresents input)).joint

end Stochastic

end

end Problib.Inference
