module

public import Problib.Analysis.Gaussian.Network.Predict
public import Problib.Analysis.Gaussian.Network.Observe
import Problib.Real.Grind
import Problib.Measure.Measurability.Real

/-! The Kalman filter as a collapsed Gaussian network.

A linear-Gaussian state-space step (`LinearGaussianStep dx dy`) moves the
state by `x' = c + F x + w`, with the process noise `w` drawn from a network,
and observes `y ~ N(e + H x', diag r)`. The source is the measure a program
denotes when it draws the initial state from a network and then, once per
observation, moves the state and weights it by the observation's likelihood
(`source`). It is a measure, not a probability: its mass is the evidence.

The filter carries a network and the evidence so far (`filter`). Each step
predicts, then observes:

- **Predict** (`predict`): append the moved state as children of the old one
  (`childRows`), move the children in front by adjacent reversals
  (`blockWord`), and keep the first `dx` rows, which drops the old state from
  the sinks. Its law is the old law bound against the move (`predict_law`).
- **Observe**: L6a's `score_collapse` per coordinate (`Network.observe`).

So the source is the evidence times the filtered network's law
(`filter_law`). The evidence is positive and finite
(`evidence_positive_finite`), and the filtered network keeps the state's
dimension (`length_filtered`).

The class covers a Gaussian initial state given as a network, affine moves
and observations, and positive noise in both. Zero process noise, noiseless
observations and singular covariances are outside it: `Network` and
`ObservesAll` require positive variances.
-/

set_option autoImplicit false

namespace Problib.Analysis.Gaussian

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

/-! ### The move as a kernel -/

public theorem moved_measurable (affine : Affine) :
    MeasurableMap (Space.product (Space.list borel) (Space.list borel)) (Space.list borel)
      (fun pair => addLists (affine.apply pair.1) pair.2) := by
  obtain ⟨offset, matrix⟩ := affine
  induction offset generalizing matrix with
  | nil =>
      have equal : (fun pair : List Carrier × List Carrier =>
          addLists (Affine.apply ⟨[], matrix⟩ pair.1) pair.2) = fun _ => [] := rfl
      rw [equal]
      intro set measurable
      exact MeasurableMap.constant _ (Space.list borel) ([] : List Carrier) measurable
  | cons first offset induction =>
      cases matrix with
      | nil =>
          have equal : (fun pair : List Carrier × List Carrier =>
              addLists (Affine.apply ⟨first :: offset, []⟩ pair.1) pair.2) = fun _ => [] := rfl
          rw [equal]
          intro set measurable
          exact MeasurableMap.constant _ (Space.list borel) ([] : List Carrier) measurable
      | cons row matrix =>
          have equal : (fun pair : List Carrier × List Carrier =>
              addLists (Affine.apply ⟨first :: offset, row :: matrix⟩ pair.1) pair.2) = fun pair =>
                if pair.2.length = 0 then []
                else add (add first (dot row pair.1)) (entry pair.2 0) ::
                  addLists (Affine.apply ⟨offset, matrix⟩ pair.1) pair.2.tail := by
            funext pair
            match pair with
            | (_, []) => rfl
            | (_, _ :: _) => simp [addLists, Affine.apply, entry]
          rw [equal]
          apply MeasurableMap.ite
          · have counting : MeasurableMap (Space.product (Space.list borel) (Space.list borel))
                (Space.discrete Nat) (fun pair : List Carrier × List Carrier => pair.2.length) :=
              MeasurableMap.comp (ListSpace.length_measurable borel)
                (Space.second_measurable (Space.list borel) (Space.list borel))
            exact counting (set := fun length => length = 0) trivial
          · intro set measurable
            exact MeasurableMap.constant _ (Space.list borel) ([] : List Carrier) measurable
          · have head : MeasurableMap (Space.product (Space.list borel) (Space.list borel)) borel
                (fun pair : List Carrier × List Carrier =>
                  add (add first (dot row pair.1)) (entry pair.2 0)) :=
              measurable_add
                (MeasurableMap.comp (add_left_measurable first)
                  (MeasurableMap.comp (dot_measurable row) (Space.first_measurable _ _)))
                (MeasurableMap.comp (entry_measurable 0) (Space.second_measurable _ _))
            have rest : MeasurableMap (Space.product (Space.list borel) (Space.list borel))
                (Space.list borel) (fun pair : List Carrier × List Carrier =>
                  addLists (Affine.apply ⟨offset, matrix⟩ pair.1) pair.2.tail) :=
              MeasurableMap.comp (induction matrix)
                (Space.pair_measurable (Space.first_measurable _ _)
                  (MeasurableMap.comp (ListSpace.tail_measurable borel)
                    (Space.second_measurable _ _)))
            intro set measurable
            exact MeasurableMap.comp (ListSpace.cons_measurable borel) (Space.pair_measurable head
                rest)
              measurable

public theorem addListsAt_measurable (affine : Affine) (values : List Carrier) :
    MeasurableMap (Space.list borel) (Space.list borel) (addLists (affine.apply values)) :=
  addLists_measurable _

/-- `x ↦` the law of `c + F x + w` with `w` drawn from the noise network. -/
@[expose] public def moveKernel (affine : Affine) (noise : Network) :
    Kernel (Space.list borel) (Space.list borel) :=
  (Kernel.attach (Kernel.const (Space.list borel) noise.law)
      (Kernel.IsSFinite.const _ (Measure.SFinite.ofFinite noise.law_isProbability.to_finite))).map
    (fun pair => addLists (affine.apply pair.1) pair.2) (moved_measurable affine)

public theorem moveKernel_apply (affine : Affine) (noise : Network) (values : List Carrier) :
    moveKernel affine noise values =
      noise.law.map (addLists (affine.apply values)) (addListsAt_measurable affine values) := by
  unfold moveKernel
  rw [Kernel.map_apply, Kernel.attach_apply, Kernel.const_apply, Measure.map_comp]

/-! ### The class -/

/-- One step of a linear-Gaussian state-space model with a state of `dx`
coordinates and observations of `dy`: the move `x' = c + F x + w` with `w`
drawn from the process-noise network, and the observation rows
`yⱼ ~ N(eⱼ + ⟨Hⱼ, x'⟩, rⱼ)`. -/
public structure LinearGaussianStep (dx dy : Nat) where
  transition : Affine
  noise : Network
  observation : List Row
  transitionShaped : transition.Shaped dx dx
  noiseLength : noise.length = dx
  observes : ObservesAll dx observation
  observationLength : observation.length = dy

namespace LinearGaussianStep

variable {dx dy : Nat} (step : LinearGaussianStep dx dy)

/-- The move, as a kernel of the state. -/
@[expose] public def move : Kernel (Space.list borel) (Space.list borel) :=
  moveKernel step.transition step.noise

/-- One source step: move the state, then weight it by the likelihood of the
observation. -/
@[expose] public def sourceStep (law : Measure (Space.list borel)) (observed : List Carrier) :
    Measure (Space.list borel) :=
  (law.bind step.move).withDensity (fun values => likelihood step.observation values observed)

/-- The source: the initial network's law, then one step per observation. -/
@[expose] public def source (initial : Network) (observations : List (List Carrier)) :
    Measure (Space.list borel) :=
  observations.foldl step.sourceStep initial.law

/-- The predict joint: the old state's network with the moved state appended
as its children, then moved in front, so it draws `x' ++ x`. -/
@[expose] public def joint (network : Network) : Network :=
  (network.extend (childRows step.transition network.length step.noise.rows)
      (childRows_triangular step.transition network.length step.noise)
      (childRows_positive step.transition network.length step.noise)).reverseAlong
    (blockWord network.length dx)

public theorem length_joint (network : Network) :
    (step.joint network).length = network.length + dx := by
  unfold joint
  rw [Network.length_reverseAlong, Network.length_extend, length_childRows]
  change network.length + step.noise.length = _
  rw [step.noiseLength]

/-- Predict: keep the joint's moved state, which drops the old state from the
sinks. -/
@[expose] public def predict (network : Network) : Network :=
  (step.joint network).take dx

public theorem length_predict (network : Network) : (step.predict network).length = dx := by
  unfold predict
  rw [Network.length_take, step.length_joint]
  omega

/-- The predicted network's law is the old law bound against the move. -/
public theorem predict_law (network : Network) (length : network.length = dx) :
    network.law.bind step.move = (step.predict network).law := by
  unfold predict joint
  rw [← Network.take_law, ← Network.reverse_along, Measure.map_comp, Network.extend_law,
    Measure.map_bind]
  apply Measure.bind_congr_ae
  apply Measure.AE.mono network.law_length_null
  intro values counted
  change step.move values = (restKernel _ values).map _ _
  rw [restKernel_childRows step.transition (rows := dx) (length ▸ step.transitionShaped)
      step.noise (Nat.le_of_eq step.noiseLength) counted, Measure.map_comp, move, moveKernel_apply]
  apply Measure.map_congr_on _ step.noise.law_length_null
  intro noise noiseCounted
  change noise.length = step.noise.length at noiseCounted
  have movedCounted : (addLists (step.transition.apply values) noise).length = dx := by
    unfold addLists
    rw [List.length_zipWith, step.transition.length_apply step.transitionShaped, noiseCounted,
        step.noiseLength,
      Nat.min_self]
  change addLists _ noise =
    (permute (blockWord network.length dx) (values ++ addLists _ noise)).take dx
  rw [permute_blockWord values _ counted movedCounted, List.take_left' movedCounted]

public theorem move_isProbability (values : List Carrier) :
    Measure.IsProbability (step.move values) := by
  rw [move, moveKernel_apply]
  exact step.noise.law_isProbability.map _ _

/-- The move is a Markov kernel, so it is s-finite. -/
public def moveSFinite : Kernel.IsSFinite step.move :=
  Kernel.IsSFinite.ofMarkov step.move_isProbability

/-- A move has `dx` coordinates. -/
public theorem move_length (values : List Carrier) :
    (step.move values).AE (fun moved => moved.length = dx) := by
  have counting : (Space.list borel).Measurable (fun moved : List Carrier => moved.length = dx) :=
      by
    exact ListSpace.length_measurable borel (set := fun length => length = dx) trivial
  rw [move, moveKernel_apply, Measure.ae_map_iff _ _ counting]
  apply Measure.AE.mono step.noise.law_length_null
  intro noise counted
  change (addLists _ noise).length = dx
  change noise.length = step.noise.length at counted
  unfold addLists
  rw [List.length_zipWith, step.transition.length_apply step.transitionShaped, counted,
    step.noiseLength, Nat.min_self]

/-- `x ↦` the law of `x' ++ x`, with `x'` the move of `x`. -/
@[expose] public def jointKernel : Kernel (Space.list borel) (Space.list borel) :=
  (Kernel.attach step.move step.moveSFinite).map (fun pair => pair.2 ++ pair.1)
    (MeasurableMap.comp append_measurable (Space.swap_measurable _ _))

public theorem jointKernel_apply (values : List Carrier) :
    step.jointKernel values =
      (step.move values).map (fun moved => moved ++ values) (appendRight_measurable values) := by
  unfold jointKernel
  rw [Kernel.map_apply, Kernel.attach_apply, Measure.map_comp]
  exact MeasurableMap.comp append_measurable (Space.swap_measurable _ _)

/-- The predict joint's law is the old law bound against the joint kernel. -/
public theorem joint_law (network : Network) (length : network.length = dx) :
    network.law.bind step.jointKernel = (step.joint network).law := by
  unfold joint
  rw [← Network.reverse_along, Network.extend_law, Measure.map_bind]
  apply Measure.bind_congr_ae
  apply Measure.AE.mono network.law_length_null
  intro values counted
  change step.jointKernel values = (restKernel _ values).map _ _
  rw [restKernel_childRows step.transition (rows := dx) (length ▸ step.transitionShaped)
      step.noise (Nat.le_of_eq step.noiseLength) counted, Measure.map_comp, jointKernel_apply,
    move, moveKernel_apply, Measure.map_comp]
  apply Measure.map_congr_on _ step.noise.law_length_null
  intro noise noiseCounted
  change noise.length = step.noise.length at noiseCounted
  have movedCounted : (addLists (step.transition.apply values) noise).length = dx := by
    unfold addLists
    rw [List.length_zipWith, step.transition.length_apply step.transitionShaped, noiseCounted,
      step.noiseLength, Nat.min_self]
  change addLists _ noise ++ values =
    permute (blockWord network.length dx) (values ++ addLists _ noise)
  rw [permute_blockWord values _ counted movedCounted]

/-! ### The filter -/

/-- One filter step: predict, then observe, multiplying the evidence. -/
@[expose] public def filterStep (state : Network × ENNReal) (observed : List Carrier) :
    Network × ENNReal :=
  let next := (step.predict state.1).observe step.observation observed
  (next.1, ENNReal.mul state.2 next.2)

/-- The filter over the observations, from the initial network and evidence one. -/
@[expose] public def filter (initial : Network) (observations : List (List Carrier)) :
    Network × ENNReal :=
  observations.foldl step.filterStep (initial, ENNReal.one)

/-- The filtered network: the state given every observation. -/
@[expose] public def filtered (initial : Network) (observations : List (List Carrier)) : Network :=
  (step.filter initial observations).1

/-- The evidence: the source's total mass. -/
@[expose] public def evidence (initial : Network) (observations : List (List Carrier)) : ENNReal :=
  (step.filter initial observations).2

private theorem foldl_filter (observations : List (List Carrier)) :
    ∀ (state : Network × ENNReal), state.1.length = dx →
      (observations.foldl step.filterStep state).1.length = dx := by
  induction observations with
  | nil => exact fun _ counted => counted
  | cons observed observations induction =>
      intro state counted
      apply induction
      exact ((step.predict state.1).length_observe _ _).trans (step.length_predict state.1)

public theorem length_filtered (initial : Network) (length : initial.length = dx)
    (observations : List (List Carrier)) : (step.filtered initial observations).length = dx :=
  step.foldl_filter observations _ length

public theorem evidence_positive_finite (initial : Network) (observations : List (List Carrier)) :
    PositiveFinite (step.evidence initial observations) := by
  unfold evidence filter
  suffices ∀ (state : Network × ENNReal), PositiveFinite state.2 →
      PositiveFinite (observations.foldl step.filterStep state).2 from this _ PositiveFinite.one
  induction observations with
  | nil => exact fun _ holds => holds
  | cons observed observations induction =>
      exact fun state holds => induction _
        (PositiveFinite.mul holds ((step.predict state.1).observe_positive_finite _ _))

/-- The Kalman filter: the source is the evidence times the filtered
network's law. -/
public theorem filter_law (initial : Network) (length : initial.length = dx)
    (observations : List (List Carrier)) (counted : ∀ observed ∈ observations, observed.length =
        dy) :
    step.source initial observations =
      Measure.smul (step.evidence initial observations) (step.filtered initial observations).law :=
          by
  unfold source evidence filtered filter
  rw [← Measure.one_smul initial.law]
  generalize ENNReal.one = scalar
  induction observations generalizing initial scalar with
  | nil => rfl
  | cons observed observations induction =>
      rw [List.foldl_cons, List.foldl_cons]
      have observes : ObservesAll (step.predict initial).length step.observation := by
        rw [step.length_predict]
        exact step.observes
      have stepped : step.sourceStep (Measure.smul scalar initial.law) observed =
          Measure.smul (step.filterStep (initial, scalar) observed).2
            (step.filterStep (initial, scalar) observed).1.law := by
        unfold sourceStep filterStep
        rw [Measure.smul_bind, step.predict_law initial length,
          Network.smul_withDensity_left _ _ (likelihood_measurable _ _),
          (step.predict initial).observe_law _ _ observes
            ((counted observed (List.mem_cons_self ..)).trans step.observationLength.symm),
          Measure.smul_smul]
      rw [stepped]
      exact induction _ (((step.predict initial).length_observe _ _).trans (step.length_predict _))
        (fun current member => counted current (List.mem_cons_of_mem _ member)) _

end LinearGaussianStep

end
end Problib.Analysis.Gaussian
