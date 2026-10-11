module

public import Problib.Analysis.Gaussian.Network.Kalman
import Problib.Real.Grind

/-! The Kalman smoother as one joint backward network over the trajectory.

The trajectory source keeps every state, latest first: it draws `x₀` from the
initial network, and then, once per observation, draws `x'` from the move of
the newest state, puts it in front of the trajectory, and weights by the
likelihood of the observation at `x'` (`trajectorySource`).

The smoother carries one network over the whole trajectory (`smoothStep`). Its
first `dx` rows draw the newest state, from the filtered network; each later
block draws an older state given the newer ones and the observations so far.
One step builds the predict joint over `(x', x)` from the first block
(`LinearGaussianStep.joint`), keeps the older blocks behind it with their
coefficients shifted past `x'` (`shiftRows`), and observes `x'` in place
(`Network.collapse_prefix`). The trajectory source is the evidence times the
smoothed network's law (`smoother_law`), and the smoothed network's first
block is the filtered network (`smoothed_root`).

The rows are dense: a trajectory of `T + 1` states has `(T + 1)·dx` nodes, and
row `i` holds `i` coefficients, almost all of them zero. A draw costs
`O(T²dx²)`, against the `O(T dx²)` a banded backward draw needs.

Independent draws from each state's smoothed marginal are not a smoother: the
states are correlated, and this network draws them jointly.
-/

set_option autoImplicit false

namespace Problib.Analysis.Gaussian

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

/-! ### Two independent draws, appended in either order -/

/-- `z ↦` the law of `x' ++ z`, with `x'` drawn from a fixed measure. -/
@[expose] public def appendAfter (law : Measure (Space.list borel))
    (finite : Measure.SFinite law) : Kernel (Space.list borel) (Space.list borel) :=
  (Kernel.attach (Kernel.const (Space.list borel) law) (Kernel.IsSFinite.const _ finite)).map
    (fun pair => pair.2 ++ pair.1)
    (MeasurableMap.comp append_measurable (Space.swap_measurable _ _))

/-- `x' ↦` the law of `x' ++ z`, with `z` drawn from a fixed measure. -/
@[expose] public def appendBefore (law : Measure (Space.list borel))
    (finite : Measure.SFinite law) : Kernel (Space.list borel) (Space.list borel) :=
  (Kernel.attach (Kernel.const (Space.list borel) law) (Kernel.IsSFinite.const _ finite)).map
    (fun pair => pair.1 ++ pair.2) append_measurable

public theorem appendAfter_apply (law : Measure (Space.list borel)) (finite : Measure.SFinite law)
    (values : List Carrier) :
    appendAfter law finite values = law.map (fun moved => moved ++ values) (appendRight_measurable
        values) := by
  unfold appendAfter
  rw [Kernel.map_apply, Kernel.attach_apply, Kernel.const_apply, Measure.map_comp]
  exact MeasurableMap.comp append_measurable (Space.swap_measurable _ _)

public theorem appendBefore_apply (law : Measure (Space.list borel)) (finite : Measure.SFinite law)
    (front : List Carrier) :
    appendBefore law finite front = law.map (fun values => front ++ values) (prepend_measurable
        front) := by
  unfold appendBefore
  rw [Kernel.map_apply, Kernel.attach_apply, Kernel.const_apply, Measure.map_comp]

/-- Drawing `z` then `x'`, or `x'` then `z`, gives the same `x' ++ z` (Tonelli,
through the product's swap). -/
public theorem bind_appendAfter (back front : Measure (Space.list borel))
    (backFinite : Measure.SFinite back) (frontFinite : Measure.SFinite front) :
    back.bind (appendAfter front frontFinite) = front.bind (appendBefore back backFinite) := by
  unfold appendAfter appendBefore
  rw [← Measure.map_bind, ← Measure.map_bind]
  change (Measure.prod back front frontFinite).map _ _ = (Measure.prod front back backFinite).map _
      _
  rw [← Measure.prod_swap frontFinite backFinite, Measure.map_comp]
  exact MeasurableMap.comp append_measurable (Space.swap_measurable _ _)

namespace LinearGaussianStep

variable {dx dy : Nat} (step : LinearGaussianStep dx dy)

/-! ### The trajectory source -/

/-- `z ↦` the law of `x' ++ z`, with `x'` the move of `z`'s newest state. -/
@[expose] public def trajectoryKernel : Kernel (Space.list borel) (Space.list borel) :=
  (Kernel.attach (step.move.precomp (List.take dx) (take_measurable dx))
      (Kernel.IsSFinite.ofMarkov fun values => step.move_isProbability (values.take dx))).map
    (fun pair => pair.2 ++ pair.1)
    (MeasurableMap.comp append_measurable (Space.swap_measurable _ _))

public theorem trajectoryKernel_apply (values : List Carrier) :
    step.trajectoryKernel values =
      (step.move (values.take dx)).map (fun moved => moved ++ values) (appendRight_measurable
          values) := by
  unfold trajectoryKernel
  rw [Kernel.map_apply, Kernel.attach_apply, Measure.map_comp]
  · rfl
  · exact MeasurableMap.comp append_measurable (Space.swap_measurable _ _)

/-- One trajectory step: put the moved state in front, then weight by the
likelihood of the observation at it. -/
@[expose] public def trajectoryStep (law : Measure (Space.list borel)) (observed : List Carrier) :
    Measure (Space.list borel) :=
  (law.bind step.trajectoryKernel).withDensity
    (fun values => likelihood step.observation (values.take dx) observed)

/-- The trajectory source: every state, latest first. -/
@[expose] public def trajectorySource (initial : Network) (observations : List (List Carrier)) :
    Measure (Space.list borel) :=
  observations.foldl step.trajectoryStep initial.law

/-! ### The smoother -/

public theorem smooth_triangular (network : Network) (long : dx ≤ network.length) :
    TriangularFrom (step.joint (network.take dx)).length (shiftRows dx (network.rows.drop dx)) := by
  rw [step.length_joint, Nat.add_comm]
  exact shiftRows_triangular (network.drop_triangular long)

public theorem shiftRows_positive (network : Network) (count : Nat) :
    ∀ row ∈ shiftRows count (network.rows.drop count), lt zero row.variance := by
  intro row member
  obtain ⟨original, found, rfl⟩ := List.mem_map.mp member
  exact network.positive original (List.mem_of_mem_drop found)

/-- The predict joint of the newest state, with the older blocks behind it. -/
@[expose] public def smoothJoint (network : Network) (long : dx ≤ network.length) : Network :=
  (step.joint (network.take dx)).extend (shiftRows dx (network.rows.drop dx))
    (step.smooth_triangular network long) (shiftRows_positive network dx)

public theorem length_smoothJoint (network : Network) (long : dx ≤ network.length) :
    dx ≤ (step.smoothJoint network long).length := by
  unfold smoothJoint
  rw [Network.length_extend, step.length_joint]
  omega

public theorem take_smoothJoint (network : Network) (long : dx ≤ network.length) :
    (step.smoothJoint network long).take dx = step.predict (network.take dx) := by
  apply Network.ext
  change ((step.joint (network.take dx)).rows ++ _).take dx = (step.joint (network.take
      dx)).rows.take dx
  have joined := step.length_joint (network.take dx)
  unfold Network.length at joined
  rw [List.take_append_of_le_length (by omega)]

/-- One smoother step: observe the newest state of the predict joint, in place. -/
@[expose] public def smoothStep (network : Network) (observed : List Carrier) : Network :=
  if long : dx ≤ network.length then
    (step.smoothJoint network long).replacePrefix dx
      ((step.predict (network.take dx)).observe step.observation observed).1
      (((step.predict (network.take dx)).length_observe _ _).trans (step.length_predict _))
  else network

/-- The smoothed network: the whole trajectory given every observation. -/
@[expose] public def smoothed (initial : Network) (observations : List (List Carrier)) : Network :=
  observations.foldl step.smoothStep initial

private theorem smoothStep_eq (network : Network) (long : dx ≤ network.length)
    (observed : List Carrier) :
    step.smoothStep network observed =
      (step.smoothJoint network long).replacePrefix dx
        ((step.predict (network.take dx)).observe step.observation observed).1
        (((step.predict (network.take dx)).length_observe _ _).trans (step.length_predict _)) := by
  unfold smoothStep
  rw [dite_eq_left_of_eq_true (eq_true long)]

private theorem long_smoothStep (network : Network) (long : dx ≤ network.length)
    (observed : List Carrier) : dx ≤ (step.smoothStep network observed).length := by
  rw [step.smoothStep_eq network long, Network.length_replacePrefix _ _ _ _
    (step.length_smoothJoint network long)]
  exact step.length_smoothJoint network long

private theorem take_smoothStep (network : Network) (long : dx ≤ network.length)
    (observed : List Carrier) :
    (step.smoothStep network observed).take dx =
      ((step.predict (network.take dx)).observe step.observation observed).1 := by
  rw [step.smoothStep_eq network long, Network.take_replacePrefix]

/-! ### The smoother's law -/

/-- Older blocks keep their prefix, so the trajectory kernel reads it as fixed. -/
private theorem bind_trajectoryKernel (rows : List Row) {values : List Carrier}
    (counted : values.length = dx) :
    (restKernel rows values).bind step.trajectoryKernel =
      (restKernel rows values).bind
        (appendAfter (step.move values) (Measure.SFinite.ofFinite (step.move_isProbability
            values).to_finite)) := by
  have prefixed := restKernel_prefix rows values []
  rw [List.append_nil] at prefixed
  rw [← prefixed, Measure.bind_map, Measure.bind_map]
  congr 1
  apply Kernel.ext
  intro drawn
  rw [Kernel.precomp_apply, Kernel.precomp_apply, trajectoryKernel_apply, appendAfter_apply]
  have kept : (values ++ drawn.drop values.length).take dx = values := by
    rw [← counted, List.take_left]
  simp only [kept]

/-- The joint kernel, then the shifted older blocks: the move in front of the
older blocks' draw. -/
private theorem jointKernel_bind (rows : List Row) (values : List Carrier) :
    (step.jointKernel values).bind (restKernel (shiftRows dx rows)) =
      (step.move values).bind
        (appendBefore (restKernel rows values)
          (Measure.SFinite.ofFinite (restKernel_isProbability rows values).to_finite)) := by
  rw [step.jointKernel_apply, Measure.bind_map]
  apply Measure.bind_congr_ae
  apply Measure.AE.mono (step.move_length values)
  intro moved movedCounted
  dsimp only
  rw [Kernel.precomp_apply, appendBefore_apply, restKernel_shift rows movedCounted]

/-- Binding the trajectory kernel against a smoothed network gives the law of
its smoothing joint. -/
public theorem smoothJoint_law (network : Network) (long : dx ≤ network.length) :
    network.law.bind step.trajectoryKernel = (step.smoothJoint network long).law := by
  have rootLength : (network.take dx).length = dx := by
    rw [Network.length_take]
    omega
  conv => lhs; rw [← network.take_extend long]
  rw [smoothJoint, Network.extend_law, Network.extend_law, ← step.joint_law _ rootLength,
    Measure.bind_assoc, Measure.bind_assoc]
  apply Measure.bind_congr_ae
  apply Measure.AE.mono (network.take dx).law_length_null
  intro values counted
  change values.length = (network.take dx).length at counted
  rw [rootLength] at counted
  dsimp only
  rw [Kernel.comp_apply, Kernel.comp_apply, step.bind_trajectoryKernel _ counted,
    step.jointKernel_bind _ values, bind_appendAfter]

/-- One smoother step against one trajectory step. -/
private theorem trajectoryStep_smul (network : Network) (long : dx ≤ network.length)
    (scalar : ENNReal) (observed : List Carrier) (counted : observed.length = dy) :
    step.trajectoryStep (Measure.smul scalar network.law) observed =
      Measure.smul (step.filterStep (network.take dx, scalar) observed).2
        (step.smoothStep network observed).law := by
  have density : ENNRealMeasurable (Space.list borel)
      (fun values => likelihood step.observation (values.take dx) observed) :=
    ENNRealMeasurable.comp (likelihood_measurable _ _) (take_measurable dx)
  have observes : ObservesAll (step.predict (network.take dx)).length step.observation := by
    rw [step.length_predict]
    exact step.observes
  unfold trajectoryStep filterStep
  rw [Measure.smul_bind, Network.smul_withDensity_left _ _ density, step.smoothJoint_law network
      long,
    (step.smoothJoint network long).collapse_prefix (step.length_smoothJoint network long)
      _ _ (likelihood_measurable _ _) _
      (by
        rw [step.take_smoothJoint network long]
        exact (step.predict (network.take dx)).observe_law _ _ observes
          (counted.trans step.observationLength.symm)),
    Measure.smul_smul, step.smoothStep_eq network long]

private theorem foldl_smooth (observations : List (List Carrier)) :
    ∀ (network : Network) (scalar : ENNReal), dx ≤ network.length →
      (∀ observed ∈ observations, observed.length = dy) →
      observations.foldl step.trajectoryStep (Measure.smul scalar network.law) =
          Measure.smul (observations.foldl step.filterStep (network.take dx, scalar)).2
            (observations.foldl step.smoothStep network).law ∧
        (observations.foldl step.smoothStep network).take dx =
          (observations.foldl step.filterStep (network.take dx, scalar)).1 := by
  induction observations with
  | nil => exact fun _ _ _ _ => ⟨rfl, rfl⟩
  | cons observed observations induction =>
      intro network scalar long counted
      rw [List.foldl_cons, List.foldl_cons, List.foldl_cons,
        step.trajectoryStep_smul network long scalar observed (counted observed (List.mem_cons_self
            ..))]
      have next : step.filterStep (network.take dx, scalar) observed =
          ((step.smoothStep network observed).take dx,
            (step.filterStep (network.take dx, scalar) observed).2) := by
        rw [step.take_smoothStep network long]
        rfl
      rw [next]
      exact induction _ _ (step.long_smoothStep network long observed)
        fun current member => counted current (List.mem_cons_of_mem _ member)

private theorem take_initial (initial : Network) (length : initial.length = dx) :
    initial.take dx = initial :=
  Network.ext (List.take_of_length_le (by unfold Network.length at length; omega))

/-- The Kalman smoother: the trajectory source is the evidence times the
smoothed network's law. -/
public theorem smoother_law (initial : Network) (length : initial.length = dx)
    (observations : List (List Carrier)) (counted : ∀ observed ∈ observations, observed.length =
        dy) :
    step.trajectorySource initial observations =
      Measure.smul (step.evidence initial observations) (step.smoothed initial observations).law :=
          by
  have folded := (step.foldl_smooth observations initial ENNReal.one (by omega) counted).1
  rw [Measure.one_smul, take_initial initial length] at folded
  exact folded

/-- The smoothed network's first block is the filtered network. -/
public theorem smoothed_root (initial : Network) (length : initial.length = dx)
    (observations : List (List Carrier)) (counted : ∀ observed ∈ observations, observed.length =
        dy) :
    (step.smoothed initial observations).take dx = step.filtered initial observations := by
  have folded := (step.foldl_smooth observations initial ENNReal.one (by omega) counted).2
  rw [take_initial initial length] at folded
  exact folded

end LinearGaussianStep

end
end Problib.Analysis.Gaussian
