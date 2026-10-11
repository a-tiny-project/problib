module

public import Problib.Inference.Involutive
public import Problib.Measure.Real.Invariant
public import Problib.Measure.Real.Finiteness
public import Problib.Real.Grind

set_option autoImplicit false

/-! Leapfrog as a reversible integrator.

Hamiltonian Monte Carlo proposes by integrating a position and a momentum
forward, then negating the momentum. `hmc_invariant` and
`involutive_invariant_of_reference` need that proposal to be an involution that
preserves a reference measure (`ReversibleIntegrator`). This file builds the
instance for leapfrog once, over any `InvariantVolume` on the position space,
against the product of that volume with itself (`phaseVolume`).

Each leapfrog substep is a shear: a kick `(x, p) ↦ (x, p + f(x))` moves the
momentum by an amount that depends only on the position, and a drift
`(x, p) ↦ (x + v(p), p)` moves the position by an amount that depends only on
the momentum. Within each fiber a shear is a translation, which the volume
preserves, so Tonelli carries the fiberwise fact to the product
(`prod_map_fiber`, `prod_map_fiber_first`). Negating the momentum is a
reflection in each fiber.

Reversibility is algebraic, from the volume's three laws. A kick undone through
the flip is the flip, `kick (flip (kick z)) = flip z`, for any impulse. A drift
satisfies the same equation when its velocity `v` is odd. One leapfrog step is
the palindrome kick, drift, kick, so `step (flip (step z)) = flip z`, and
induction gives the same for any number of steps (`leapfrog_reverses`). The
flip after the steps then makes the proposal an involution.

The impulse is any measurable function. Nothing here asks it to be the
gradient of a log density: the accept test corrects any deterministic
impulse, so a wrong force costs acceptance and never correctness. The velocity
is any measurable odd function; with a step `ε` it is `p ↦ ε·p`, and with a
mass matrix `M` it is `p ↦ ε·M⁻¹p`.

The instances are Lebesgue measure on a line (`realLeapfrogIntegrator`), on
`n` coordinates (`piLeapfrogIntegrator`), and on any product of invariant
volumes, such as the pair `ℝ × ℝ` Church spells a plane with. -/

namespace Problib.Inference

open Problib.Real Problib.Measure
open Problib.Real.Construction.Dedekind
open Problib.Measure.Real (Carrier borel measurable_mul)

universe u v
variable {α : Type u} {space : Space α}

public section

/-- The reference of the leapfrog integrator: the volume on position and on
momentum. -/
@[expose] noncomputable def phaseVolume (volume : InvariantVolume space) :
    Measure (Space.product space space) :=
  Measure.prod volume.measure volume.measure volume.finite

/-! ### Substeps -/

/-- A kick moves the momentum by an impulse read at the position. -/
@[expose] def kick (volume : InvariantVolume space) (impulse : α → α) (point : α × α) : α × α :=
  (point.1, volume.add point.2 (impulse point.1))

/-- A drift moves the position by a velocity read at the momentum. -/
@[expose] def drift (volume : InvariantVolume space) (velocity : α → α) (point : α × α) :
    α × α :=
  (volume.add point.1 (velocity point.2), point.2)

/-- The flip negates the momentum. -/
@[expose] def flipMomentum (volume : InvariantVolume space) (point : α × α) : α × α :=
  (point.1, volume.neg point.2)

variable (volume : InvariantVolume space)

theorem kick_measurable {impulse : α → α} (impulseMeasurable : MeasurableMap space space impulse) :
    MeasurableMap (Space.product space space) (Space.product space space) (kick volume impulse) :=
  Space.pair_measurable (Space.first_measurable _ _)
    (MeasurableMap.comp volume.addMeasurable (Space.pair_measurable (Space.second_measurable _ _)
      (MeasurableMap.comp impulseMeasurable (Space.first_measurable _ _))))

theorem drift_measurable {velocity : α → α}
    (velocityMeasurable : MeasurableMap space space velocity) :
    MeasurableMap (Space.product space space) (Space.product space space) (drift volume velocity) :=
  Space.pair_measurable
    (MeasurableMap.comp volume.addMeasurable (Space.pair_measurable (Space.first_measurable _ _)
      (MeasurableMap.comp velocityMeasurable (Space.second_measurable _ _))))
    (Space.second_measurable _ _)

theorem flipMomentum_measurable :
    MeasurableMap (Space.product space space) (Space.product space space)
      (flipMomentum volume) :=
  Space.pair_measurable (Space.first_measurable _ _)
    (MeasurableMap.comp volume.negMeasurable (Space.second_measurable _ _))

/-- A kick is a shear of the momentum, so it preserves phase volume. -/
theorem map_kick {impulse : α → α} (impulseMeasurable : MeasurableMap space space impulse) :
    (phaseVolume volume).map (kick volume impulse) (kick_measurable volume impulseMeasurable) =
      phaseVolume volume :=
  prod_map_fiber volume.measure volume.measure volume.finite
    (fun position momentum => volume.add momentum (impulse position))
    (kick_measurable volume impulseMeasurable)
    (fun position => volume.translate (impulse position))

/-- A drift is a shear of the position, so it preserves phase volume. -/
theorem map_drift {velocity : α → α} (velocityMeasurable : MeasurableMap space space velocity) :
    (phaseVolume volume).map (drift volume velocity) (drift_measurable volume velocityMeasurable) =
      phaseVolume volume :=
  prod_map_fiber_first volume.measure volume.measure volume.finite volume.finite
    (fun momentum position => volume.add position (velocity momentum))
    (drift_measurable volume velocityMeasurable)
    (fun momentum => volume.translate (velocity momentum))

/-- The flip reflects each momentum fiber, so it preserves phase volume. -/
theorem map_flipMomentum :
    (phaseVolume volume).map (flipMomentum volume) (flipMomentum_measurable volume) =
      phaseVolume volume :=
  prod_map_fiber volume.measure volume.measure volume.finite (fun _ momentum => volume.neg momentum)
    (flipMomentum_measurable volume) (fun _ => volume.reflect)

theorem flipMomentum_flipMomentum (point : α × α) :
    flipMomentum volume (flipMomentum volume point) = point := by
  change (point.1, volume.neg (volume.neg point.2)) = point
  rw [volume.neg_neg]

/-- A kick undone through the flip is the flip, for any impulse. -/
theorem kick_flip_kick (impulse : α → α) (point : α × α) :
    kick volume impulse (flipMomentum volume (kick volume impulse point)) =
      flipMomentum volume point := by
  change (point.1, volume.add (volume.neg (volume.add point.2 (impulse point.1)))
    (impulse point.1)) = (point.1, volume.neg point.2)
  have cancel := volume.add_neg_cancel_right (volume.neg point.2) (volume.neg (impulse point.1))
  rw [volume.neg_neg] at cancel
  rw [volume.neg_add, cancel]

/-- A drift undone through the flip is the flip, when the velocity is odd. -/
theorem drift_flip_drift {velocity : α → α}
    (velocityOdd : ∀ momentum, velocity (volume.neg momentum) = volume.neg (velocity momentum))
    (point : α × α) :
    drift volume velocity (flipMomentum volume (drift volume velocity point)) =
      flipMomentum volume point := by
  change (volume.add (volume.add point.1 (velocity point.2)) (velocity (volume.neg point.2)),
    volume.neg point.2) = (point.1, volume.neg point.2)
  rw [velocityOdd, volume.add_neg_cancel_right]

/-! ### Leapfrog -/

/-- One leapfrog step: a kick, a drift of the full step, and a kick. With the
impulse `x ↦ (ε/2)·g(x)` and the velocity `p ↦ ε·p`, this is the
Störmer–Verlet step for the force `g`. -/
@[expose] def leapfrogStep (impulse velocity : α → α) (point : α × α) : α × α :=
  kick volume impulse (drift volume velocity (kick volume impulse point))

/-- `count` leapfrog steps. -/
@[expose] def leapfrog (impulse velocity : α → α) : Nat → α × α → α × α
  | 0 => fun point => point
  | count + 1 => fun point =>
      leapfrogStep volume impulse velocity (leapfrog impulse velocity count point)

variable {volume}

theorem leapfrogStep_measurable {impulse velocity : α → α}
    (impulseMeasurable : MeasurableMap space space impulse)
    (velocityMeasurable : MeasurableMap space space velocity) :
    MeasurableMap (Space.product space space) (Space.product space space)
      (leapfrogStep volume impulse velocity) :=
  MeasurableMap.comp (kick_measurable volume impulseMeasurable)
    (MeasurableMap.comp (drift_measurable volume velocityMeasurable)
      (kick_measurable volume impulseMeasurable))

theorem leapfrog_measurable {impulse velocity : α → α}
    (impulseMeasurable : MeasurableMap space space impulse)
    (velocityMeasurable : MeasurableMap space space velocity) :
    (count : Nat) → MeasurableMap (Space.product space space) (Space.product space space)
      (leapfrog volume impulse velocity count)
  | 0 => MeasurableMap.identity _
  | count + 1 => MeasurableMap.comp (leapfrogStep_measurable impulseMeasurable velocityMeasurable)
      (leapfrog_measurable impulseMeasurable velocityMeasurable count)

variable (volume)

/-- The steps commute with one step: the last step may also be read first. -/
theorem leapfrog_succ' (impulse velocity : α → α) (count : Nat) (point : α × α) :
    leapfrog volume impulse velocity (count + 1) point =
      leapfrog volume impulse velocity count (leapfrogStep volume impulse velocity point) := by
  induction count generalizing point with
  | zero => rfl
  | succ count previous =>
      change leapfrogStep volume impulse velocity
        (leapfrog volume impulse velocity (count + 1) point) = _
      rw [previous]
      rfl

/-- One step undone through the flip is the flip. -/
theorem leapfrogStep_reverses (impulse : α → α) {velocity : α → α}
    (velocityOdd : ∀ momentum, velocity (volume.neg momentum) = volume.neg (velocity momentum))
    (point : α × α) :
    leapfrogStep volume impulse velocity
        (flipMomentum volume (leapfrogStep volume impulse velocity point)) =
      flipMomentum volume point := by
  unfold leapfrogStep
  rw [kick_flip_kick, drift_flip_drift volume velocityOdd, kick_flip_kick]

/-- Any number of steps undone through the flip is the flip. -/
theorem leapfrog_reverses (impulse : α → α) {velocity : α → α}
    (velocityOdd : ∀ momentum, velocity (volume.neg momentum) = volume.neg (velocity momentum))
    (count : Nat) (point : α × α) :
    leapfrog volume impulse velocity count
        (flipMomentum volume (leapfrog volume impulse velocity count point)) =
      flipMomentum volume point := by
  induction count generalizing point with
  | zero => rfl
  | succ count previous =>
      change leapfrogStep volume impulse velocity (leapfrog volume impulse velocity count
        (flipMomentum volume (leapfrog volume impulse velocity (count + 1) point))) = _
      rw [leapfrog_succ', previous, leapfrogStep_reverses volume impulse velocityOdd]

variable {volume}

/-- Any number of steps preserves phase volume. -/
theorem map_leapfrog {impulse velocity : α → α}
    (impulseMeasurable : MeasurableMap space space impulse)
    (velocityMeasurable : MeasurableMap space space velocity) :
    (count : Nat) → (phaseVolume volume).map (leapfrog volume impulse velocity count)
      (leapfrog_measurable impulseMeasurable velocityMeasurable count) = phaseVolume volume
  | 0 => Measure.map_id (phaseVolume volume)
  | count + 1 => by
      have previous := map_leapfrog impulseMeasurable velocityMeasurable count
      calc
        (phaseVolume volume).map (leapfrog volume impulse velocity (count + 1))
            (leapfrog_measurable impulseMeasurable velocityMeasurable (count + 1)) =
          ((((phaseVolume volume).map (leapfrog volume impulse velocity count)
            (leapfrog_measurable impulseMeasurable velocityMeasurable count)).map
            (kick volume impulse) (kick_measurable volume impulseMeasurable)).map
            (drift volume velocity) (drift_measurable volume velocityMeasurable)).map
            (kick volume impulse) (kick_measurable volume impulseMeasurable) := by
          rw [Measure.map_comp, Measure.map_comp, Measure.map_comp]
          rfl
        _ = phaseVolume volume := by
          rw [previous, map_kick volume impulseMeasurable, map_drift volume velocityMeasurable,
            map_kick volume impulseMeasurable]

variable (volume)

/-- Leapfrog with momentum negation is a reversible integrator against phase
volume, for any measurable impulse, any measurable odd velocity and any number
of steps. -/
@[expose] noncomputable def leapfrogIntegrator {impulse velocity : α → α}
    (impulseMeasurable : MeasurableMap space space impulse)
    (velocityMeasurable : MeasurableMap space space velocity)
    (velocityOdd : ∀ momentum, velocity (volume.neg momentum) = volume.neg (velocity momentum))
    (count : Nat) :
    ReversibleIntegrator space space (phaseVolume volume) where
  integrate := leapfrog volume impulse velocity count
  integrateMeasurable := leapfrog_measurable (volume := volume) impulseMeasurable
    velocityMeasurable count
  flip := flipMomentum volume
  flipMeasurable := flipMomentum_measurable volume
  involutive point := by
    rw [leapfrog_reverses volume impulse velocityOdd, flipMomentum_flipMomentum]
  referenceInvariant := by
    have composed := Measure.map_comp (phaseVolume volume) _ _
      (leapfrog_measurable (volume := volume) impulseMeasurable velocityMeasurable count)
      (flipMomentum_measurable volume)
    rw [map_leapfrog (volume := volume) impulseMeasurable velocityMeasurable,
      map_flipMomentum] at composed
    exact composed.symm

/-- The integrator's trajectory is the leapfrog steps, then the flip. -/
theorem leapfrogIntegrator_trajectory {impulse velocity : α → α}
    (impulseMeasurable : MeasurableMap space space impulse)
    (velocityMeasurable : MeasurableMap space space velocity)
    (velocityOdd : ∀ momentum, velocity (volume.neg momentum) = volume.neg (velocity momentum))
    (count : Nat) (point : α × α) :
    (leapfrogIntegrator volume impulseMeasurable velocityMeasurable velocityOdd count).trajectory
        point =
      flipMomentum volume (leapfrog volume impulse velocity count point) :=
  rfl

/-! ### Instances -/

/-- The velocity of a scalar step on a line, `p ↦ ε·p`. -/
theorem scale_measurable (step : Carrier) : MeasurableMap borel borel (mul step) :=
  measurable_mul (MeasurableMap.constant _ _ step) (MeasurableMap.identity _)

theorem scale_odd (step : Carrier) (momentum : Carrier) :
    mul step (InvariantVolume.real.neg momentum) = InvariantVolume.real.neg (mul step momentum) := by
  change mul step (neg momentum) = neg (mul step momentum)
  real_grind

/-- Leapfrog on a line against Lebesgue measure on `ℝ × ℝ`, with the velocity
`p ↦ ε·p`. -/
@[expose] noncomputable def realLeapfrogIntegrator {impulse : Carrier → Carrier}
    (impulseMeasurable : MeasurableMap borel borel impulse) (step : Carrier) (count : Nat) :
    ReversibleIntegrator borel borel (phaseVolume InvariantVolume.real) :=
  leapfrogIntegrator InvariantVolume.real impulseMeasurable (scale_measurable step)
    (scale_odd step) count

/-- The velocity of a scalar step on `n` coordinates, `p ↦ ε·p`. -/
@[expose] noncomputable def scalePi (dimension : Nat) (step : Carrier) (momentum : Fin dimension → Carrier) :
    Fin dimension → Carrier :=
  fun index => mul step (momentum index)

theorem scalePi_measurable (dimension : Nat) (step : Carrier) :
    MeasurableMap (Space.pi (fun _ : Fin dimension => borel))
      (Space.pi (fun _ : Fin dimension => borel)) (scalePi dimension step) :=
  Space.pi_measurable fun index =>
    MeasurableMap.comp (scale_measurable step)
      (Space.coordinate_measurable (fun _ : Fin dimension => borel) index)

theorem scalePi_odd (dimension : Nat) (step : Carrier) (momentum : Fin dimension → Carrier) :
    scalePi dimension step ((InvariantVolume.pi dimension).neg momentum) =
      (InvariantVolume.pi dimension).neg (scalePi dimension step momentum) := by
  funext index
  change mul step (neg (momentum index)) = neg (mul step (momentum index))
  real_grind

/-- Leapfrog on `n` coordinates against `volumePi n` on position and momentum,
with the velocity `p ↦ ε·p`. -/
@[expose] noncomputable def piLeapfrogIntegrator (dimension : Nat)
    {impulse : (Fin dimension → Carrier) → Fin dimension → Carrier}
    (impulseMeasurable : MeasurableMap (Space.pi (fun _ : Fin dimension => borel))
      (Space.pi (fun _ : Fin dimension => borel)) impulse)
    (step : Carrier) (count : Nat) :
    ReversibleIntegrator (Space.pi (fun _ : Fin dimension => borel))
      (Space.pi (fun _ : Fin dimension => borel)) (phaseVolume (InvariantVolume.pi dimension)) :=
  leapfrogIntegrator (InvariantVolume.pi dimension) impulseMeasurable
    (scalePi_measurable dimension step) (scalePi_odd dimension step) count

/-! ### The position chain -/

/-- One HMC step on the position alone: draw a momentum, integrate, and accept
the new position or keep the old one. When the position law extended by the
momentum has a density against the integrator's reference, the step leaves the
position law invariant. It is `hmc_invariant` read on the position: the
momentum is the involutive kernel's auxiliary draw, so no refresh step and no
marginalization appear. -/
theorem hmc_position_invariant {γ : Type u} {δ : Type v} {state : Space γ}
    {auxiliarySpace : Space δ}
    (positionLaw : Measure state)
    (momentum : Kernel state auxiliarySpace)
    (momentumFinite : Kernel.IsSFinite momentum)
    (momentumMarkov : ∀ input, Measure.IsProbability (momentum input))
    (reference : Measure (Space.product state auxiliarySpace))
    (integrator : ReversibleIntegrator state auxiliarySpace reference)
    {density : γ × δ → Carrier}
    (densityMeasurable : MeasurableMap (Space.product state auxiliarySpace) borel density)
    (represents : positionLaw.semiproduct momentum momentumFinite =
      reference.withDensity (fun point => ENNReal.ofReal (density point))) :
    KernelInvariant positionLaw
      (involutiveKernel momentum momentumFinite integrator.trajectory
        integrator.trajectory_measurable
        (involutiveAccept integrator.trajectory density)
        (involutiveAccept_measurable integrator.trajectory integrator.trajectory_measurable
          densityMeasurable)) :=
  involutive_invariant_of_reference positionLaw momentum momentumFinite momentumMarkov
    integrator.trajectory integrator.trajectory_measurable integrator.trajectory_involutive
    reference integrator.referenceInvariant densityMeasurable represents

end

end Problib.Inference
