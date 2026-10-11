module

public import Problib.Analysis.Arctangent.Function
public import Problib.Analysis.Trigonometric.Pi
import Problib.Real.Grind

/-! The arctangent inverts the tangent of sine and cosine.

Along the arctangent, the tilt `ψ x = sin (atan x) - x · cos (atan x)` satisfies
`ψ' = x · K x · ψ` with `K x = 1 / (1 + x²)`, so its energy `ψ² · K` has zero
derivative on the whole line. The energy is zero at zero, where the arctangent
is zero, so the tilt vanishes and `sin (atan x) = x · cos (atan x)`. Cosine is
positive on the arctangent's range `(-π/2, π/2)`, which gives `tan ∘ atan = id`.
In the other order, `atan (tan t)` and `t` have a zero sine difference and lie
less than `π` apart, so they are equal.
-/

set_option autoImplicit false

namespace Problib.Analysis


open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real

local notation "K(" t ")" => inverse (add one (mul t t))

noncomputable section

/-- The gap between sine and the tangent line along the arctangent. -/
private def tilt (point : selection.Carrier) : selection.Carrier :=
  sub (sin (atan point)) (mul point (cos (atan point)))

/-- The tilt's energy, `ψ² / (1 + x²)`. -/
private def tiltEnergy (point : selection.Carrier) : selection.Carrier :=
  mul (mul (tilt point) (tilt point)) (K(point))

private theorem denominator_nonzero (point : selection.Carrier) :
    add one (mul point point) ≠ zero := by
  apply nonzero_of_positive
  have square := mul_self_nonnegative point
  real_grind

private theorem hasDerivative_tiltEnergy (point : selection.Carrier) :
    HasDerivative tiltEnergy point zero := by
  have arctangent := hasDerivative_atan point
  have sine := hasDerivative_comp (inner := atan) (hasDerivative_sin (atan point)) arctangent
  have cosine := hasDerivative_comp (inner := atan) (hasDerivative_cos (atan point)) arctangent
  have slope := hasDerivative_sub sine
    (hasDerivative_mul (hasDerivative_identity point) cosine)
  have denominator := hasDerivative_add (first := fun _ => one)
    (second := fun value => mul value value) (hasDerivative_const one point)
    (hasDerivative_mul (hasDerivative_identity point) (hasDerivative_identity point))
  have reciprocal := hasDerivative_inverse denominator (denominator_nonzero point)
  have energy := hasDerivative_mul (hasDerivative_mul slope slope) reciprocal
  have transport : ∀ derivative, HasDerivative tiltEnergy point derivative →
      derivative = zero → HasDerivative tiltEnergy point zero :=
    fun _ differentiable vanishes => vanishes ▸ differentiable
  refine transport _ energy ?_
  have nonzero := denominator_nonzero point
  generalize sin (atan point) = sine at *
  generalize cos (atan point) = cosine at *
  real_grind

private theorem tilt_vanishes (point : selection.Carrier) : tilt point = zero := by
  have constant := eq_of_hasDerivative_zero hasDerivative_tiltEnergy point zero
  have atZero : tiltEnergy zero = zero := by
    unfold tiltEnergy tilt
    rw [atan_zero, sin_zero]
    real_grind
  rw [atZero] at constant
  unfold tiltEnergy at constant
  have kernelNonzero : K(point) ≠ zero :=
    nonzero_of_positive (Arctangent.kernel_positive point)
  have square : mul (tilt point) (tilt point) = zero :=
    (mul_eq_zero_iff.mp constant).elim id (fun other => False.elim (kernelNonzero other))
  exact (mul_eq_zero_iff.mp square).elim id id

/-- Along the arctangent, sine is the argument times cosine. -/
public theorem sin_atan (x : selection.Carrier) : sin (atan x) = mul x (cos (atan x)) := by
  have vanished := tilt_vanishes x
  unfold tilt at vanished
  real_grind

/-- Cosine is positive along the arctangent. -/
public theorem cos_atan_positive (x : selection.Carrier) : lt zero (cos (atan x)) :=
  cos_positive (neg_half_pi_lt_atan x) (atan_lt_half_pi x)

/-- Along the arctangent, `cos² · (1 + x²) = 1`. -/
public theorem cos_atan_sq (x : selection.Carrier) :
    mul (mul (cos (atan x)) (cos (atan x))) (add one (mul x x)) = one := by
  have pythagoras := sin_sq_add_cos_sq (atan x)
  rw [sin_atan] at pythagoras
  generalize cos (atan x) = cosine at *
  real_grind

/-- The tangent of the arctangent is the identity. -/
public theorem tan_atan (x : selection.Carrier) : div (sin (atan x)) (cos (atan x)) = x := by
  have nonzero := nonzero_of_positive (cos_atan_positive x)
  rw [sin_atan]
  generalize cos (atan x) = cosine at *
  real_grind

/-- On `(-π/2, π/2)` the arctangent of the tangent is the identity. -/
public theorem atan_tan {angle : selection.Carrier} (lower : lt (neg (half pi)) angle)
    (upper : lt angle (half pi)) : atan (div (sin angle) (cos angle)) = angle := by
  let tangent := div (sin angle) (cos angle)
  have cosinePositive := cos_positive lower upper
  have cosineNonzero := nonzero_of_positive cosinePositive
  have tangentSine : mul tangent (cos angle) = sin angle := by
    change mul (div (sin angle) (cos angle)) (cos angle) = sin angle
    generalize sin angle = sine at *
    generalize cos angle = cosine at *
    real_grind
  have difference : sin (sub (atan tangent) angle) = zero := by
    rw [sub_eq_add_neg, sin_add, cos_neg, sin_neg, sin_atan, ← tangentSine]
    real_grind
  have below := atan_lt_half_pi tangent
  have above := neg_half_pi_lt_atan tangent
  have halves := add_half pi
  rcases lt_trichotomy (atan tangent) angle with less | equal | greater
  · have reversed := sin_positive (show lt zero (sub angle (atan tangent)) by real_grind)
      (show lt (sub angle (atan tangent)) pi by real_grind)
    have swapped : sub angle (atan tangent) = neg (sub (atan tangent) angle) := by real_grind
    rw [swapped, sin_neg, difference, neg_zero] at reversed
    exact absurd reversed (lt_irrefl zero)
  · exact equal
  · have positive := sin_positive (show lt zero (sub (atan tangent) angle) by real_grind)
      (show lt (sub (atan tangent) angle) pi by real_grind)
    rw [difference] at positive
    exact absurd positive (lt_irrefl zero)

end

end Problib.Analysis
