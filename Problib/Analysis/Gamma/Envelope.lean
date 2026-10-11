module

public import Problib.Analysis.Gaussian.Dominator
public import Problib.Analysis.Real.Monotone
public import Problib.Analysis.Exponential.Derivative
public import Problib.Analysis.Real.Calculus
public import Problib.Analysis.Real.Composition
import Problib.Real.Grind

/-! The log-logistic envelope of the Gamma weight.

Cheng's rejection sampler (Cheng 1977, algorithm GB) proposes from a
log-logistic law with index `λ` centered at the shape `a`. Write a proposal as
`x = a·eˢ`. The log of the Gamma weight over the proposal density, less its value
at `x = a`, is

  `Φ(s) = (a − λ)s − a(eˢ − 1) + 2·log((1 + e^{λs})/2)`,

and the sampler is exact when `Φ ≤ 0`, so that the acceptance test is a
probability. Cheng takes `λ = √(2a − 1)`. We take `λ = √a`, so `a = λ²`, which
keeps the acceptance rate bounded below in `a` and makes `Φ ≤ 0` follow from the
tangent line `1 + x ≤ eˣ`.

With `E(t) = eᵗ − 1 − t`, the tangent of the logarithm gives two bounds,
`Φ(s) ≤ −(λ²E(s) − E(λs))` and `Φ(s) ≤ −(λ²E(s) − E(−λs))`. The first
difference decreases on the line, because its derivative is
`λ(λ(eᵗ − 1) − (e^{λt} − 1))` and `λeᵗ ≤ e^{λt} + λ − 1` for `λ ≥ 1` (convexity
of the exponential). The second increases, because `eᵗ − 1 ≥ t` and
`e^{−λt} − 1 ≥ −λt`. Both vanish at zero, so the first bound closes `s ≤ 0` and
the second `s ≥ 0`.
-/

set_option autoImplicit false

namespace Problib.Analysis.Gamma.Envelope

open Problib.Real Problib.Real.Construction.Dedekind
open Problib.Analysis.Real Problib.Analysis.Gaussian Problib.Analysis.Logarithm

noncomputable section

private theorem hasDerivative_eq {function : selection.Carrier → selection.Carrier}
    {point derivative other : selection.Carrier} (differentiable : HasDerivative function point derivative)
    (same : derivative = other) : HasDerivative function point other :=
  same ▸ differentiable

/-- The exponential lies above its tangent line at `center`. -/
public theorem exp_tangent_at (center point : selection.Carrier) :
    le (mul (exp center) (add one (sub point center))) (exp point) := by
  have tangent := mul_le_mul_nonnegative_left (exp_tangent (sub point center))
    (le_of_lt (exp_positive center))
  have shifted : add center (sub point center) = point := by real_grind
  rwa [← exp_add, shifted] at tangent

/-- Bernoulli's inequality through the exponential: `λeᵗ ≤ e^{λt} + λ − 1` for
`λ ≥ 1`, at every `t`. -/
public theorem exp_bernoulli {index : selection.Carrier} (one_le : le one index)
    (point : selection.Carrier) :
    le (mul index (exp point)) (add (exp (mul index point)) (sub index one)) := by
  have far := exp_tangent_at point (mul index point)
  have near := exp_tangent_at point zero
  rw [exp_zero] at near
  have scaled := mul_le_mul_nonnegative_left near (sub_nonnegative one_le)
  have expanded : mul (sub index one) (mul (exp point) (add one (sub zero point))) =
      sub (mul (sub index one) (exp point))
        (mul (sub index one) (mul (exp point) point)) := by real_grind
  have farExpanded : mul (exp point) (add one (sub (mul index point) point)) =
      add (exp point) (mul (sub index one) (mul (exp point) point)) := by real_grind
  rw [expanded] at scaled
  rw [farExpanded] at far
  real_grind

/-- `E(t) = eᵗ − 1 − t`. -/
@[expose] public def excess (point : selection.Carrier) : selection.Carrier :=
  sub (sub (exp point) one) point

private theorem hasDerivative_excess_scaled (scale point : selection.Carrier) :
    HasDerivative (fun value => excess (mul scale value)) point
      (mul (sub (exp (mul scale point)) one) scale) := by
  have inner : HasDerivative (fun value => mul scale value) point scale :=
    hasDerivative_eq (hasDerivative_smul scale (hasDerivative_identity point)) (mul_one scale)
  have outer : HasDerivative excess (mul scale point) (sub (exp (mul scale point)) one) :=
    hasDerivative_eq (hasDerivative_sub (hasDerivative_sub (hasDerivative_exp _)
      (hasDerivative_const one _)) (hasDerivative_identity _)) (by real_grind)
  exact hasDerivative_comp outer inner

/-- `λ²E(t) − E(λt)` decreases on the line. -/
private theorem lower_antitone {index : selection.Carrier} (one_le : le one index)
    {first second : selection.Carrier} (ordered : le first second) :
    le (sub (mul (mul index index) (excess second)) (excess (mul index second)))
      (sub (mul (mul index index) (excess first)) (excess (mul index first))) := by
  let derivative : selection.Carrier → selection.Carrier := fun point =>
    sub (mul (mul index index) (sub (exp point) one)) (mul (sub (exp (mul index point)) one) index)
  refine le_of_hasDerivative_nonpositive
    (function := fun value => sub (mul (mul index index) (excess value)) (excess (mul index value)))
    (derivative := derivative) (lower := sub first one)
    (upper := add second one) (fun point _ _ => ?_) (fun point _ _ => ?_) (by real_grind)
    (by real_grind) ordered
  · have plain := hasDerivative_excess_scaled one point
    simp only [one_mul] at plain
    exact hasDerivative_sub (hasDerivative_eq (hasDerivative_smul (mul index index) plain)
      (by real_grind)) (hasDerivative_excess_scaled index point)
  · have bernoulli := exp_bernoulli one_le point
    have indexNonnegative : le zero index := le_trans (le_of_lt one_positive) one_le
    have scaled := mul_le_mul_nonnegative_left bernoulli indexNonnegative
    show le (sub (mul (mul index index) (sub (exp point) one))
      (mul (sub (exp (mul index point)) one) index)) zero
    real_grind

/-- `λ²E(t) − E(−λt)` increases on the line. -/
private theorem upper_monotone {index : selection.Carrier} (one_le : le one index)
    {first second : selection.Carrier} (ordered : le first second) :
    le (sub (mul (mul index index) (excess first)) (excess (mul (neg index) first)))
      (sub (mul (mul index index) (excess second)) (excess (mul (neg index) second))) := by
  let derivative : selection.Carrier → selection.Carrier := fun point =>
    sub (mul (mul index index) (sub (exp point) one))
      (mul (sub (exp (mul (neg index) point)) one) (neg index))
  refine le_of_hasDerivative_nonnegative
    (function := fun value => sub (mul (mul index index) (excess value))
      (excess (mul (neg index) value)))
    (derivative := derivative) (lower := sub first one)
    (upper := add second one) (fun point _ _ => ?_) (fun point _ _ => ?_) (by real_grind)
    (by real_grind) ordered
  · have plain := hasDerivative_excess_scaled one point
    simp only [one_mul] at plain
    exact hasDerivative_sub (hasDerivative_eq (hasDerivative_smul (mul index index) plain)
      (by real_grind)) (hasDerivative_excess_scaled (neg index) point)
  · have indexNonnegative : le zero index := le_trans (le_of_lt one_positive) one_le
    have grows := mul_le_mul_nonnegative_left (exp_tangent point)
      (mul_nonnegative indexNonnegative indexNonnegative)
    have falls := mul_le_mul_nonnegative_left (exp_tangent (mul (neg index) point))
      indexNonnegative
    show le zero (sub (mul (mul index index) (sub (exp point) one))
      (mul (sub (exp (mul (neg index) point)) one) (neg index)))
    real_grind

/-- The log of the Gamma weight over the log-logistic proposal, at `x = a·eˢ`,
less its value at `x = a`, with `a = λ²`. -/
@[expose] public def logRatio (index point : selection.Carrier) : selection.Carrier :=
  add (sub (mul (sub (mul index index) index) point)
      (mul (mul index index) (sub (exp point) one)))
    (mul (selection.ofRat 2)
      (logIntegral (div (add one (exp (mul index point))) (selection.ofRat 2))))

/-- The logarithm lies below its tangent line at one. -/
public theorem log_le_sub_one {value : selection.Carrier} (positive : lt zero value) :
    le (logIntegral value) (sub value one) := by
  have tangent := exp_tangent (logIntegral value)
  rw [exp_log value positive] at tangent
  real_grind

/-- The envelope: the acceptance ratio is at most one, for `λ ≥ 1`. -/
public theorem logRatio_nonpositive {index : selection.Carrier} (one_le : le one index)
    (point : selection.Carrier) : le (logRatio index point) zero := by
  have twoPositive : lt zero (selection.ofRat 2) := ofRat_two_positive
  have weight := exp_positive (mul index point)
  have halfPositive : lt zero (div (add one (exp (mul index point))) (selection.ofRat 2)) :=
    mul_positive (by real_grind) (inverse_of_positive_positive twoPositive)
  rcases le_total point zero with negative | positive
  · -- `2·log((1 + w)/2) ≤ w − 1`.
    have tangent := log_le_sub_one halfPositive
    have decreasing := lower_antitone one_le negative
    simp only [excess, mul_zero, exp_zero] at decreasing
    unfold logRatio
    have doubled := mul_le_mul_nonnegative_left tangent (le_of_lt twoPositive)
    have half : mul (selection.ofRat 2)
        (sub (div (add one (exp (mul index point))) (selection.ofRat 2)) one) =
        sub (exp (mul index point)) one := by real_grind
    rw [half] at doubled
    real_grind
  · -- `log((1 + w)/2) = λs + log((1 + 1/w)/2) ≤ λs + (1/w − 1)/2`.
    have reciprocal : exp (mul (neg index) point) = inverse (exp (mul index point)) := by
      rw [← exp_neg]
      congr 1
      real_grind
    have tailPositive : lt zero (div (add one (exp (mul (neg index) point))) (selection.ofRat 2)) :=
      mul_positive (by have := exp_positive (mul (neg index) point); real_grind)
        (inverse_of_positive_positive twoPositive)
    have split : div (add one (exp (mul index point))) (selection.ofRat 2) =
        mul (exp (mul index point))
          (div (add one (exp (mul (neg index) point))) (selection.ofRat 2)) := by
      rw [reciprocal]
      have nonzero := nonzero_of_positive weight
      have cancel := mul_inverse_cancel nonzero
      rw [div_eq_mul_inverse, div_eq_mul_inverse]
      real_grind
    have logSplit := log_mul _ _ weight tailPositive
    rw [← split, log_exp] at logSplit
    have tangent := log_le_sub_one tailPositive
    have increasing := upper_monotone one_le positive
    simp only [excess, mul_zero, exp_zero] at increasing
    unfold logRatio
    rw [logSplit]
    have doubled := mul_le_mul_nonnegative_left tangent (le_of_lt twoPositive)
    have half : mul (selection.ofRat 2)
        (sub (div (add one (exp (mul (neg index) point))) (selection.ofRat 2)) one) =
        sub (exp (mul (neg index) point)) one := by real_grind
    rw [half] at doubled
    real_grind

end

end Problib.Analysis.Gamma.Envelope
