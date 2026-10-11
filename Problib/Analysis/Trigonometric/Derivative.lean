module

public import Problib.Analysis.Trigonometric
public import Problib.Analysis.Real.Composition
public import Problib.Analysis.Real.MeanValue
import Problib.Real.Grind

/-! The identities of sine and cosine, from their derivatives.

A pair of functions that rotates under differentiation, `f' = g` and
`g' = -f`, keeps the energy `f² + g²` constant, because its derivative is
`2fg - 2gf`. Sine and cosine form such a pair, so `sin² + cos²` keeps its value
one at zero. Each other identity is a difference that forms such a pair and
vanishes at zero, so its energy is zero everywhere and the difference vanishes:
the parities, with the difference `sin (-x) + sin x`, and the addition formulas
at a fixed second argument.
-/

set_option autoImplicit false

namespace Problib.Analysis

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real

noncomputable section

/-- Sine is continuous at every point. -/
public theorem sin_continuous (point : selection.Carrier) :
    Approaches (fun displacement => sin (add point displacement)) (sin point) :=
  hasDerivative_continuous (hasDerivative_sin point)

/-- Cosine is continuous at every point. -/
public theorem cos_continuous (point : selection.Carrier) :
    Approaches (fun displacement => cos (add point displacement)) (cos point) :=
  hasDerivative_continuous (hasDerivative_cos point)

section Rotation

variable {first second : selection.Carrier → selection.Carrier}
  (firstDerivative : ∀ point, HasDerivative first point (second point))
  (secondDerivative : ∀ point, HasDerivative second point (neg (first point)))

include firstDerivative secondDerivative

/-- A rotating pair keeps its energy. -/
private theorem energy_constant (point other : selection.Carrier) :
    add (mul (first point) (first point)) (mul (second point) (second point)) =
      add (mul (first other) (first other)) (mul (second other) (second other)) := by
  apply eq_of_hasDerivative_zero (function := fun value =>
    add (mul (first value) (first value)) (mul (second value) (second value)))
  intro value
  have energy := hasDerivative_add
    (hasDerivative_mul (firstDerivative value) (firstDerivative value))
    (hasDerivative_mul (secondDerivative value) (secondDerivative value))
  have cancels : add
      (add (mul (second value) (first value)) (mul (first value) (second value)))
      (add (mul (neg (first value)) (second value))
        (mul (second value) (neg (first value)))) = zero := by
    real_grind
  rwa [cancels] at energy

/-- A rotating pair that vanishes at zero vanishes everywhere. -/
private theorem rotation_vanishes (firstZero : first zero = zero)
    (secondZero : second zero = zero) (point : selection.Carrier) :
    first point = zero ∧ second point = zero := by
  have energy := energy_constant firstDerivative secondDerivative point zero
  rw [firstZero, secondZero, mul_zero, add_zero] at energy
  have firstSquare := mul_self_nonnegative (first point)
  have secondSquare := mul_self_nonnegative (second point)
  have firstFlat : mul (first point) (first point) = zero := by real_grind
  have secondFlat : mul (second point) (second point) = zero := by real_grind
  exact ⟨(mul_eq_zero_iff.mp firstFlat).elim id id,
    (mul_eq_zero_iff.mp secondFlat).elim id id⟩

end Rotation

/-- Pythagoras: `sin² x + cos² x = 1`. -/
public theorem sin_sq_add_cos_sq (point : selection.Carrier) :
    add (mul (sin point) (sin point)) (mul (cos point) (cos point)) = one := by
  rw [energy_constant hasDerivative_sin hasDerivative_cos point zero, sin_zero, cos_zero,
    mul_zero, mul_one, zero_add]

private theorem abs_le_one_of_square {value : selection.Carrier}
    (square : le (mul value value) one) : le (abs value) one := by
  have magnitude : mul (abs value) (abs value) = mul value value := by
    rw [← abs_mul, abs_of_nonnegative (mul_self_nonnegative value)]
  by_cases within : le (abs value) one
  · exact within
  · have beyond := lt_of_not_le within
    have positive := lt_trans one_positive beyond
    have grown := mul_lt_mul_positive_left beyond positive
    rw [mul_one, magnitude] at grown
    exact False.elim (lt_irrefl one (lt_of_lt_of_le (lt_trans beyond grown) square))

public theorem abs_sin_le_one (point : selection.Carrier) : le (abs (sin point)) one := by
  apply abs_le_one_of_square
  have identity := sin_sq_add_cos_sq point
  have other := mul_self_nonnegative (cos point)
  real_grind

public theorem abs_cos_le_one (point : selection.Carrier) : le (abs (cos point)) one := by
  apply abs_le_one_of_square
  have identity := sin_sq_add_cos_sq point
  have other := mul_self_nonnegative (sin point)
  real_grind

private theorem hasDerivative_neg_argument {function : selection.Carrier → selection.Carrier}
    {point derivative : selection.Carrier}
    (differentiable : HasDerivative function (neg point) derivative) :
    HasDerivative (fun value => function (neg value)) point (neg derivative) := by
  have composed := hasDerivative_comp (inner := fun value => neg value) differentiable
    (hasDerivative_neg (hasDerivative_identity point))
  rwa [mul_neg, mul_one] at composed

private theorem parity (point : selection.Carrier) :
    sub (cos (neg point)) (cos point) = zero ∧
      add (sin (neg point)) (sin point) = zero := by
  apply rotation_vanishes
    (first := fun value => sub (cos (neg value)) (cos value))
    (second := fun value => add (sin (neg value)) (sin value))
  · intro value
    have derivative := hasDerivative_sub
      (hasDerivative_neg_argument (hasDerivative_cos (neg value))) (hasDerivative_cos value)
    have equal : sub (neg (neg (sin (neg value)))) (neg (sin value)) =
        add (sin (neg value)) (sin value) := by
      real_grind
    rwa [equal] at derivative
  · intro value
    have derivative := hasDerivative_add
      (hasDerivative_neg_argument (hasDerivative_sin (neg value))) (hasDerivative_sin value)
    have equal : add (neg (cos (neg value))) (cos value) =
        neg (sub (cos (neg value)) (cos value)) := by
      real_grind
    rwa [equal] at derivative
  · change sub (cos (neg zero)) (cos zero) = zero
    rw [neg_zero, sub_self]
  · change add (sin (neg zero)) (sin zero) = zero
    rw [neg_zero, sin_zero, add_zero]

public theorem cos_neg (point : selection.Carrier) : cos (neg point) = cos point := by
  have vanishes := (parity point).1
  real_grind

public theorem sin_neg (point : selection.Carrier) : sin (neg point) = neg (sin point) := by
  have vanishes := (parity point).2
  real_grind

private theorem hasDerivative_shifted {function : selection.Carrier → selection.Carrier}
    {point derivative : selection.Carrier} (shift : selection.Carrier)
    (differentiable : HasDerivative function (add point shift) derivative) :
    HasDerivative (fun value => function (add value shift)) point derivative := by
  have composed := hasDerivative_comp (inner := fun value => add value shift) differentiable
    (hasDerivative_add (first := fun value => value) (second := fun _ => shift)
      (hasDerivative_identity point) (hasDerivative_const shift point))
  rwa [add_zero, mul_one] at composed

private theorem addition (shift point : selection.Carrier) :
    sub (sin (add point shift))
        (add (mul (sin point) (cos shift)) (mul (cos point) (sin shift))) = zero ∧
      sub (cos (add point shift))
        (sub (mul (cos point) (cos shift)) (mul (sin point) (sin shift))) = zero := by
  apply rotation_vanishes
    (first := fun value => sub (sin (add value shift))
      (add (mul (sin value) (cos shift)) (mul (cos value) (sin shift))))
    (second := fun value => sub (cos (add value shift))
      (sub (mul (cos value) (cos shift)) (mul (sin value) (sin shift))))
  · intro value
    have derivative := hasDerivative_sub
      (hasDerivative_shifted shift (hasDerivative_sin (add value shift)))
      (hasDerivative_add (hasDerivative_mul (hasDerivative_sin value)
          (hasDerivative_const (cos shift) value))
        (hasDerivative_mul (hasDerivative_cos value) (hasDerivative_const (sin shift) value)))
    have equal : sub (cos (add value shift))
        (add (add (mul (cos value) (cos shift)) (mul (sin value) zero))
          (add (mul (neg (sin value)) (sin shift)) (mul (cos value) zero))) =
        sub (cos (add value shift))
          (sub (mul (cos value) (cos shift)) (mul (sin value) (sin shift))) := by
      real_grind
    rwa [equal] at derivative
  · intro value
    have derivative := hasDerivative_sub
      (hasDerivative_shifted shift (hasDerivative_cos (add value shift)))
      (hasDerivative_sub (hasDerivative_mul (hasDerivative_cos value)
          (hasDerivative_const (cos shift) value))
        (hasDerivative_mul (hasDerivative_sin value) (hasDerivative_const (sin shift) value)))
    have equal : sub (neg (sin (add value shift)))
        (sub (add (mul (neg (sin value)) (cos shift)) (mul (cos value) zero))
          (add (mul (cos value) (sin shift)) (mul (sin value) zero))) =
        neg (sub (sin (add value shift))
          (add (mul (sin value) (cos shift)) (mul (cos value) (sin shift)))) := by
      real_grind
    rwa [equal] at derivative
  · change sub (sin (add zero shift))
      (add (mul (sin zero) (cos shift)) (mul (cos zero) (sin shift))) = zero
    rw [zero_add, sin_zero, cos_zero]
    real_grind
  · change sub (cos (add zero shift))
      (sub (mul (cos zero) (cos shift)) (mul (sin zero) (sin shift))) = zero
    rw [zero_add, sin_zero, cos_zero]
    real_grind

/-- The addition formula for sine. -/
public theorem sin_add (first second : selection.Carrier) :
    sin (add first second) =
      add (mul (sin first) (cos second)) (mul (cos first) (sin second)) := by
  have vanishes := (addition second first).1
  real_grind

/-- The addition formula for cosine. -/
public theorem cos_add (first second : selection.Carrier) :
    cos (add first second) =
      sub (mul (cos first) (cos second)) (mul (sin first) (sin second)) := by
  have vanishes := (addition second first).2
  real_grind

end

end Problib.Analysis
