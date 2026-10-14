module

public import Problib.Analysis.Trigonometric.Series
import Problib.Real.Grind

/-! Sine and cosine as factorial series.

Cosine is `Σ wₙ xⁿ / n!` with the weights `1, 0, -1, 0` repeating, and sine is
the same series with the weights `0, 1, 0, -1`. Moving the sine weights one
place later gives the cosine weights, and moving the cosine weights gives the
negated sine weights, so the derivatives are read off the weights: sine
differentiates to cosine and cosine to the negated sine.
-/

set_option autoImplicit false

namespace Problib.Analysis

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real
open Problib.Analysis.Trigonometric

noncomputable section

/-- The cosine weights `1, 0, -1, 0`, repeating. -/
@[expose] public def cosineValues (index : Nat) : selection.Carrier :=
  match index % 4 with
  | 0 => one
  | 2 => neg one
  | _ => zero

/-- The sine weights `0, 1, 0, -1`, repeating. -/
@[expose] public def sineValues (index : Nat) : selection.Carrier :=
  match index % 4 with
  | 1 => one
  | 3 => neg one
  | _ => zero

private theorem residues (index : Nat) :
    index % 4 = 0 ∨ index % 4 = 1 ∨ index % 4 = 2 ∨ index % 4 = 3 := by
  omega

private theorem abs_one_le : le (abs one) one := by
  rw [abs_of_nonnegative one_nonnegative]
  exact le_refl one

private theorem abs_neg_one_le : le (abs (neg one)) one := by
  rw [abs_neg]
  exact abs_one_le

private theorem abs_zero_le : le (abs zero) one := by
  rw [abs_zero]
  exact one_nonnegative

public theorem cosineValues_bounded (index : Nat) : le (abs (cosineValues index)) one := by
  unfold cosineValues
  rcases residues index with residue | residue | residue | residue <;>
    simp only [residue] <;>
    first | exact abs_one_le | exact abs_neg_one_le | exact abs_zero_le

public theorem sineValues_bounded (index : Nat) : le (abs (sineValues index)) one := by
  unfold sineValues
  rcases residues index with residue | residue | residue | residue <;>
    simp only [residue] <;>
    first | exact abs_one_le | exact abs_neg_one_le | exact abs_zero_le

/-- The cosine weights, bounded by one. -/
@[expose] public def cosineWeight : Weight := ⟨cosineValues, one, cosineValues_bounded⟩

/-- The sine weights, bounded by one. -/
@[expose] public def sineWeight : Weight := ⟨sineValues, one, sineValues_bounded⟩

/-- Sine, the series `Σ (-1)ᵏ x²ᵏ⁺¹ / (2k + 1)!`. -/
@[expose] public def sin (point : selection.Carrier) : selection.Carrier :=
  weighted sineWeight point

/-- Cosine, the series `Σ (-1)ᵏ x²ᵏ / (2k)!`. -/
@[expose] public def cos (point : selection.Carrier) : selection.Carrier :=
  weighted cosineWeight point

public theorem sin_zero : sin zero = zero := by
  unfold sin
  rw [weighted_zero]
  rfl

public theorem cos_zero : cos zero = one := by
  unfold cos
  rw [weighted_zero]
  rfl

private theorem sine_shift : sineWeight.shift.values = cosineWeight.values := by
  funext index
  change sineValues (index + 1) = cosineValues index
  have next : (index + 1) % 4 = (index % 4 + 1) % 4 := by omega
  unfold sineValues cosineValues
  rw [next]
  rcases residues index with residue | residue | residue | residue <;>
    simp only [residue] <;> rfl

private theorem cosine_shift :
    cosineWeight.shift.values = (Weight.combine (neg one) sineWeight zero sineWeight).values := by
  funext index
  change cosineValues (index + 1) =
    add (mul (neg one) (sineValues index)) (mul zero (sineValues index))
  have negated : ∀ value : selection.Carrier,
      add (mul (neg one) value) (mul zero value) = neg value := by
    intro value
    real_grind
  have next : (index + 1) % 4 = (index % 4 + 1) % 4 := by omega
  rw [negated]
  unfold sineValues cosineValues
  rw [next]
  rcases residues index with residue | residue | residue | residue <;>
    simp only [residue] <;>
    first | exact neg_zero.symm | exact (neg_neg one).symm | rfl

/-- Sine differentiates to cosine. -/
public theorem hasDerivative_sin (point : selection.Carrier) :
    HasDerivative sin point (cos point) := by
  have derivative := hasDerivative_weighted sineWeight point
  rwa [weighted_congr sine_shift] at derivative

/-- Cosine differentiates to the negated sine. -/
public theorem hasDerivative_cos (point : selection.Carrier) :
    HasDerivative cos point (neg (sin point)) := by
  have derivative := hasDerivative_weighted cosineWeight point
  rw [weighted_congr cosine_shift, weighted_combine, zero_mul, add_zero] at derivative
  have negated : mul (neg one) (sin point) = neg (sin point) := by
    rw [neg_mul, one_mul]
  rwa [← negated]

end

end Problib.Analysis
