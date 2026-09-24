module

public import Problib.Analysis.Pi

/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

The positive-root identification adapts the positive branch of integral_gaussian
in Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35: nonnegative quantities with the same
square agree. Here the square comes from the pi-free quadrant identity and
reflection, and positive volume scaling supplies the parameterized formula.
No Mathlib import, complex integration, or trigonometric pi is used.
-/

set_option autoImplicit false

namespace Problib.Analysis.Gaussian

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

private theorem ofReal_two : ENNReal.ofReal (selection.ofRat 2) =
    ENNReal.add ENNReal.one ENNReal.one := by
  have h : selection.ofRat 2 = add one one := by
    calc
      selection.ofRat 2 = selection.ofRat ((1 : Rat) + 1) := congrArg selection.ofRat (Rat.natCast_add 1 1)
      _ = add one one := by rw [ofRat_add, ofRat_one]
  rw [h, ENNReal.ofReal_add one_nonnegative one_nonnegative, ENNReal.ofReal_one]

/-- The whole-line nonnegative Gaussian integral. -/
@[expose] public def G : ENNReal :=
  lintegral volume (fun x => ENNReal.ofReal (exp (neg (mul x x))))

/-- Reflection doubles the positive half-line mass; the point at zero is null. -/
public theorem whole_line :
    G = ENNReal.mul (ENNReal.ofReal (selection.ofRat 2)) gaussianHalf := by
  rw [ofReal_two]
  exact lintegral_volume_even gaussian_measurable (fun x => by
    rw [neg_mul_neg])

public theorem integral_finite : ENNReal.Finite G := by
  rw [whole_line]
  exact ENNReal.mul_finite (ENNReal.ofReal_finite _) half_finite

public theorem integral_positive : ENNReal.lt ENNReal.zero G := by
  rw [whole_line, ofReal_two, ENNReal.mul_comm, ENNReal.mul_add, ENNReal.mul_one]
  refine ⟨ENNReal.zero_le _, fun h => half_positive.2 (ENNReal.le_trans ?_ h)⟩
  simpa only [ENNReal.add_zero] using ENNReal.add_le_add_left (ENNReal.zero_le gaussianHalf) gaussianHalf

private theorem square_mul (a b : ENNReal) :
    ENNReal.mul (ENNReal.mul a b) (ENNReal.mul a b) =
      ENNReal.mul (ENNReal.mul a a) (ENNReal.mul b b) := by
  rw [ENNReal.mul_assoc, ← ENNReal.mul_assoc b a, ENNReal.mul_comm b a,
    ENNReal.mul_assoc a b b, ← ENNReal.mul_assoc]

/-- The quadrant identity evaluates the square without assuming a Gaussian value. -/
public theorem integral_square : ENNReal.mul G G = ENNReal.ofReal pi := by
  rw [whole_line, square_mul, quadrant, ← ENNReal.mul_assoc,
    ← ofReal_mul ofRat_two_positive.1 ofRat_two_positive.1,
    ← ofReal_mul (mul_nonnegative ofRat_two_positive.1 ofRat_two_positive.1)
      (inverse_of_positive_positive ofRat_two_positive).1,
    mul_assoc, mul_inverse_cancel (positive_iff_nonnegative_and_nonzero.mp ofRat_two_positive).2,
    mul_one, pi_ofReal]

/-- The finite Gaussian mass is the unique nonnegative square root of pi. -/
public theorem integral_root : G = ENNReal.finite (sqrt (NNReal.ofReal pi)) := by
  rcases ENNReal.exists_finite_of_finite integral_finite with ⟨g, hg⟩
  have sq := integral_square
  rw [hg] at sq
  have root := sqrt_unique (NNReal.ofReal pi) g (ENNReal.finite_injective sq)
  rw [hg, root]

/-- Positive scaling of volume evaluates every positive-coefficient Gaussian. -/
public theorem gaussian_integral (b : Carrier) (hb : lt zero b) :
    lintegral volume (fun x => ENNReal.ofReal (exp (neg (mul b (mul x x))))) =
      ENNReal.finite (sqrt (NNReal.ofReal (div pi b))) := by
  let r := sqrt (NNReal.ofReal b)
  have bp : NNReal.lt NNReal.zero (NNReal.ofReal b) := by
    change lt zero (NNReal.toReal (NNReal.ofReal b))
    rw [NNReal.toReal_ofReal hb.1]
    exact hb
  have rp : lt zero r.val := sqrt_positive _ bp
  have rs : mul r.val r.val = b := by
    have h := congrArg NNReal.toReal (sqrt_square (NNReal.ofReal b))
    rw [NNReal.toReal_mul, NNReal.toReal_ofReal hb.1] at h
    exact h
  have same (x : Carrier) : mul (mul r.val x) (mul r.val x) = mul b (mul x x) := by
    rw [mul_assoc, ← mul_assoc x r.val, mul_comm x r.val,
      mul_assoc r.val x x, ← mul_assoc, rs]
  have scaled := lintegral_volume_scale r.val rp gaussian_measurable
  simp only [same] at scaled
  rw [scaled, show lintegral volume (fun x => ENNReal.ofReal (exp (neg (mul x x)))) = G from rfl,
    integral_root]
  have divide : NNReal.ofReal (div pi b) = NNReal.div (NNReal.ofReal pi) (NNReal.ofReal b) := by
    apply NNReal.ext
    rw [NNReal.toReal_ofReal (div_nonnegative pi_positive.1 hb.1), NNReal.toReal_div,
      NNReal.toReal_ofReal pi_positive.1, NNReal.toReal_ofReal hb.1]
  rw [divide, sqrt_div]
  change ENNReal.finite (NNReal.mul (NNReal.ofReal (inverse r.val))
    (sqrt (NNReal.ofReal pi))) = ENNReal.finite (NNReal.div (sqrt (NNReal.ofReal pi)) r)
  apply congrArg ENNReal.finite
  apply NNReal.ext
  rw [NNReal.toReal_mul, NNReal.toReal_ofReal (inverse_of_positive_positive rp).1,
    NNReal.toReal_div, div_eq_mul_inverse, mul_comm]
  rfl

/-- At zero the formula gives zero, while the integral of the constant one
already dominates the positive Gaussian mass. -/
public theorem gaussian_integral_requires_positive :
    lintegral volume (fun x => ENNReal.ofReal (exp (neg (mul zero (mul x x))))) ≠
      ENNReal.finite (sqrt (NNReal.ofReal (div pi zero))) := by
  have zero_mul (x : Carrier) : mul zero x = zero := by
    rw [mul_comm]
    exact multiplicativeSelection.ring.mul_zero x
  have constant : (fun x : Carrier => ENNReal.ofReal (exp (neg (mul zero (mul x x))))) =
      (fun _ => ENNReal.one) := by
    funext x
    rw [zero_mul, neg_zero, exp_zero, ENNReal.ofReal_one]
  have bound : ENNReal.le G (lintegral volume (fun _ => ENNReal.one)) := by
    apply lintegral_mono
    intro x
    have sq : le zero (mul x x) := by
      rcases le_total zero x with h | h
      · exact mul_nonnegative h h
      · have hn : le zero (neg x) := by simpa only [neg_zero] using neg_le_neg_iff.mpr h
        have hsq := mul_nonnegative hn hn
        rw [neg_mul_neg] at hsq
        exact hsq
    have e := exp_monotone (neg_le_neg_iff.mpr sq)
    rw [neg_zero, exp_zero] at e
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_monotone e
  rw [constant, div_zero, NNReal.ofReal_zero, sqrt_zero]
  intro equal
  rw [equal] at bound
  exact integral_positive.2 bound

end
end Problib.Analysis.Gaussian
