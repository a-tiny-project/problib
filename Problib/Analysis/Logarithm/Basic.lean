module

public import Problib.Analysis.Logarithm.Interval
public import Problib.Analysis.MonotoneInverse
public import Problib.Measure.Real.Finiteness
public import Problib.Measure.Kernel.Measurable

/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot, Sébastien Gouëzel

The oriented difference argument adapts integral_interval_sub_left and
integral_add_adjacent_intervals in
Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35. Tiny projects only proved-finite
nonnegative integrals, splits at one, and uses explicit Dedekind group laws.
Multiplication then follows from the already proved positive scaling of J.
No signed integration or Mathlib import is used.
-/

set_option autoImplicit false

namespace Problib.Analysis.Logarithm

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

/-- The oriented reciprocal integral, extended by zero off the positive ray. -/
@[expose] public def logIntegral (x : Carrier) : Carrier := by
  classical
  exact if lt zero x then
    sub (ENNReal.toReal (J one x)) (ENNReal.toReal (J x one)) else zero

private theorem neg_add (x : Carrier) : add (neg x) x = zero := by rw [add_comm, add_neg]

private theorem real_add {a b : ENNReal} (ha : ENNReal.Finite a) (hb : ENNReal.Finite b) :
    ENNReal.toReal (ENNReal.add a b) = add (ENNReal.toReal a) (ENNReal.toReal b) := by
  rcases ENNReal.exists_finite_of_finite ha with ⟨a, rfl⟩
  rcases ENNReal.exists_finite_of_finite hb with ⟨b, rfl⟩
  rfl

private theorem interval_add_real (a b c : Carrier) (ha : lt zero a)
    (hab : le a b) (hbc : le b c) :
    ENNReal.toReal (J a c) = add (ENNReal.toReal (J a b)) (ENNReal.toReal (J b c)) := by
  rw [interval_add a b c hab hbc, real_add (interval_finite a b ha)
    (interval_finite b c (lt_of_lt_of_le ha hab))]

public theorem log_of_positive (x : Carrier) (hx : lt zero x) :
    logIntegral x = sub (ENNReal.toReal (J one x)) (ENNReal.toReal (J x one)) := by
  simp only [logIntegral, if_pos hx]

public theorem log_of_nonpositive (x : Carrier) (hx : le x zero) : logIntegral x = zero := by
  simp only [logIntegral, if_neg (fun h : lt zero x => h.2 hx)]

public theorem log_one : logIntegral one = zero := by
  rw [log_of_positive one one_positive, interval_self, sub_self]

private theorem log_above_one (x : Carrier) (hx : le one x) :
    logIntegral x = ENNReal.toReal (J one x) := by
  rw [log_of_positive x (lt_of_lt_of_le one_positive hx), interval_reverse x one hx,
    ENNReal.toReal_zero, sub_zero]

private theorem log_below_one (x : Carrier) (hx : lt zero x) (hx1 : le x one) :
    logIntegral x = neg (ENNReal.toReal (J x one)) := by
  rw [log_of_positive x hx, interval_reverse one x hx1, ENNReal.toReal_zero, zero_sub]

/-- The oriented integral is an additive potential on positive ordered endpoints. -/
public theorem log_difference (a b : Carrier) (ha : lt zero a) (hab : le a b) :
    logIntegral b = add (logIntegral a) (ENNReal.toReal (J a b)) := by
  rcases le_total one a with h1a | ha1
  · rw [log_above_one a h1a, log_above_one b (le_trans h1a hab)]
    exact interval_add_real one a b one_positive h1a hab
  · rcases le_total b one with hb1 | h1b
    · rw [log_below_one a ha ha1, log_below_one b (lt_of_lt_of_le ha hab) hb1,
        interval_add_real a b one ha hab hb1, Construction.Dedekind.neg_add]
      rw [add_assoc, add_comm (neg (ENNReal.toReal (J b one))), ← add_assoc,
        neg_add, zero_add]
    · rw [log_below_one a ha ha1, log_above_one b h1b,
        interval_add_real a one b ha ha1 h1b, ← add_assoc, neg_add, zero_add]

/-- Strict growth is the positivity of the intervening reciprocal integral. -/
public theorem log_strict (x y : Carrier) (hx : lt zero x) (hxy : lt x y) :
    lt (logIntegral x) (logIntegral y) := by
  rw [log_difference x y hx hxy.1]
  have hp : lt zero (ENNReal.toReal (J x y)) :=
    (ENNReal.toReal_lt_toReal_iff (show ENNReal.Finite ENNReal.zero from True.intro)
      (interval_finite x y hx)).mpr
      (interval_positive x y hx hxy)
  have shifted := (add_lt_add_left_iff (shift := logIntegral x)).mpr hp
  simpa only [add_zero] using shifted

public theorem log_monotone (x y : Carrier) (hx : lt zero x) (hxy : le x y) :
    le (logIntegral x) (logIntegral y) := by
  rw [log_difference x y hx hxy]
  have shifted := (add_le_add_left_iff (shift := logIntegral x)).mpr (ENNReal.toReal_nonnegative (J x y))
  simpa only [add_zero] using shifted

/-- Positive rescaling turns the oriented difference into the logarithm of the factor. -/
public theorem log_mul (x y : Carrier) (hx : lt zero x) (hy : lt zero y) :
    logIntegral (mul x y) = add (logIntegral x) (logIntegral y) := by
  rcases le_total one y with h1y | hy1
  · have hxy : le x (mul x y) := by
      simpa only [mul_one] using mul_le_mul_nonnegative_left h1y hx.1
    rw [log_difference x (mul x y) hx hxy, log_above_one y h1y]
    have scaled := interval_scale one y x one_positive hx
    rw [mul_one] at scaled
    rw [scaled]
  · have hxy : le (mul x y) x := by
      simpa only [mul_one] using mul_le_mul_nonnegative_left hy1 hx.1
    have eq := log_difference (mul x y) x (mul_positive hx hy) hxy
    have scaled := interval_scale y one x hy hx
    rw [mul_one] at scaled
    rw [scaled] at eq
    rw [log_below_one y hy hy1, eq, add_assoc, add_neg, add_zero]

public theorem log_inverse (x : Carrier) (hx : lt zero x) :
    logIntegral (inverse x) = neg (logIntegral x) := by
  have eq := log_mul x (inverse x) hx (inverse_of_positive_positive hx)
  rw [mul_inverse_cancel_of_positive hx, log_one] at eq
  apply add_left_cancel (left := logIntegral x)
  rw [← eq, add_neg]

private def two : Carrier := add one one
private theorem one_lt_two : lt one two := by
  have h := (add_lt_add_left_iff (shift := one)).mpr one_positive
  simpa only [add_zero, two] using h
private theorem two_positive : lt zero two := lt_trans one_positive one_lt_two

/-- Powers of two provide an explicit sequence on which logarithms diverge. -/
@[expose] public def powerTwo : Nat → Carrier
  | 0 => one
  | n + 1 => mul (powerTwo n) (add one one)

public theorem powerTwo_positive (n : Nat) : lt zero (powerTwo n) := by
  induction n with
  | zero => exact one_positive
  | succ n ih => exact mul_positive ih two_positive

public theorem log_powerTwo (n : Nat) :
    logIntegral (powerTwo n) = mul (selection.ofRat (n : Rat)) (logIntegral (add one one)) := by
  induction n with
  | zero =>
    change logIntegral one = mul (selection.ofRat 0) (logIntegral (add one one))
    rw [log_one, ofRat_zero, mul_comm]
    exact (multiplicativeSelection.ring.mul_zero _).symm
  | succ n ih =>
    rw [powerTwo, log_mul (powerTwo n) (add one one) (powerTwo_positive n) two_positive, ih,
      Rat.natCast_add, ofRat_add, show ((1 : Nat) : Rat) = 1 from rfl, ofRat_one,
      add_mul]
    rw [mul_comm one, mul_one]

public theorem log_above (r : Carrier) : ∃ x, lt zero x ∧ lt r (logIntegral x) := by
  have hp : lt zero (logIntegral (add one one)) := by
    have h := log_strict one two one_positive one_lt_two
    rw [log_one] at h
    exact h
  rcases exists_nat_strict_upper (div r (logIntegral (add one one))) with ⟨n, hn⟩
  refine ⟨powerTwo n, powerTwo_positive n, ?_⟩
  rw [log_powerTwo]
  have h := mul_lt_mul_positive_right hn hp
  rw [div_mul_cancel r (positive_iff_nonnegative_and_nonzero.mp hp).2] at h
  exact h

public theorem log_below (r : Carrier) : ∃ x, lt zero x ∧ lt (logIntegral x) r := by
  rcases log_above (neg r) with ⟨x, hx, h⟩
  refine ⟨inverse x, inverse_of_positive_positive hx, ?_⟩
  rw [log_inverse x hx]
  have reversed := neg_lt_neg_iff.mpr h
  simpa only [neg_neg] using reversed

/-- A small multiplicative increment gives the right order witness. -/
public theorem log_right (x : Carrier) (hx : lt zero x) (r : Carrier)
    (hxr : lt (logIntegral x) r) :
    ∃ y, lt x y ∧ lt (logIntegral y) r := by
  rcases exists_rational_between (lt_iff_sub_positive.mp hxr) with ⟨q, hq, hgap⟩
  let d := selection.ofRat q
  have hd : lt zero d := hq
  have h1 : lt one (add one d) := by
    simpa only [add_zero] using (add_lt_add_left_iff (shift := one)).mpr hd
  have hyp : lt zero (add one d) := lt_trans one_positive h1
  refine ⟨mul x (add one d), ?_, ?_⟩
  · simpa only [mul_one] using mul_lt_mul_positive_left h1 hx
  · have hbound : le (logIntegral (add one d)) d := by
      rw [log_above_one _ h1.1]
      have bound := (interval_bounds one (add one d) one_positive h1.1).2
      have subeq : sub (add one d) one = d := by
        rw [sub_eq_add_neg, add_comm one d, add_assoc, add_neg, add_zero]
      rw [subeq, div_one] at bound
      exact (ENNReal.le_ofReal_iff_toReal_le (interval_finite one _ one_positive) hd.1).mp bound
    rw [log_mul x _ hx hyp]
    exact lt_of_le_of_lt (add_le_add_left_iff.mpr hbound) (lt_sub_iff_add_lt.mp hgap)

/-- Reciprocal order reversal transports the right witness to the left. -/
public theorem log_left (x : Carrier) (hx : lt zero x) (r : Carrier)
    (hrx : lt r (logIntegral x)) :
    ∃ y, lt zero y ∧ lt y x ∧ lt r (logIntegral y) := by
  have hix : lt (logIntegral (inverse x)) (neg r) := by
    rw [log_inverse x hx]
    exact neg_lt_neg_iff.mpr hrx
  rcases log_right (inverse x) (inverse_of_positive_positive hx) (neg r) hix with ⟨z, hxz, hzr⟩
  have hz : lt zero z := lt_trans (inverse_of_positive_positive hx) hxz
  refine ⟨inverse z, inverse_of_positive_positive hz, ?_, ?_⟩
  · have h := inverse_lt_inverse_of_positive (inverse_of_positive_positive hx) hz hxz
    simpa only [inverse_inverse] using h
  · rw [log_inverse z hz]
    have h := neg_lt_neg_iff.mpr hzr
    simpa only [neg_neg] using h

/-- The integral logarithm supplies every hypothesis of positive-ray inversion. -/
public theorem log_order_data : Problib.Analysis.PositiveOrderData logIntegral where
  strict := fun x y hx _ hxy => log_strict x y hx hxy
  lower := log_below
  upper := log_above
  right := log_right
  left := log_left

public theorem log_surjective (r : Carrier) : ∃ x, lt zero x ∧ logIntegral x = r :=
  Problib.Analysis.surjective_of_order logIntegral log_order_data r

private theorem interval_measurable (a b : Carrier → Carrier)
    (ha : MeasurableMap borel borel a) (hb : MeasurableMap borel borel b) :
    ENNRealMeasurable borel (fun x => J (a x) (b x)) := by
  let f : Carrier × Carrier → ENNReal :=
    ennrealIndicator (fun p => Ioc (a p.1) (b p.1) p.2)
      (fun p => ENNReal.ofReal (inverse p.2))
  have hf : ENNRealMeasurable (Space.product borel borel) f := by
    apply ENNRealMeasurable.indicator
    · exact (Space.product borel borel).inter
        (measurable_lt (MeasurableMap.comp ha (Space.first_measurable borel borel))
          (Space.second_measurable borel borel))
        (measurable_le (Space.second_measurable borel borel)
          (MeasurableMap.comp hb (Space.first_measurable borel borel)))
    · exact reciprocal_measurable.comp (Space.second_measurable borel borel)
  have hm := Kernel.lintegral_measurable_joint (Kernel.const borel volume)
    (Kernel.IsSFinite.const borel volumeSFinite) (function := fun x t => f (x, t)) hf
  have eq : (fun x => lintegral volume (fun t => f (x, t))) = (fun x => J (a x) (b x)) := by
    funext x
    exact lintegral_indicator volume _ (measurable_ioc (a x) (b x)) _
  change ENNRealMeasurable borel (fun x => lintegral volume (fun t => f (x, t))) at hm
  rw [eq] at hm
  exact hm

/-- Measurability of the zero extension is piecewise. Parameter integration
makes both projected interval terms measurable, even outside the positive ray;
no global monotonicity of the extended logarithm is used. -/
public theorem log_measurable : MeasurableMap borel borel logIntegral := by
  have forward := interval_measurable (fun _ => one) (fun x => x)
    (MeasurableMap.constant borel borel one) (MeasurableMap.identity borel)
  have backward := interval_measurable (fun x => x) (fun _ => one)
    (MeasurableMap.identity borel) (MeasurableMap.constant borel borel one)
  classical
  unfold logIntegral
  intro set hs
  exact measurable_piecewise (region := fun x => lt zero x) (measurable_ioi zero)
    (measurable_sub (MeasurableMap.comp toReal_measurable forward.measurableMap)
      (MeasurableMap.comp toReal_measurable backward.measurableMap))
    (MeasurableMap.constant borel borel zero) hs

/-- The totalization cannot be globally monotone: positive inputs below one
have negative logarithms, whereas the logarithm at zero is zero. -/
public theorem log_not_globally_monotone : ¬Monotone logIntegral := by
  intro h
  rcases log_below zero with ⟨x, hx, hneg⟩
  have bound := h hx.1
  rw [log_of_nonpositive zero (le_refl zero)] at bound
  exact hneg.2 bound

/-- Positivity cannot be dropped from the multiplication law. -/
public theorem log_mul_zero_fails : ∃ y, lt zero y ∧
    logIntegral (mul zero y) ≠ add (logIntegral zero) (logIntegral y) := by
  rcases log_above zero with ⟨y, hy, hlog⟩
  refine ⟨y, hy, ?_⟩
  rw [mul_comm zero y, mul_zero,
    log_of_nonpositive zero (le_refl zero), zero_add]
  intro eq
  exact hlog.2 (eq ▸ le_refl zero)

end
end Problib.Analysis.Logarithm
