module

public import Problib.Measure.Real.Arithmetic
public import Problib.Measure.Real.IntervalIntegral

/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot, Sébastien Gouëzel

The reflection substitution follows integral_comp_sub_left in
Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35. Tiny uses the composition of
translation and negation on volume, an invariant open interval, and null
endpoints. The first moment then follows by adding the reflected integrand
and cancelling only after proving finiteness. No Mathlib import is used.
-/

set_option autoImplicit false

namespace Problib.Measure.Real

open Problib.Real
open Problib.Real.Construction.Dedekind

/-- The identity integrand is bounded by the endpoint on its interval. -/
public theorem first_moment_bound (c : Carrier) :
    ENNReal.le (lintegral (volume.restrict (Ioc zero c)) ENNReal.ofReal)
      (ENNReal.mul (ENNReal.ofReal c) (ENNReal.ofReal c)) := by
  have bound := @lintegral_mono_ae _ borel (volume.restrict (Ioc zero c))
    ENNReal.ofReal (fun _ => ENNReal.ofReal c)
    ((volume.ae_restrict_mem (measurable_ioc zero c)).mono
      (fun _ member => ENNReal.ofReal_monotone member.2))
  rw [lintegral_const, Measure.restrict_apply_univ, volume_ioc,
    sub_eq_add_neg, neg_zero, add_zero] at bound
  exact bound

/-- Finiteness is established before any cancellation or projection. -/
public theorem first_moment_finite (c : Carrier) :
    ENNReal.Finite (lintegral (volume.restrict (Ioc zero c)) ENNReal.ofReal) :=
  ENNReal.finite_of_le (first_moment_bound c)
    (ENNReal.mul_finite (ENNReal.ofReal_finite c) (ENNReal.ofReal_finite c))

private theorem reflection_preimage (c : Carrier) :
    Set.preimage (sub c) (Ioo zero c) = Ioo zero c := by
  apply Set.ext
  intro x
  change (lt zero (sub c x) ∧ lt (sub c x) c) ↔ (lt zero x ∧ lt x c)
  rw [← lt_iff_sub_positive (left := x) (right := c),
    lt_iff_sub_positive (left := sub c x) (right := c), sub_sub_cancel]
  exact and_comm

/-- Reflection around the midpoint preserves the interval lower integral.
The endpoint change is justified by singleton nullity, including empty intervals. -/
public theorem lintegral_interval_reflection (c : Carrier) {f : Carrier → ENNReal}
    (measurable : ENNRealMeasurable borel f) :
    lintegral (volume.restrict (Ioc zero c)) (fun x => f (sub c x)) =
      lintegral (volume.restrict (Ioc zero c)) f := by
  have reflectionMeasurable : MeasurableMap borel borel (sub c) :=
    MeasurableMap.comp (translate_measurable c) neg_measurable
  have invariant : volume.map (sub c) reflectionMeasurable = volume := by
    change volume.map (fun x => add c (neg x))
      (MeasurableMap.comp (translate_measurable c) neg_measurable) = volume
    rw [← Measure.map_comp volume neg (add c) neg_measurable (translate_measurable c),
      map_volume_neg, map_volume_translate]
  have restricted := Measure.map_restrict volume (sub c) reflectionMeasurable
    (measurable_ioo zero c)
  rw [reflection_preimage, invariant] at restricted
  rw [← restrict_volume_ioo zero c, ← lintegral_map _ _ reflectionMeasurable measurable,
    restricted]

private theorem two_eq : selection.ofRat 2 = add one one := by
  rw [show (2 : Rat) = 1 + 1 from Rat.natCast_add 1 1, ofRat_add, ofRat_one]

/-- The lower integral of x on (0,c] is c²/2 for a nonnegative endpoint. -/
public theorem first_moment (c : Carrier) (nonnegative : le zero c) :
    lintegral (volume.restrict (Ioc zero c)) ENNReal.ofReal =
      ENNReal.ofReal (div (mul c c) (selection.ofRat 2)) := by
  have finiteIntegral := first_moment_finite c
  have reflected := lintegral_interval_reflection c ofReal_measurable
  have sum := lintegral_add (volume.restrict (Ioc zero c))
    (right := fun x => ENNReal.ofReal (sub c x)) ofReal_measurable
    (ofReal_measurable.comp (MeasurableMap.comp (translate_measurable c) neg_measurable))
  have constant := lintegral_restrict_ioc_congr zero c
    (fun x => ENNReal.add (ENNReal.ofReal x) (ENNReal.ofReal (sub c x)))
    (fun _ => ENNReal.ofReal c) (fun x member => by
      rw [← ENNReal.ofReal_add member.1.1
        (show le zero (sub c x) from
          additive.orderedGroup.sub_nonnegative_of_le member.2), add_sub_cancel])
  rw [reflected] at sum
  rw [constant, lintegral_const, Measure.restrict_apply_univ, volume_ioc,
    sub_eq_add_neg, neg_zero, add_zero,
    ← ofReal_mul nonnegative nonnegative] at sum
  rcases ENNReal.exists_finite_of_finite finiteIntegral with ⟨value, valueEq⟩
  rw [valueEq] at sum ⊢
  have doubled : add value.val value.val = mul c c := by
    have projected := congrArg ENNReal.toReal sum.symm
    rw [ENNReal.toReal_ofReal (mul_nonnegative nonnegative nonnegative)] at projected
    exact projected
  have valueFormula : value.val = div (mul c c) (selection.ofRat 2) := by
    apply mul_right_cancel_of_nonzero (factor := selection.ofRat 2)
      (fun equal => ofRat_two_positive.2 (by rw [equal]; exact le_refl zero))
    rw [div_mul_cancel _ (fun equal => ofRat_two_positive.2 (by rw [equal]; exact le_refl zero)),
      two_eq, mul_add, mul_one, doubled]
  rw [← valueFormula]
  exact (ENNReal.ofReal_toReal_finite value).symm

/-- Negative endpoints refute the first-moment formula without nonnegativity. -/
public theorem first_moment_requires_nonnegative :
    lintegral (volume.restrict (Ioc zero (neg one))) ENNReal.ofReal ≠
      ENNReal.ofReal (div (mul (neg one) (neg one)) (selection.ofRat 2)) := by
  have nonpositive : le (neg one) zero := by
    simpa only [neg_zero] using (neg_le_neg_iff.mpr one_nonnegative)
  rw [ioc_empty_of_le nonpositive, Measure.restrict_empty, lintegral_zero_measure]
  have square : mul (neg one) (neg one) = one := by
    calc
      mul (neg one) (neg one) = mul one one :=
        multiplicativeSelection.ring.neg_mul_neg one one
      _ = one := mul_one one
  rw [square]
  have onePositive : lt zero one := by
    rw [← ofRat_zero, ← ofRat_one]
    exact (ofRat_lt_iff 0 1).mpr (by decide)
  intro equal
  exact (div_positive onePositive ofRat_two_positive).2 (ENNReal.ofReal_eq_zero_iff.mp equal.symm)

end Problib.Measure.Real
