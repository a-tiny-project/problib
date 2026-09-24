module

public import Problib.Analysis.Exponential.Integral

/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

The product-integral and exponential-addition steps adapt
integral_gaussian_sq_complex in Mathlib/Analysis/SpecialFunctions/Gaussian/
GaussianIntegral.lean at commit 15fe1e4eb92a37c66db923a0fa96596d7b504a35.
Here positive half-line scaling y = x*t replaces polar coordinates, and the
proved layer-cake radial integral replaces a primitive. Everything stays in
nonnegative lower integrals. No Mathlib import or pi evaluation is used.
-/

set_option autoImplicit false

namespace Problib.Analysis.Gaussian

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

/-- The Gaussian mass on the positive half line. -/
@[expose] public def gaussianHalf : ENNReal :=
  lintegral (volume.restrict (Ioi zero))
    (fun x => ENNReal.ofReal (exp (neg (mul x x))))

/-- The rational half-line integral, before any finite-real projection. -/
@[expose] public def rationalHalf : ENNReal :=
  lintegral (volume.restrict (Ioi zero))
    (fun t => ENNReal.ofReal (inverse (add one (mul t t))))

public theorem gaussian_measurable : ENNRealMeasurable borel
    (fun x => ENNReal.ofReal (exp (neg (mul x x)))) :=
  ofReal_measurable.comp (MeasurableMap.comp exp_measurable
    (MeasurableMap.comp neg_measurable
      (measurable_mul (MeasurableMap.identity borel) (MeasurableMap.identity borel))))

public theorem rational_measurable : ENNRealMeasurable borel
    (fun t => ENNReal.ofReal (inverse (add one (mul t t)))) :=
  ofReal_measurable.comp (MeasurableMap.comp Real.inverse_measurable
    (measurable_add (MeasurableMap.constant borel borel one)
      (measurable_mul (MeasurableMap.identity borel) (MeasurableMap.identity borel))))

private theorem interval_indicator (c : Carrier) (f : Carrier → ENNReal) :
    lintegral (volume.restrict (Ioi zero)) (ennrealIndicator (Iic c) f) =
      lintegral (volume.restrict (Ioc zero c)) f := by
  rw [lintegral_indicator _ _ (measurable_iic c),
    Measure.restrict_restrict volume _ (measurable_iic c)]
  have same : Set.inter (Iic c) (Ioi zero) = Ioc zero c := by
    apply Set.ext
    intro x
    exact and_comm
  rw [same]

private theorem gaussian_le_one (x : Carrier) (hx : le zero x) :
    le (exp (neg (mul x x))) one := by
  have hn := neg_le_neg_iff.mpr (mul_nonnegative hx hx)
  rw [neg_zero] at hn
  simpa only [exp_zero] using exp_monotone hn

/-- A bounded interval and the already evaluated radial tail bound the mass. -/
public theorem half_bound : ENNReal.le gaussianHalf
    (ENNReal.add ENNReal.one (ENNReal.ofReal (inverse (selection.ofRat 2)))) := by
  let g := fun x => ENNReal.ofReal (exp (neg (mul x x)))
  let w := fun x => ENNReal.mul (ENNReal.ofReal x) (g x)
  have wm : ENNRealMeasurable borel w :=
    ENNRealMeasurable.mul ofReal_measurable gaussian_measurable
  have bound := @lintegral_mono_ae _ borel (volume.restrict (Ioi zero)) g
    (fun x => ENNReal.add (ennrealIndicator (Iic one) (fun _ => ENNReal.one) x) (w x))
    ((volume.ae_restrict_mem (measurable_ioi zero)).mono (fun x hx => by
      classical
      by_cases h1 : le x one
      · simp only [ennrealIndicator, ennrealPiecewise, Iic, if_pos h1]
        have hg : ENNReal.le (g x) ENNReal.one := by
          simpa only [g, ENNReal.ofReal_one] using
            ENNReal.ofReal_monotone (gaussian_le_one x hx.1)
        apply ENNReal.le_trans hg
        simpa only [ENNReal.add_zero] using ENNReal.add_le_add_left (ENNReal.zero_le (w x)) ENNReal.one
      · simp only [ennrealIndicator, ennrealPiecewise, Iic, if_neg h1, ENNReal.zero_add]
        have hg := mul_le_mul_nonnegative_right (not_lt_iff_le.mp
          (fun h : lt x one => h1 h.1)) (exp_positive (neg (mul x x))).1
        rw [mul_comm one, mul_one] at hg
        exact ENNReal.le_trans (ENNReal.ofReal_monotone hg)
          (by rw [ofReal_mul hx.1 (exp_positive _).1]; exact ENNReal.le_refl _)))
  have wi : lintegral (volume.restrict (Ioi zero)) w = radialIntegral one := by
    apply lintegral_congr_ae
    exact (volume.ae_restrict_mem (measurable_ioi zero)).mono (fun x hx => by
      change ENNReal.mul (ENNReal.ofReal x) (ENNReal.ofReal (exp (neg (mul x x)))) =
        ENNReal.ofReal (mul x (exp (neg (mul one (mul x x)))))
      rw [one_mul, ofReal_mul hx.1 (exp_positive _).1])
  rw [lintegral_add _ (ENNRealMeasurable.indicator (measurable_iic one)
      (ENNRealMeasurable.constant _ _)) wm,
    interval_indicator, lintegral_const, Measure.restrict_apply_univ, volume_ioc,
    sub_eq_add_neg, neg_zero, add_zero, ENNReal.one_mul,
    ENNReal.ofReal_one, wi, radialIntegral_eq one NNReal.one_positive,
    mul_one] at bound
  exact bound

/-- Finiteness precedes all cancellation of the Gaussian mass. -/
public theorem half_finite : ENNReal.Finite gaussianHalf :=
  ENNReal.finite_of_le half_bound (ENNReal.add_finite trivial (ENNReal.ofReal_finite _))

/-- The Gaussian is bounded below by exp(-1) on the unit interval. -/
public theorem half_lower_bound : ENNReal.le (ENNReal.ofReal (exp (neg one))) gaussianHalf := by
  have bound := @lintegral_mono_ae _ borel (volume.restrict (Ioi zero))
    (ennrealIndicator (Iic one) (fun _ => ENNReal.ofReal (exp (neg one))))
    (fun x => ENNReal.ofReal (exp (neg (mul x x))))
    ((volume.ae_restrict_mem (measurable_ioi zero)).mono (fun x hx => by
      classical
      by_cases h1 : le x one
      · simp only [ennrealIndicator, ennrealPiecewise, Iic, if_pos h1]
        have sq : le (mul x x) one := by
          have a := mul_le_mul_nonnegative_right h1 hx.1
          rw [mul_comm one, mul_one] at a
          exact le_trans a h1
        exact ENNReal.ofReal_monotone (exp_monotone (neg_le_neg_iff.mpr sq))
      · simp only [ennrealIndicator, ennrealPiecewise, Iic, if_neg h1]
        exact ENNReal.zero_le _))
  rw [interval_indicator, lintegral_const, Measure.restrict_apply_univ, volume_ioc,
    sub_eq_add_neg, neg_zero, add_zero, ENNReal.ofReal_one,
    ENNReal.mul_one] at bound
  exact bound

public theorem half_positive : ENNReal.lt ENNReal.zero gaussianHalf := by
  refine ⟨ENNReal.zero_le _, ?_⟩
  intro h
  have z := ENNReal.le_antisymm (ENNReal.le_trans half_lower_bound h) (ENNReal.zero_le _)
  exact (exp_positive (neg one)).2 (ENNReal.ofReal_eq_zero_iff.mp z)

/-- The radial coefficient is strictly positive for every real slope. -/
public theorem coefficient_positive (t : Carrier) : lt zero (add one (mul t t)) := by
  have sq : le zero (mul t t) := by
    rcases le_total zero t with h | h
    · exact mul_nonnegative h h
    · have hn : le zero (neg t) := by
        simpa only [neg_zero] using neg_le_neg_iff.mpr h
      have hp := mul_nonnegative hn hn
      rwa [neg_mul_neg] at hp
  have h : le one (add one (mul t t)) := by
    simpa only [add_zero] using
      (add_le_add_left_iff.mpr sq : le (add one zero) (add one (mul t t)))
  exact lt_of_lt_of_le NNReal.one_positive h

/-- The x-weighted inner integral is invariant under y = x*t for x > 0. -/
public theorem scaled_gaussian_integral (x : Carrier) (hx : lt zero x) :
    lintegral (volume.restrict (Ioi zero))
      (fun t => ENNReal.ofReal (mul x (exp (neg (mul (mul x t) (mul x t)))))) =
      gaussianHalf := by
  have same : (fun t => ENNReal.ofReal (mul x (exp (neg (mul (mul x t) (mul x t)))))) =
      (fun t => ENNReal.mul (ENNReal.ofReal x)
        (ENNReal.ofReal (exp (neg (mul (mul x t) (mul x t)))))) := by
    funext t
    exact ofReal_mul hx.1 (exp_positive _).1
  rw [same, lintegral_smul _ _ (gaussian_measurable.comp (scale_measurable x hx.1)),
    lintegral_volume_restrict_scale x hx gaussian_measurable,
    ← ENNReal.mul_assoc, ofReal_mul_ofReal_inverse hx, ENNReal.one_mul]
  rfl

/-- The zero scaling factor loses the entire positive Gaussian mass. -/
public theorem scaled_gaussian_integral_requires_positive :
    lintegral (volume.restrict (Ioi zero))
      (fun t => ENNReal.ofReal (mul zero (exp (neg (mul (mul zero t) (mul zero t)))))) ≠
      gaussianHalf := by
  have same : (fun t : Carrier =>
      ENNReal.ofReal (mul zero (exp (neg (mul (mul zero t) (mul zero t)))))) =
        (fun _ => ENNReal.zero) := by
    funext t
    rw [mul_comm zero, mul_zero, ENNReal.ofReal_zero]
  rw [same, lintegral_zero]
  intro h
  exact half_positive.2 (by rw [← h]; exact ENNReal.le_refl _)

private def quadrantKernel (p : Carrier × Carrier) : ENNReal :=
  ENNReal.ofReal (mul p.1 (exp (neg (mul (add one (mul p.2 p.2)) (mul p.1 p.1)))))

private theorem kernel_measurable :
    ENNRealMeasurable (Space.product borel borel) quadrantKernel := by
  have x : MeasurableMap (Space.product borel borel) borel (fun p => p.1) :=
    Space.first_measurable borel borel
  have t : MeasurableMap (Space.product borel borel) borel (fun p => p.2) :=
    Space.second_measurable borel borel
  exact ofReal_measurable.comp (measurable_mul x
    (MeasurableMap.comp exp_measurable (MeasurableMap.comp neg_measurable
      (measurable_mul (measurable_add (MeasurableMap.constant _ _ one)
        (measurable_mul t t)) (measurable_mul x x)))))

private theorem exponent_split (x t : Carrier) :
    neg (mul (add one (mul t t)) (mul x x)) =
      add (neg (mul x x)) (neg (mul (mul x t) (mul x t))) := by
  have sq : mul (mul x t) (mul x t) = mul (mul x x) (mul t t) := by
    rw [mul_assoc, ← mul_assoc t x, mul_comm t x,
      mul_assoc x t t, ← mul_assoc]
  rw [sq, mul_comm (add one (mul t t)), mul_add, mul_one]
  exact additive.group.neg_add_distrib _ _

private theorem kernel_fiber (x : Carrier) (hx : lt zero x) :
    lintegral (volume.restrict (Ioi zero)) (fun t => quadrantKernel (x,t)) =
      ENNReal.mul (ENNReal.ofReal (exp (neg (mul x x)))) gaussianHalf := by
  have same : (fun t => quadrantKernel (x,t)) = (fun t =>
      ENNReal.mul (ENNReal.ofReal (exp (neg (mul x x))))
        (ENNReal.ofReal (mul x (exp (neg (mul (mul x t) (mul x t))))))) := by
    funext t
    unfold quadrantKernel
    rw [exponent_split, exp_add]
    rw [← ofReal_mul (exp_positive _).1 (mul_nonnegative hx.1 (exp_positive _).1)]
    rw [← mul_assoc, mul_comm x, mul_assoc]
  have hm : ENNRealMeasurable borel (fun t =>
      ENNReal.ofReal (mul x (exp (neg (mul (mul x t) (mul x t)))))) :=
    ofReal_measurable.comp (measurable_mul (MeasurableMap.constant _ _ x)
      (MeasurableMap.comp exp_measurable (MeasurableMap.comp neg_measurable
        (measurable_mul (scale_measurable x hx.1) (scale_measurable x hx.1)))))
  rw [same, lintegral_smul _ _ hm, scaled_gaussian_integral x hx]

private theorem reciprocal_product (a : Carrier) (ha : lt zero a) :
    inverse (mul (selection.ofRat 2) a) =
      mul (inverse (selection.ofRat 2)) (inverse a) := by
  have tn := (positive_iff_nonnegative_and_nonzero.mp ofRat_two_positive).2
  have an := (positive_iff_nonnegative_and_nonzero.mp ha).2
  have pn := (positive_iff_nonnegative_and_nonzero.mp (mul_positive ofRat_two_positive ha)).2
  apply mul_left_cancel_of_nonzero (factor := mul (selection.ofRat 2) a) pn
  rw [mul_inverse_cancel pn, mul_assoc, ← mul_assoc a,
    mul_comm a (inverse (selection.ofRat 2)), mul_assoc,
    mul_inverse_cancel an, mul_one, mul_inverse_cancel tn]

/-- Tonelli and positive scaling evaluate the quadrant without a value for pi. -/
public theorem quadrant :
    ENNReal.mul gaussianHalf gaussianHalf =
      ENNReal.mul (ENNReal.ofReal (inverse (selection.ofRat 2))) rationalHalf := by
  let μ := volume.restrict (Ioi zero)
  have sf := volumeSFinite.restrict (measurable_ioi zero)
  calc
    ENNReal.mul gaussianHalf gaussianHalf = lintegral μ (fun x =>
        ENNReal.mul (ENNReal.ofReal (exp (neg (mul x x)))) gaussianHalf) := by
      have hm := lintegral_smul μ gaussianHalf gaussian_measurable
      rw [show (fun x => ENNReal.mul (ENNReal.ofReal (exp (neg (mul x x)))) gaussianHalf) =
        (fun x => ENNReal.mul gaussianHalf (ENNReal.ofReal (exp (neg (mul x x)))) ) from
          funext (fun x => ENNReal.mul_comm _ _)]
      exact hm.symm
    _ = lintegral μ (fun x => lintegral μ (fun t => quadrantKernel (x,t))) := by
      apply lintegral_congr_ae
      exact (volume.ae_restrict_mem (measurable_ioi zero)).mono
        (fun x hx => (kernel_fiber x hx).symm)
    _ = lintegral (Measure.prod μ μ sf) quadrantKernel :=
      (lintegral_prod μ μ sf kernel_measurable).symm
    _ = lintegral μ (fun t => lintegral μ (fun x => quadrantKernel (x,t))) :=
      lintegral_prod_symm μ μ sf sf kernel_measurable
    _ = lintegral μ (fun t => ENNReal.ofReal (inverse (mul (selection.ofRat 2)
        (add one (mul t t))))) := by
      apply lintegral_congr
      intro t
      exact radialIntegral_eq _ (coefficient_positive t)
    _ = lintegral μ (fun t => ENNReal.mul (ENNReal.ofReal (inverse (selection.ofRat 2)))
        (ENNReal.ofReal (inverse (add one (mul t t))))) := by
      apply lintegral_congr
      intro t
      rw [reciprocal_product _ (coefficient_positive t),
        ofReal_mul (inverse_of_positive_positive ofRat_two_positive).1
          (inverse_of_positive_positive (coefficient_positive t)).1]
    _ = ENNReal.mul (ENNReal.ofReal (inverse (selection.ofRat 2))) rationalHalf :=
      lintegral_smul μ _ rational_measurable

/-- The rational mass is finite because its positive finite multiple is I². -/
public theorem rational_finite : ENNReal.Finite rationalHalf := by
  have finiteProduct := ENNReal.mul_finite half_finite half_finite
  rw [quadrant] at finiteProduct
  have hn : ENNReal.ofReal (inverse (selection.ofRat 2)) ≠ ENNReal.zero := by
    intro h
    exact (inverse_of_positive_positive ofRat_two_positive).2 (ENNReal.ofReal_eq_zero_iff.mp h)
  apply ENNReal.finite_iff_ne_top.mpr
  intro top
  rw [top, ENNReal.mul_top_of_ne_zero hn] at finiteProduct
  exact finiteProduct

public theorem rational_positive : ENNReal.lt ENNReal.zero rationalHalf := by
  refine ⟨ENNReal.zero_le _, ?_⟩
  intro h
  have hz := ENNReal.le_antisymm h (ENNReal.zero_le _)
  have q := quadrant
  rw [hz, ENNReal.mul_zero] at q
  rcases ENNReal.mul_eq_zero_iff.mp q with h | h
  · exact half_positive.2 (by rw [h]; exact ENNReal.le_refl _)
  · exact half_positive.2 (by rw [h]; exact ENNReal.le_refl _)

end
end Problib.Analysis.Gaussian
