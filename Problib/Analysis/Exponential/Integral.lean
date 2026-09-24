module

public import Problib.Analysis.Sqrt
public import Problib.Measure.Integral.LayerCake
public import Problib.Measure.Real.Moment

/-
Copyright (c) 2022 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä

The indicator-fiber and Tonelli argument adapts
lintegral_comp_eq_lintegral_meas_le_mul_of_measurable_of_sigmaFinite in
Mathlib/MeasureTheory/Integral/Layercake.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35. Here the reciprocal triangle
identifies the negative-log area after explicit null-endpoint changes.
The landed weighted layer-cake theorem and interval first moment then
compute exponential and radial integrals. No Mathlib import, derivative,
or nonlinear substitution is used.
-/

set_option autoImplicit false

namespace Problib.Analysis

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind
open Logarithm

noncomputable section

private def reciprocal (u : Carrier) : ENNReal := ENNReal.ofReal (inverse u)

private theorem reciprocal_cancel {u : Carrier} (hu : lt zero u) :
    ENNReal.mul (reciprocal u) (ENNReal.ofReal u) = ENNReal.one := by
  unfold reciprocal
  rw [ENNReal.ofReal_of_nonnegative (inverse_of_positive_positive hu).1,
    ENNReal.ofReal_of_nonnegative hu.1, ENNReal.finite_mul_finite]
  apply congrArg ENNReal.finite
  apply NNReal.ext
  change mul (inverse u) u = one
  exact inverse_mul_cancel ((positive_iff_nonnegative_and_nonzero.mp hu).2)

private def triangle : Problib.Measure.Set (Carrier × Carrier) :=
  fun p => Ioc zero one p.2 ∧ Ioc zero p.2 p.1

private def triangleKernel (p : Carrier × Carrier) : ENNReal :=
  ennrealIndicator triangle (fun z => reciprocal z.2) p

private theorem triangle_measurable : (Space.product borel borel).Measurable triangle := by
  exact (Space.product borel borel).inter
    (Space.second_measurable borel borel (measurable_ioc zero one))
    ((Space.product borel borel).inter
      (Space.first_measurable borel borel (measurable_ioi zero))
      (measurable_le (Space.first_measurable borel borel)
        (Space.second_measurable borel borel)))

private theorem triangleKernel_measurable
    (hq : ENNRealMeasurable borel reciprocal) :
    ENNRealMeasurable (Space.product borel borel) triangleKernel :=
  ENNRealMeasurable.indicator triangle_measurable
    (hq.comp (Space.second_measurable borel borel))

private theorem triangle_fiber (u : Carrier) :
    lintegral volume (fun t => triangleKernel (t,u)) =
      ennrealIndicator (Ioc zero one) (fun _ => ENNReal.one) u := by
  classical
  by_cases hu : Ioc zero one u
  · have heq : (fun t => triangleKernel (t,u)) =
        ennrealIndicator (Ioc zero u) (fun _ => reciprocal u) := by
      funext t
      simp [triangleKernel, triangle, ennrealIndicator, ennrealPiecewise, hu]
    rw [heq, lintegral_indicator volume _ (measurable_ioc zero u),
      lintegral_const, Measure.restrict_apply_univ, volume_ioc,
      sub_eq_add_neg, neg_zero, add_zero, reciprocal_cancel hu.1]
    simp [ennrealIndicator, ennrealPiecewise, hu]
  · have heq : (fun t => triangleKernel (t,u)) = (fun _ => ENNReal.zero) := by
      funext t
      simp [triangleKernel, triangle, ennrealIndicator, ennrealPiecewise, hu]
    rw [heq, lintegral_zero]
    simp [ennrealIndicator, ennrealPiecewise, hu]

-- Evaluate the reciprocal triangle before identifying its logarithmic fiber.
private theorem triangle_unit_area :
    lintegral volume (fun t => lintegral volume (fun u => triangleKernel (t,u))) =
      ENNReal.one := by
  have hm := triangleKernel_measurable reciprocal_measurable
  calc
    lintegral volume (fun t => lintegral volume (fun u => triangleKernel (t,u))) =
        lintegral (Measure.prod volume volume volumeSFinite) triangleKernel :=
      (lintegral_prod volume volume volumeSFinite hm).symm
    _ = lintegral volume (fun u => lintegral volume (fun t => triangleKernel (t,u))) :=
      lintegral_prod_symm volume volume volumeSFinite volumeSFinite hm
    _ = lintegral volume (ennrealIndicator (Ioc zero one) (fun _ => ENNReal.one)) :=
      lintegral_congr volume triangle_fiber
    _ = ENNReal.one := by
      rw [lintegral_indicator volume _ (measurable_ioc zero one),
        lintegral_const, Measure.restrict_apply_univ, volume_ioc,
        sub_eq_add_neg, neg_zero, add_zero, ENNReal.one_mul]
      exact ENNReal.ofReal_toReal_finite NNReal.one

private theorem negative_log (t : Carrier) (ht : Ioc zero one t) :
    ENNReal.ofReal (neg (logIntegral t)) = J t one := by
  rw [log_of_positive t ht.1, interval_reverse one t ht.2, ENNReal.toReal_zero,
    sub_eq_add_neg, add_comm zero, add_zero, neg_neg]
  exact ENNReal.ofReal_toReal (interval_finite t one ht.1)

/-- Removing both endpoints gives the same finite reciprocal area as minus
logarithm on the unit interval, including the degenerate t = one case. -/
public theorem negative_log_interval (t : Carrier) (ht : Ioc zero one t) :
    lintegral (volume.restrict (Ioo t one)) (fun u => ENNReal.ofReal (inverse u)) =
      ENNReal.ofReal (neg (logIntegral t)) := by
  rw [interval_open, negative_log t ht]

/-- The triangle's opposite fiber is closed at t. Its lower endpoint is null,
so intervalClosed identifies it with J; intervalOpen also removes the endpoint
at one. At t = one all three integrals are zero. -/
private theorem triangle_log_fiber (t : Carrier) :
    lintegral volume (fun u => triangleKernel (t,u)) =
      ennrealIndicator (Ioc zero one) (fun t => ENNReal.ofReal (neg (logIntegral t))) t := by
  classical
  by_cases ht : Ioc zero one t
  · have heq : (fun u => triangleKernel (t,u)) =
        ennrealIndicator (Icc t one) reciprocal := by
      funext u
      have same : triangle (t,u) ↔ Icc t one u :=
        ⟨fun h => ⟨h.2.2, h.1.2⟩,
         fun h => ⟨⟨lt_of_lt_of_le ht.1 h.1, h.2⟩, ht.1, h.1⟩⟩
      simp only [triangleKernel, ennrealIndicator, ennrealPiecewise, same]
    rw [heq, lintegral_indicator volume _ (measurable_icc t one)]
    change lintegral (volume.restrict (Icc t one)) (fun u => ENNReal.ofReal (inverse u)) = _
    rw [interval_closed, ← interval_open t one, negative_log_interval t ht]
    simp only [ennrealIndicator, ennrealPiecewise, if_pos ht]
  · have heq : (fun u => triangleKernel (t,u)) = (fun _ => ENNReal.zero) := by
      funext u
      have hn : ¬triangle (t,u) := fun h => ht ⟨h.2.1, le_trans h.2.2 h.1.2⟩
      simp only [triangleKernel, ennrealIndicator, ennrealPiecewise, if_neg hn]
    rw [heq, lintegral_zero]
    simp only [ennrealIndicator, ennrealPiecewise, if_neg ht]

/-- The negative logarithm has unit area on (0,1]. -/
public theorem negative_log_area :
    lintegral (volume.restrict (Ioc zero one))
      (fun t => ENNReal.ofReal (neg (logIntegral t))) = ENNReal.one := by
  rw [← lintegral_indicator volume _ (measurable_ioc zero one)]
  rw [← lintegral_congr volume triangle_log_fiber]
  exact triangle_unit_area

private theorem exp_neg_le_one (u : Carrier) (hu : le zero u) :
    le (exp (neg u)) one := by
  have hn : le (neg u) zero := by
    simpa only [neg_zero] using (neg_le_neg_iff.mpr hu)
  simpa only [exp_zero] using exp_monotone hn

/-- Positive exponential levels correspond to logarithmic upper bounds. -/
public theorem exp_neg_sublevel (t u : Carrier) (ht : lt zero t) :
    le t (exp (neg u)) ↔ le u (neg (logIntegral t)) := by
  have hn : le (logIntegral t) (neg u) ↔ le u (neg (logIntegral t)) := by
    rw [← neg_le_neg_iff, neg_neg]
  rw [← hn]
  constructor
  · intro h
    simpa only [log_exp] using log_monotone t (exp (neg u)) ht h
  · intro h
    simpa only [exp_log t ht] using exp_monotone h

private theorem negative_log_nonnegative (t : Carrier) (ht : Ioc zero one t) :
    le zero (neg (logIntegral t)) := by
  have h := log_monotone t one ht.1 ht.2
  rw [log_one] at h
  simpa only [neg_zero] using (neg_le_neg_iff.mpr h)

private theorem halfline_indicator (c : Carrier) (w : Carrier → ENNReal) :
    lintegral (volume.restrict (Ioi zero))
      (ennrealIndicator (fun x => le x c) w) =
      lintegral (volume.restrict (Ioc zero c)) w := by
  change lintegral (volume.restrict (Ioi zero)) (ennrealIndicator (Iic c) w) = _
  rw [lintegral_indicator _ (Iic c) (measurable_iic c),
    Measure.restrict_restrict volume _ (measurable_iic c)]
  have same : Set.inter (Iic c) (Ioi zero) = Ioc zero c := by
    apply Set.ext
    intro x
    exact and_comm
  rw [same]

/-- The cutoff has no contribution at nonpositive levels or above one. -/
private theorem empty_level (u t : Carrier) (hu : le zero u)
    (ht : ¬Ioc zero one t) : ¬Ioc zero (exp (neg u)) t := by
  intro h
  exact ht ⟨h.1, le_trans h.2 (exp_neg_le_one u hu)⟩

private theorem unit_fiber (t : Carrier) :
    lintegral (volume.restrict (Ioi zero))
      (ennrealIndicator (fun u => Ioc zero (exp (neg u)) t) (fun _ => ENNReal.one)) =
      ennrealIndicator (Ioc zero one) (fun t => ENNReal.ofReal (neg (logIntegral t))) t := by
  classical
  by_cases hp : lt zero t
  · by_cases h1 : le t one
    · have ht : Ioc zero one t := ⟨hp, h1⟩
      have same : (fun u => Ioc zero (exp (neg u)) t) =
          (fun u => le u (neg (logIntegral t))) := by
        apply Set.ext
        intro u
        exact ⟨fun h => (exp_neg_sublevel t u hp).mp h.2,
          fun h => ⟨hp, (exp_neg_sublevel t u hp).mpr h⟩⟩
      rw [same, halfline_indicator, lintegral_const, Measure.restrict_apply_univ,
        volume_ioc, sub_eq_add_neg, neg_zero, add_zero, ENNReal.one_mul]
      simp only [ennrealIndicator, ennrealPiecewise, if_pos ht]
    · have hn : ¬Ioc zero one t := fun h => h1 h.2
      have same := (volume.ae_restrict_mem (measurable_ioi zero)).mono
        (fun u hu => show ennrealIndicator (fun u => Ioc zero (exp (neg u)) t)
            (fun _ => ENNReal.one) u = ENNReal.zero from by
          simp only [ennrealIndicator, ennrealPiecewise, if_neg (empty_level u t hu.1 hn)])
      rw [lintegral_congr_ae same, lintegral_zero]
      simp only [ennrealIndicator, ennrealPiecewise, if_neg hn]
  · have same : (ennrealIndicator (fun u => Ioc zero (exp (neg u)) t)
        (fun _ => ENNReal.one)) = (fun _ => ENNReal.zero) := by
      funext u
      simp only [ennrealIndicator, ennrealPiecewise, if_neg (fun h : Ioc zero (exp (neg u)) t => hp h.1)]
    rw [same, lintegral_zero]
    simp only [ennrealIndicator, ennrealPiecewise, if_neg (fun h : Ioc zero one t => hp h.1)]

/-- The exponential of minus the identity has unit half-line integral. -/
public theorem unit_integral :
    lintegral (volume.restrict (Ioi zero))
      (fun u => ENNReal.ofReal (exp (neg u))) = ENNReal.one := by
  rw [lintegral_layer_cake_one _ (volumeSFinite.restrict (measurable_ioi zero))
    (MeasurableMap.comp exp_measurable neg_measurable)]
  rw [lintegral_congr volume unit_fiber,
    lintegral_indicator volume _ (measurable_ioc zero one)]
  exact negative_log_area

/-- Squaring on the nonnegative ray has the closed interval sublevel specified
by the already constructed square root. The zero boundary is included. -/
public theorem square_sublevel (c : Carrier) (hc : le zero c) :
    let r := (sqrt (NNReal.ofReal c)).val
    le zero r ∧ mul r r = c ∧
      ∀ x, le zero x → (le (mul x x) c ↔ le x r) := by
  let q := NNReal.ofReal c
  have hq : q.val = c := NNReal.toReal_ofReal hc
  have square : mul (sqrt q).val (sqrt q).val = c := by
    have h := congrArg NNReal.toReal (sqrt_square q)
    exact h.trans hq
  refine ⟨(sqrt q).property, square, ?_⟩
  intro x hx
  have h := square_le_iff (⟨x, hx⟩ : NNReal) (sqrt q)
  change le (mul x x) (mul (sqrt q).val (sqrt q).val) ↔ le x (sqrt q).val at h
  rw [square] at h
  exact h

/-- On the positive level interval, the radial superlevel is a closed
square-root sublevel. This includes level one, where the interval is empty
on the positive x ray. -/
public theorem radial_sublevel (a t x : Carrier) (ha : lt zero a)
    (ht : Ioc zero one t) (hx : le zero x) :
    le t (exp (neg (mul a (mul x x)))) ↔
      le x (sqrt (NNReal.ofReal (div (neg (logIntegral t)) a))).val := by
  rw [exp_neg_sublevel t _ ht.1]
  have scale := mul_le_mul_left_iff (factor := a) (left := mul x x)
    (right := div (neg (logIntegral t)) a) ha
  rw [mul_div_cancel _ (positive_iff_nonnegative_and_nonzero.mp ha).2] at scale
  rw [scale]
  exact (square_sublevel _ (div_nonnegative (negative_log_nonnegative t ht) ha.1)).2.2 x hx

private theorem radial_factor (a z : Carrier) (ha : lt zero a) :
    div (div z a) (selection.ofRat 2) =
      mul (inverse (mul (selection.ofRat 2) a)) z := by
  have an := (positive_iff_nonnegative_and_nonzero.mp ha).2
  have tn := (positive_iff_nonnegative_and_nonzero.mp ofRat_two_positive).2
  have dn := (positive_iff_nonnegative_and_nonzero.mp (mul_positive ofRat_two_positive ha)).2
  apply mul_left_cancel_of_nonzero (factor := mul (selection.ofRat 2) a) dn
  rw [mul_assoc, mul_comm a (div (div z a) (selection.ofRat 2)),
    ← mul_assoc, mul_div_cancel _ tn, div_mul_cancel _ an]
  rw [← mul_assoc, mul_inverse_cancel dn, mul_comm one z, mul_one]

private theorem radial_fiber (a t : Carrier) (ha : lt zero a) :
    lintegral (volume.restrict (Ioi zero))
      (ennrealIndicator (fun x => Ioc zero (exp (neg (mul a (mul x x)))) t) ENNReal.ofReal) =
      ennrealIndicator (Ioc zero one) (fun t =>
        ENNReal.mul (ENNReal.ofReal (inverse (mul (selection.ofRat 2) a)))
          (ENNReal.ofReal (neg (logIntegral t)))) t := by
  classical
  by_cases hp : lt zero t
  · by_cases h1 : le t one
    · have ht : Ioc zero one t := ⟨hp, h1⟩
      let r := (sqrt (NNReal.ofReal (div (neg (logIntegral t)) a))).val
      have root := square_sublevel _ (div_nonnegative (negative_log_nonnegative t ht) ha.1)
      have same := (volume.ae_restrict_mem (measurable_ioi zero)).mono
        (fun x hx => show
          ennrealIndicator (fun x => Ioc zero (exp (neg (mul a (mul x x)))) t) ENNReal.ofReal x =
            ennrealIndicator (fun x => le x r) ENNReal.ofReal x from by
          have member : Ioc zero (exp (neg (mul a (mul x x)))) t ↔ le x r :=
            ⟨fun h => (radial_sublevel a t x ha ht hx.1).mp h.2,
              fun h => ⟨hp, (radial_sublevel a t x ha ht hx.1).mpr h⟩⟩
          simp only [ennrealIndicator, ennrealPiecewise, member])
      rw [lintegral_congr_ae same, halfline_indicator, first_moment r root.1,
        root.2.1, radial_factor a _ ha,
        ofReal_mul (inverse_of_positive_positive (mul_positive ofRat_two_positive ha)).1
          (negative_log_nonnegative t ht)]
      simp only [ennrealIndicator, ennrealPiecewise, if_pos ht]
    · have hn : ¬Ioc zero one t := fun h => h1 h.2
      have same := (volume.ae_restrict_mem (measurable_ioi zero)).mono
        (fun x hx => show
          ennrealIndicator (fun x => Ioc zero (exp (neg (mul a (mul x x)))) t) ENNReal.ofReal x =
            ENNReal.zero from by
          have empty := empty_level (mul a (mul x x)) t
            (mul_nonnegative ha.1 (mul_nonnegative hx.1 hx.1)) hn
          simp only [ennrealIndicator, ennrealPiecewise, if_neg empty])
      rw [lintegral_congr_ae same, lintegral_zero]
      simp only [ennrealIndicator, ennrealPiecewise, if_neg hn]
  · have same : ennrealIndicator
        (fun x => Ioc zero (exp (neg (mul a (mul x x)))) t) ENNReal.ofReal =
          (fun _ => ENNReal.zero) := by
      funext x
      simp only [ennrealIndicator, ennrealPiecewise,
        if_neg (fun h : Ioc zero (exp (neg (mul a (mul x x)))) t => hp h.1)]
    rw [same, lintegral_zero]
    simp only [ennrealIndicator, ennrealPiecewise,
      if_neg (fun h : Ioc zero one t => hp h.1)]

/-- The weighted Gaussian radial integral on the positive half line. -/
@[expose] public def radialIntegral (a : Carrier) : ENNReal :=
  lintegral (volume.restrict (Ioi zero))
    (fun x => ENNReal.ofReal (mul x (exp (neg (mul a (mul x x))))))

/-- Weighted layer cake and the first interval moment evaluate the radial
integral without a nonlinear change of variables. -/
public theorem radialIntegral_eq (a : Carrier) (ha : lt zero a) :
    radialIntegral a = ENNReal.ofReal (inverse (mul (selection.ofRat 2) a)) := by
  have height : MeasurableMap borel borel
      (fun x => exp (neg (mul a (mul x x)))) :=
    MeasurableMap.comp exp_measurable (MeasurableMap.comp neg_measurable
      (measurable_mul (MeasurableMap.constant borel borel a)
        (measurable_mul (MeasurableMap.identity borel) (MeasurableMap.identity borel))))
  have same := (volume.ae_restrict_mem (measurable_ioi zero)).mono
    (fun x hx => ofReal_mul hx.1 (exp_positive (neg (mul a (mul x x)))).1)
  rw [radialIntegral, lintegral_congr_ae same,
    lintegral_layer_cake _ (volumeSFinite.restrict (measurable_ioi zero)) height ofReal_measurable,
    lintegral_congr volume (fun t => radial_fiber a t ha),
    lintegral_indicator volume _ (measurable_ioc zero one),
    lintegral_smul _ _ (ofReal_measurable.comp (MeasurableMap.comp neg_measurable log_measurable)),
    negative_log_area, ENNReal.mul_one]

/-- The zero coefficient cannot satisfy the positive-coefficient formula:
its radial mass is already positive on (0,1], while the proposed reciprocal
value is zero under totalized division. -/
public theorem radialIntegral_requires_positive :
    radialIntegral zero ≠ ENNReal.ofReal (inverse (mul (selection.ofRat 2) zero)) := by
  have zero_mul (x : Carrier) : mul zero x = zero := by
    rw [mul_comm]
    exact multiplicativeSelection.ring.mul_zero x
  have base : radialIntegral zero = lintegral (volume.restrict (Ioi zero)) ENNReal.ofReal := by
    apply lintegral_congr
    intro x
    rw [zero_mul, neg_zero, exp_zero, mul_one]
  have lower := lintegral_mono (volume.restrict (Ioi zero))
    (fun x => show ENNReal.le (ennrealIndicator (fun x => le x one) ENNReal.ofReal x)
        (ENNReal.ofReal x) from by
      classical
      by_cases h : le x one
      · simp only [ennrealIndicator, ennrealPiecewise, if_pos h]
        exact ENNReal.le_refl _
      · simp only [ennrealIndicator, ennrealPiecewise, if_neg h]
        exact ENNReal.zero_le _)
  rw [halfline_indicator, first_moment one NNReal.one_positive.1, mul_one] at lower
  rw [base, mul_comm (selection.ofRat 2) zero, zero_mul, inverse_zero, ENNReal.ofReal_zero]
  intro equal
  rw [equal] at lower
  have hz := ENNReal.le_antisymm lower (ENNReal.zero_le _)
  exact (div_positive NNReal.one_positive ofRat_two_positive).2 (ENNReal.ofReal_eq_zero_iff.mp hz)

end
end Problib.Analysis
