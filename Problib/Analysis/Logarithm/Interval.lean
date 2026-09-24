module

public import Problib.Measure.Real.Arithmetic
public import Problib.Measure.Real.IntervalIntegral

/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot, Sébastien Gouëzel

The adjacent-interval partition argument adapts integral_add_adjacent_intervals
in Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35. Here ordered half-open intervals
partition a nonnegative lower integral, so no signed integral is introduced.
Positive scaling uses the already proved transport of volume. No Mathlib
import is used.
-/

set_option autoImplicit false

namespace Problib.Analysis.Logarithm

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

/-- The nonnegative reciprocal integral on a half-open interval. Reversed
intervals are empty; orientation belongs to the later logarithm definition. -/
@[expose] public noncomputable def J (a b : Carrier) : ENNReal :=
  lintegral (volume.restrict (Ioc a b)) (fun t => ENNReal.ofReal (inverse t))

public theorem interval_upper (a b : Carrier) (ha : lt zero a) :
    ENNReal.le (J a b)
      (ENNReal.mul (ENNReal.ofReal (inverse a)) (ENNReal.ofReal (sub b a))) := by
  have h := @lintegral_mono_ae _ borel (volume.restrict (Ioc a b))
    (fun t => ENNReal.ofReal (inverse t)) (fun _ => ENNReal.ofReal (inverse a))
    ((volume.ae_restrict_mem (measurable_ioc a b)).mono (fun t ht =>
      ENNReal.ofReal_monotone (inverse_le_inverse_of_positive ha ht.1.1)))
  rw [lintegral_const, Measure.restrict_apply_univ, volume_ioc] at h
  exact h

public theorem interval_finite (a b : Carrier) (ha : lt zero a) : ENNReal.Finite (J a b) :=
  ENNReal.finite_of_le (interval_upper a b ha)
    (ENNReal.mul_finite (ENNReal.ofReal_finite _) (ENNReal.ofReal_finite _))

public theorem interval_lower (a b : Carrier) (ha : lt zero a) :
    ENNReal.le
      (ENNReal.mul (ENNReal.ofReal (inverse b)) (ENNReal.ofReal (sub b a))) (J a b) := by
  have h := @lintegral_mono_ae _ borel (volume.restrict (Ioc a b))
    (fun _ => ENNReal.ofReal (inverse b)) (fun t => ENNReal.ofReal (inverse t))
    ((volume.ae_restrict_mem (measurable_ioc a b)).mono (fun t ht =>
      ENNReal.ofReal_monotone (inverse_le_inverse_of_positive (lt_trans ha ht.1) ht.2)))
  rw [lintegral_const, Measure.restrict_apply_univ, volume_ioc] at h
  exact h

public theorem reciprocal_measurable :
    ENNRealMeasurable borel (fun t => ENNReal.ofReal (inverse t)) :=
  ofReal_measurable.comp Real.inverse_measurable

/-- Reciprocal rectangles bound the integral for ordered positive endpoints. -/
public theorem interval_bounds (a b : Carrier) (ha : lt zero a) (hab : le a b) :
    ENNReal.le (ENNReal.ofReal (div (sub b a) b)) (J a b) ∧
      ENNReal.le (J a b) (ENNReal.ofReal (div (sub b a) a)) := by
  have hb : lt zero b := ⟨le_trans ha.1 hab, fun h => ha.2 (le_trans hab h)⟩
  have hd : le zero (sub b a) := additive.orderedGroup.sub_nonnegative_of_le hab
  constructor
  · simpa only [div_eq_mul_inverse, ofReal_mul hd (inverse_of_positive_positive hb).1,
      ENNReal.mul_comm] using interval_lower a b ha
  · simpa only [div_eq_mul_inverse, ofReal_mul hd (inverse_of_positive_positive ha).1,
      ENNReal.mul_comm] using interval_upper a b ha

/-- Reversed endpoints give the empty integral. -/
public theorem interval_reverse (a b : Carrier) (hba : le b a) : J a b = ENNReal.zero := by
  have empty : Ioc a b = Set.empty := by
    apply Set.ext
    intro t
    exact ⟨fun h => h.1.2 (le_trans h.2 hba), False.elim⟩
  rw [J, empty, Measure.restrict_empty, lintegral_zero_measure]

public theorem interval_self (a : Carrier) : J a a = ENNReal.zero :=
  interval_reverse a a (le_refl a)

/-- Concatenation needs ordered endpoints, but not positivity or finiteness. -/
public theorem interval_add (a b c : Carrier) (hab : le a b) (hbc : le b c) :
    J a c = ENNReal.add (J a b) (J b c) := by
  classical
  let q := fun t => ENNReal.ofReal (inverse t)
  have split : ∀ t, ennrealIndicator (Ioc a c) q t =
      ENNReal.add (ennrealIndicator (Ioc a b) q t) (ennrealIndicator (Ioc b c) q t) := by
    intro t
    by_cases ht : Ioc a c t
    · by_cases htb : le t b
      · have first : Ioc a b t := ⟨ht.1, htb⟩
        have second : ¬Ioc b c t := fun h => h.1.2 htb
        simp only [ennrealIndicator, ennrealPiecewise, if_pos ht, if_pos first,
          if_neg second, ENNReal.add_zero]
      · have first : ¬Ioc a b t := fun h => htb h.2
        have second : Ioc b c t := ⟨not_le_iff_lt.mp htb, ht.2⟩
        simp only [ennrealIndicator, ennrealPiecewise, if_pos ht, if_neg first,
          if_pos second, ENNReal.zero_add]
    · have first : ¬Ioc a b t := fun h => ht ⟨h.1, le_trans h.2 hbc⟩
      have second : ¬Ioc b c t := by
        intro h
        exact ht ⟨⟨le_trans hab h.1.1, fun reverse => h.1.2 (le_trans reverse hab)⟩, h.2⟩
      simp only [ennrealIndicator, ennrealPiecewise, if_neg ht, if_neg first,
        if_neg second, ENNReal.zero_add]
  calc
    J a c = lintegral volume (ennrealIndicator (Ioc a c) q) :=
      (lintegral_indicator volume _ (measurable_ioc a c) q).symm
    _ = lintegral volume (fun t => ENNReal.add
        (ennrealIndicator (Ioc a b) q t) (ennrealIndicator (Ioc b c) q t)) :=
      lintegral_congr volume split
    _ = ENNReal.add (J a b) (J b c) := by
      rw [lintegral_add volume
        (ENNRealMeasurable.indicator (measurable_ioc a b) reciprocal_measurable)
        (ENNRealMeasurable.indicator (measurable_ioc b c) reciprocal_measurable),
        lintegral_indicator volume _ (measurable_ioc a b),
        lintegral_indicator volume _ (measurable_ioc b c)]
      rfl

/-- Removing the upper endpoint preserves the reciprocal integral. -/
public theorem interval_open (a b : Carrier) :
    lintegral (volume.restrict (Ioo a b)) (fun t => ENNReal.ofReal (inverse t)) = J a b :=
  lintegral_restrict_ioo a b _

/-- Adding the lower endpoint preserves the reciprocal integral, including
coincident or reversed endpoints. This identifies the logarithmic triangle's
closed opposite fiber with the half-open interval used by J. -/
public theorem interval_closed (a b : Carrier) :
    lintegral (volume.restrict (Icc a b)) (fun t => ENNReal.ofReal (inverse t)) = J a b := by
  have same : volume.AEEq (Icc a b) (Ioc a b) := by
    apply Measure.NullSet.mono (show volume.NullSet (Set.singleton a) from volume_singleton a)
    intro t differs
    change t = a
    apply Classical.byContradiction
    intro unequal
    apply differs
    apply propext
    constructor
    · intro h
      exact ⟨⟨h.1, fun reverse => unequal (le_antisymm reverse h.1)⟩, h.2⟩
    · intro h
      exact ⟨h.1.1, h.2⟩
  rw [Measure.restrict_congr_ae same]
  rfl

private theorem inverse_mul {x y : Carrier} (hx : lt zero x) (hy : lt zero y) :
    inverse (mul x y) = mul (inverse x) (inverse y) := by
  have xn := (positive_iff_nonnegative_and_nonzero.mp hx).2
  have yn := (positive_iff_nonnegative_and_nonzero.mp hy).2
  have xyn := (positive_iff_nonnegative_and_nonzero.mp (mul_positive hx hy)).2
  apply mul_right_cancel_of_nonzero (factor := mul x y) xyn
  rw [inverse_mul_cancel xyn]
  symm
  calc
    mul (mul (inverse x) (inverse y)) (mul x y) =
        mul (inverse x) (mul (inverse y) (mul x y)) := mul_assoc _ _ _
    _ = mul (inverse x) (mul x (mul (inverse y) y)) := by
      rw [← mul_assoc (inverse y) x y, mul_comm (inverse y) x, mul_assoc x (inverse y) y]
    _ = one := by rw [inverse_mul_cancel yn, mul_one, inverse_mul_cancel xn]

private def integrand (a b : Carrier) : Carrier → ENNReal :=
  ennrealIndicator (Ioc a b) (fun t => ENNReal.ofReal (inverse t))
private theorem scale_integrand (a b c t : Carrier) (ha : lt zero a) (hc : lt zero c) :
    integrand (mul c a) (mul c b) (mul c t) =
      ENNReal.mul (ENNReal.ofReal (inverse c)) (integrand a b t) := by
  classical
  have member : Ioc (mul c a) (mul c b) (mul c t) ↔ Ioc a b t :=
    and_congr (mul_lt_mul_left_iff hc) (mul_le_mul_left_iff hc)
  by_cases ht : Ioc a b t
  · have tp := lt_trans ha ht.1
    simp only [integrand, ennrealIndicator, ennrealPiecewise,
      if_pos ht, if_pos (member.mpr ht)]
    rw [inverse_mul hc tp]
    exact ofReal_mul (inverse_of_positive_positive hc).1 (inverse_of_positive_positive tp).1
  · have hscaled : ¬Ioc (mul c a) (mul c b) (mul c t) := fun h => ht (member.mp h)
    simp only [integrand, ennrealIndicator, ennrealPiecewise,
      if_neg ht, if_neg hscaled, ENNReal.mul_zero]

/-- Positive scaling leaves the reciprocal interval integral unchanged. -/
public theorem interval_scale
    (a b c : Carrier) (ha : lt zero a) (hc : lt zero c) :
    J (mul c a) (mul c b) = J a b := by
  have hm : ∀ a b, ENNRealMeasurable borel (integrand a b) :=
    fun a b => ENNRealMeasurable.indicator (measurable_ioc a b) reciprocal_measurable
  have factorPositive : ENNReal.lt ENNReal.zero (ENNReal.ofReal (inverse c)) := by
    rw [← ENNReal.ofReal_zero]
    exact (ENNReal.ofReal_lt_ofReal_iff (le_refl zero) (inverse_of_positive_positive hc).1).mpr
      (inverse_of_positive_positive hc)
  have integral_eq : ∀ a b, lintegral volume (integrand a b) = J a b := by
    intro a b
    exact lintegral_indicator volume _ (measurable_ioc a b) _
  have equal : ENNReal.mul (ENNReal.ofReal (inverse c)) (J (mul c a) (mul c b)) =
      ENNReal.mul (ENNReal.ofReal (inverse c)) (J a b) := by
    calc
      ENNReal.mul (ENNReal.ofReal (inverse c)) (J (mul c a) (mul c b)) =
          lintegral volume (fun x => integrand (mul c a) (mul c b) (mul c x)) := by
        rw [lintegral_volume_scale c hc (hm _ _), integral_eq]
      _ = lintegral volume (fun x => ENNReal.mul (ENNReal.ofReal (inverse c)) (integrand a b x)) :=
        lintegral_congr volume (fun x => scale_integrand a b c x ha hc)
      _ = ENNReal.mul (ENNReal.ofReal (inverse c)) (J a b) := by
        rw [lintegral_smul volume _ (hm a b), integral_eq]
  apply ENNReal.le_antisymm
  · apply (ENNReal.mul_le_mul_left_iff (ENNReal.ofReal_finite _) factorPositive).mp
    rw [equal]
    exact ENNReal.le_refl _
  · apply (ENNReal.mul_le_mul_left_iff (ENNReal.ofReal_finite _) factorPositive).mp
    rw [equal]
    exact ENNReal.le_refl _

/-- Every nonempty interval with positive lower endpoint has positive integral. -/
public theorem interval_positive (a b : Carrier) (ha : lt zero a) (hab : lt a b) :
    ENNReal.lt ENNReal.zero (J a b) := by
  have hd : lt zero (sub b a) := by
    have shifted := (add_lt_add_right_iff (shift := neg a)).mpr hab
    simpa only [add_neg, sub_eq_add_neg] using shifted
  have hp := div_positive hd (lt_trans ha hab)
  have lowerPositive : ENNReal.lt ENNReal.zero (ENNReal.ofReal (div (sub b a) b)) := by
    rw [← ENNReal.ofReal_zero]
    exact (ENNReal.ofReal_lt_ofReal_iff (le_refl zero) hp.1).mpr hp
  have lower := (interval_bounds a b ha hab.1).1
  exact ⟨ENNReal.le_trans lowerPositive.1 lower,
    fun reverse => lowerPositive.2 (ENNReal.le_trans lower reverse)⟩

/-- Scaling by zero collapses a positive interval and cannot preserve J. -/
public theorem zero_scale_fails (a b : Carrier) (ha : lt zero a) (hab : lt a b) :
    J (mul zero a) (mul zero b) ≠ J a b := by
  have za : mul zero a = zero := by
    rw [mul_comm]
    exact multiplicativeSelection.ring.mul_zero _
  have zb : mul zero b = zero := by
    rw [mul_comm]
    exact multiplicativeSelection.ring.mul_zero _
  rw [za, zb, interval_self]
  intro equal
  exact (interval_positive a b ha hab).2 (equal ▸ ENNReal.le_refl _)

/-- An out-of-order middle endpoint cannot satisfy unrestricted concatenation. -/
public theorem unordered_add_fails (a b : Carrier) (ha : lt zero a) (hab : lt a b) :
    J a a ≠ ENNReal.add (J a b) (J b a) := by
  rw [interval_self, interval_reverse b a hab.1, ENNReal.add_zero]
  intro equal
  exact (interval_positive a b ha hab).2 (equal ▸ ENNReal.le_refl _)

end

end Problib.Analysis.Logarithm
