module

public import Problib.Measure.Real.Finiteness
public import Problib.Measure.Real.Uniqueness
public import Problib.Measure.Integral.Lebesgue.Transport
public import Problib.Measure.Integral.Lebesgue.Measure
public import Problib.Measure.Integral.Lebesgue.Algebra

set_option autoImplicit false

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Sébastien Gouëzel, Yury Kudryashov

The interval-uniqueness argument for positive scaling is adapted from
Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35 (smul_map_volume_mul_left and
map_volume_mul_left). Tiny uses explicit Dedekind operations, half-open
intervals, and local finiteness instead of Haar measure or ordered-field
instances. No Mathlib import is used.
-/

namespace Problib.Measure.Real

open Problib.Real
open Problib.Real.Construction

private theorem sub_translate (shift upper lower : Carrier) :
    Dedekind.sub (Dedekind.add shift upper) (Dedekind.add shift lower) =
      Dedekind.sub upper lower := by
  rw [Dedekind.sub_eq_add_neg, Dedekind.sub_eq_add_neg,
    Dedekind.add_comm shift upper, Dedekind.add_assoc,
    Dedekind.add_comm shift (Dedekind.neg (Dedekind.add shift lower))]
  rw [show Dedekind.add (Dedekind.neg (Dedekind.add shift lower)) shift =
    Dedekind.neg lower from Dedekind.additive.group.neg_add_add_left shift lower]

private theorem sub_sub_translate (shift upper lower : Carrier) :
    Dedekind.sub (Dedekind.sub upper shift) (Dedekind.sub lower shift) =
      Dedekind.sub upper lower := by
  have equal := sub_translate shift (Dedekind.sub upper shift) (Dedekind.sub lower shift)
  simpa only [Dedekind.add_sub_cancel] using equal.symm

/-- Translation is Borel measurable. -/
public theorem translate_measurable (shift : Carrier) :
    MeasurableMap borel borel (Dedekind.add shift) :=
  monotone_measurable (fun {_ _} included => Dedekind.add_le_add_left_iff.mpr included)

/-- Reflection is Borel measurable. -/
public theorem neg_measurable : MeasurableMap borel borel Dedekind.neg := by
  apply measurableMap_borel_iff_iic.mpr
  intro upper
  have equal : Set.preimage Dedekind.neg (Iic upper) = Ici (Dedekind.neg upper) := by
    apply Set.ext
    intro value
    change Dedekind.le (Dedekind.neg value) upper ↔ Dedekind.le (Dedekind.neg upper) value
    have equivalence := @Dedekind.neg_le_neg_iff (Dedekind.neg upper) value
    simpa only [Dedekind.neg_neg] using equivalence
  rw [equal]
  exact measurable_ici _

/-- Multiplication by a nonnegative constant is Borel measurable, including zero. -/
public theorem scale_measurable (factor : Carrier)
    (nonnegative : Dedekind.le Dedekind.zero factor) :
    MeasurableMap borel borel (Dedekind.mul factor) :=
  monotone_measurable (fun {_ _} included =>
    Dedekind.mul_le_mul_nonnegative_left included nonnegative)

/-- Positive affine maps are Borel measurable. -/
public theorem affine_measurable (shift factor : Carrier)
    (nonnegative : Dedekind.le Dedekind.zero factor) :
    MeasurableMap borel borel (fun value => Dedekind.add shift (Dedekind.mul factor value)) :=
  MeasurableMap.comp (translate_measurable shift) (scale_measurable factor nonnegative)

public theorem preimage_translate_ioc (shift lower upper : Carrier) :
    Set.preimage (Dedekind.add shift) (Ioc lower upper) =
      Ioc (Dedekind.sub lower shift) (Dedekind.sub upper shift) := by
  apply Set.ext
  intro value
  change (Dedekind.lt lower (Dedekind.add shift value) ∧
    Dedekind.le (Dedekind.add shift value) upper) ↔ _
  have lowerIff := @Dedekind.add_lt_add_left_iff (Dedekind.sub lower shift) value shift
  have upperIff := @Dedekind.add_le_add_left_iff value (Dedekind.sub upper shift) shift
  rw [Dedekind.add_sub_cancel] at lowerIff upperIff
  exact and_congr lowerIff upperIff

/-- Translation preserves Lebesgue volume. -/
public theorem map_volume_translate (shift : Carrier) :
    volume.map (Dedekind.add shift) (translate_measurable shift) = volume := by
  apply measure_ext_ioc
  · intro lower upper
    rw [volume_ioc]
    exact ENNReal.ofReal_finite _
  · intro lower upper
    rw [Measure.map_apply _ _ _ (measurable_ioc lower upper),
      preimage_translate_ioc, volume_ioc, volume_ioc, sub_sub_translate]

/-- Changing which endpoint of a bounded interval is included does not change its volume. -/
public theorem volume_ico (lower upper : Carrier) :
    volume (Ico lower upper) = ENNReal.ofReal (Dedekind.sub upper lower) := by
  have equal : volume (Ico lower upper) = volume (Icc lower upper) := by
    apply Measure.measure_eq_of_null_difference
    · apply volume.null_empty.mono
      intro value member
      exact member.2 ⟨member.1.1, member.1.2.1⟩
    · apply Measure.NullSet.mono
        (show volume.NullSet (Set.singleton upper) from volume_singleton upper)
      intro value member
      have notStrict : ¬Dedekind.lt value upper := fun strict =>
        member.2 ⟨member.1.1, strict⟩
      exact Dedekind.le_antisymm member.1.2 (not_lt_iff_le.mp notStrict)
  exact equal.trans (volume_icc lower upper)

public theorem preimage_neg_ioc (lower upper : Carrier) :
    Set.preimage Dedekind.neg (Ioc lower upper) =
      Ico (Dedekind.neg upper) (Dedekind.neg lower) := by
  apply Set.ext
  intro value
  change (Dedekind.lt lower (Dedekind.neg value) ∧ Dedekind.le (Dedekind.neg value) upper) ↔ _
  have lowerIff := @Dedekind.neg_lt_neg_iff value (Dedekind.neg lower)
  have upperIff := @Dedekind.neg_le_neg_iff (Dedekind.neg upper) value
  simp only [Dedekind.neg_neg] at lowerIff upperIff
  exact ⟨fun h => ⟨upperIff.mp h.2, lowerIff.mp h.1⟩,
    fun h => ⟨lowerIff.mpr h.2, upperIff.mpr h.1⟩⟩

/-- Reflection preserves Lebesgue volume. -/
public theorem map_volume_neg : volume.map Dedekind.neg neg_measurable = volume := by
  apply measure_ext_ioc
  · intro lower upper
    rw [volume_ioc]
    exact ENNReal.ofReal_finite _
  · intro lower upper
    rw [Measure.map_apply _ _ _ (measurable_ioc lower upper), preimage_neg_ioc,
      volume_ico, volume_ioc, Dedekind.sub_eq_add_neg, Dedekind.sub_eq_add_neg,
      Dedekind.neg_neg, Dedekind.add_comm]

private theorem inverse_mul_cancel (factor value : Carrier)
    (positive : Dedekind.lt Dedekind.zero factor) :
    Dedekind.mul (Dedekind.inverse factor) (Dedekind.mul factor value) = value := by
  rw [← Dedekind.mul_assoc, Dedekind.mul_comm (Dedekind.inverse factor) factor,
    Dedekind.mul_inverse_cancel_of_positive positive, Dedekind.one_mul]

private theorem mul_inverse_cancel (factor value : Carrier)
    (positive : Dedekind.lt Dedekind.zero factor) :
    Dedekind.mul factor (Dedekind.mul (Dedekind.inverse factor) value) = value := by
  rw [← Dedekind.mul_assoc, Dedekind.mul_inverse_cancel_of_positive positive, Dedekind.one_mul]

public theorem preimage_scale_ioc (factor lower upper : Carrier)
    (positive : Dedekind.lt Dedekind.zero factor) :
    Set.preimage (Dedekind.mul factor) (Ioc lower upper) =
      Ioc (Dedekind.mul (Dedekind.inverse factor) lower)
        (Dedekind.mul (Dedekind.inverse factor) upper) := by
  apply Set.ext
  intro value
  constructor
  · intro member
    have low := Dedekind.mul_lt_mul_positive_left member.1 (Dedekind.inverse_of_positive_positive positive)
    have high := Dedekind.mul_le_mul_nonnegative_left member.2
      (Dedekind.inverse_of_positive_positive positive).1
    rw [inverse_mul_cancel factor value positive] at low high
    exact ⟨low, high⟩
  · intro member
    have low := Dedekind.mul_lt_mul_positive_left member.1 positive
    have high := Dedekind.mul_le_mul_nonnegative_left member.2 positive.1
    rw [mul_inverse_cancel factor lower positive] at low
    rw [mul_inverse_cancel factor upper positive] at high
    exact ⟨low, high⟩

private theorem ofReal_mul_nonnegative (factor value : Carrier)
    (nonnegative : Dedekind.le Dedekind.zero factor) :
    ENNReal.ofReal (Dedekind.mul factor value) =
      ENNReal.mul (ENNReal.ofReal factor) (ENNReal.ofReal value) := by
  by_cases valueNonnegative : Dedekind.le Dedekind.zero value
  · rw [ENNReal.ofReal_of_nonnegative nonnegative,
      ENNReal.ofReal_of_nonnegative valueNonnegative,
      ENNReal.ofReal_of_nonnegative (Dedekind.mul_nonnegative nonnegative valueNonnegative)]
    rfl
  · have nonpositive := (not_le_iff_lt.mp valueNonnegative).1
    have productNonpositive := Dedekind.mul_le_mul_nonnegative_left nonpositive nonnegative
    rw [Dedekind.mul_zero] at productNonpositive
    rw [ENNReal.ofReal_eq_zero_iff.mpr nonpositive,
      ENNReal.ofReal_eq_zero_iff.mpr productNonpositive, ENNReal.mul_zero]

/-- A positive scaling pushes volume forward to inverse-factor times volume. -/
public theorem map_volume_scale (factor : Carrier)
    (positive : Dedekind.lt Dedekind.zero factor) :
    volume.map (Dedekind.mul factor) (scale_measurable factor positive.1) =
      Measure.smul (ENNReal.ofReal (Dedekind.inverse factor)) volume := by
  apply measure_ext_ioc
  · intro lower upper
    rw [Measure.smul_apply_measurable _ _ (measurable_ioc lower upper), volume_ioc]
    exact ENNReal.mul_finite (ENNReal.ofReal_finite _) (ENNReal.ofReal_finite _)
  · intro lower upper
    rw [Measure.map_apply _ _ _ (measurable_ioc lower upper),
      preimage_scale_ioc factor lower upper positive,
      Measure.smul_apply_measurable _ _ (measurable_ioc lower upper), volume_ioc, volume_ioc,
      ← Dedekind.mul_sub,
      ofReal_mul_nonnegative _ _ (Dedekind.inverse_of_positive_positive positive).1]

/-- Translation after positive scaling has the same inverse-factor pushforward. -/
public theorem map_volume_affine (shift factor : Carrier)
    (positive : Dedekind.lt Dedekind.zero factor) :
    volume.map (fun value => Dedekind.add shift (Dedekind.mul factor value))
      (affine_measurable shift factor positive.1) =
      Measure.smul (ENNReal.ofReal (Dedekind.inverse factor)) volume := by
  rw [← Measure.map_comp volume (Dedekind.mul factor) (Dedekind.add shift)
    (scale_measurable factor positive.1) (translate_measurable shift),
    map_volume_scale factor positive, Measure.map_smul, map_volume_translate]

public theorem preimage_scale_ioi_zero (factor : Carrier)
    (positive : Dedekind.lt Dedekind.zero factor) :
    Set.preimage (Dedekind.mul factor) (Ioi Dedekind.zero) = Ioi Dedekind.zero := by
  apply Set.ext
  intro value
  constructor
  · intro member
    have restored := Dedekind.mul_lt_mul_positive_left member
      (Dedekind.inverse_of_positive_positive positive)
    simpa only [Ioi, Dedekind.mul_zero, inverse_mul_cancel factor value positive] using restored
  · intro member
    have scaled := Dedekind.mul_lt_mul_positive_left member positive
    simpa only [Set.preimage, Ioi, Dedekind.mul_zero] using scaled

/-- Positive scaling preserves the positive half-line and rescales its volume. -/
public theorem map_volume_restrict_scale (factor : Carrier)
    (positive : Dedekind.lt Dedekind.zero factor) :
    (volume.restrict (Ioi Dedekind.zero)).map (Dedekind.mul factor)
      (scale_measurable factor positive.1) =
      Measure.smul (ENNReal.ofReal (Dedekind.inverse factor))
        (volume.restrict (Ioi Dedekind.zero)) := by
  have equal := Measure.map_restrict volume (Dedekind.mul factor)
    (scale_measurable factor positive.1) (measurable_ioi Dedekind.zero)
  rw [preimage_scale_ioi_zero factor positive, map_volume_scale factor positive,
    Measure.restrict_smul _ _ (measurable_ioi Dedekind.zero)] at equal
  exact equal

/-- Change of variables for a translated positive scaling of a nonnegative integrand. -/
public theorem lintegral_volume_affine (shift factor : Carrier)
    (positive : Dedekind.lt Dedekind.zero factor) {integrand : Carrier → ENNReal}
    (measurable : ENNRealMeasurable borel integrand) :
    lintegral volume (fun value => integrand (Dedekind.add shift (Dedekind.mul factor value))) =
      ENNReal.mul (ENNReal.ofReal (Dedekind.inverse factor)) (lintegral volume integrand) := by
  rw [← lintegral_map volume _ (affine_measurable shift factor positive.1) measurable,
    map_volume_affine shift factor positive, lintegral_smul_measure]

public theorem lintegral_volume_translate (shift : Carrier) {integrand : Carrier → ENNReal}
    (measurable : ENNRealMeasurable borel integrand) :
    lintegral volume (fun value => integrand (Dedekind.add shift value)) =
      lintegral volume integrand := by
  rw [← lintegral_map volume _ (translate_measurable shift) measurable, map_volume_translate]

public theorem lintegral_volume_neg {integrand : Carrier → ENNReal}
    (measurable : ENNRealMeasurable borel integrand) :
    lintegral volume (fun value => integrand (Dedekind.neg value)) =
      lintegral volume integrand := by
  rw [← lintegral_map volume _ neg_measurable measurable, map_volume_neg]

public theorem lintegral_volume_scale (factor : Carrier)
    (positive : Dedekind.lt Dedekind.zero factor) {integrand : Carrier → ENNReal}
    (measurable : ENNRealMeasurable borel integrand) :
    lintegral volume (fun value => integrand (Dedekind.mul factor value)) =
      ENNReal.mul (ENNReal.ofReal (Dedekind.inverse factor)) (lintegral volume integrand) := by
  rw [← lintegral_map volume _ (scale_measurable factor positive.1) measurable,
    map_volume_scale factor positive, lintegral_smul_measure]

public theorem lintegral_volume_restrict_scale (factor : Carrier)
    (positive : Dedekind.lt Dedekind.zero factor) {integrand : Carrier → ENNReal}
    (measurable : ENNRealMeasurable borel integrand) :
    lintegral (volume.restrict (Ioi Dedekind.zero))
        (fun value => integrand (Dedekind.mul factor value)) =
      ENNReal.mul (ENNReal.ofReal (Dedekind.inverse factor))
        (lintegral (volume.restrict (Ioi Dedekind.zero)) integrand) := by
  rw [← lintegral_map _ _ (scale_measurable factor positive.1) measurable,
    map_volume_restrict_scale factor positive, lintegral_smul_measure]

/-- Totalized inversion at zero cannot replace the positive-factor hypothesis. -/
public theorem zero_scale_does_not_rescale_volume :
    volume.map (Dedekind.mul Dedekind.zero)
        (scale_measurable Dedekind.zero (Dedekind.le_refl _)) ≠
      Measure.smul (ENNReal.ofReal (Dedekind.inverse Dedekind.zero)) volume := by
  intro equal
  have atUnit := congrArg (fun measure : Measure borel => measure unitSet) equal
  have preimage : Set.preimage (Dedekind.mul Dedekind.zero) unitSet = Set.univ := by
    apply Set.ext
    intro value
    have zeroProduct : Dedekind.mul Dedekind.zero value = Dedekind.zero := by
      rw [Dedekind.mul_comm, Dedekind.mul_zero]
    change (Dedekind.le Dedekind.zero (Dedekind.mul Dedekind.zero value) ∧
      Dedekind.le (Dedekind.mul Dedekind.zero value) Dedekind.one) ↔ True
    rw [zeroProduct]
    exact ⟨fun _ => True.intro, fun _ => ⟨Dedekind.le_refl _, Dedekind.one_nonnegative⟩⟩
  rw [Measure.map_apply _ _ _ (show borel.Measurable unitSet from measurable_icc _ _), preimage,
    Dedekind.inverse_zero, ENNReal.ofReal_zero, Measure.zero_smul, Measure.zero_apply] at atUnit
  have bound := volume.mono (Set.subset_univ unitSet)
  rw [volume_icc_zero_one, atUnit] at bound
  exact ENNReal.one_ne_zero (ENNReal.eq_zero_of_le_zero bound)

/-- Removing the endpoint of a lower ray does not change restricted volume. -/
public theorem volume_restrict_iic (upper : Carrier) :
    volume.restrict (Iic upper) = volume.restrict (Iio upper) := by
  apply Measure.ext
  intro set measurable
  rw [Measure.restrict_apply _ _ measurable, Measure.restrict_apply _ _ measurable]
  apply Measure.measure_eq_of_null_difference
  · apply Measure.NullSet.mono
      (show volume.NullSet (Set.singleton upper) from volume_singleton upper)
    intro value member
    have notStrict : ¬Dedekind.lt value upper := fun strict =>
      member.2 ⟨member.1.1, strict⟩
    exact Dedekind.le_antisymm member.1.2 (not_lt_iff_le.mp notStrict)
  · apply volume.null_empty.mono
    intro value member
    exact member.2 ⟨member.1.1, member.1.2.1⟩

public theorem volume_eq_add_halflines :
    volume = Measure.add (volume.restrict (Ioi Dedekind.zero))
      (volume.restrict (Iio Dedekind.zero)) := by
  have equal := volume.restrict_add_complement (measurable_ioi Dedekind.zero)
  rw [complement_ioi, volume_restrict_iic] at equal
  exact equal.symm

public theorem preimage_neg_ioi_zero :
    Set.preimage Dedekind.neg (Ioi Dedekind.zero) = Iio Dedekind.zero := by
  apply Set.ext
  intro value
  have equal := @Dedekind.neg_lt_neg_iff value Dedekind.zero
  simpa only [Set.preimage, Ioi, Iio, Dedekind.neg_zero] using equal

/-- Reflection carries negative half-line volume to positive half-line volume. -/
public theorem map_volume_restrict_neg :
    (volume.restrict (Iio Dedekind.zero)).map Dedekind.neg neg_measurable =
      volume.restrict (Ioi Dedekind.zero) := by
  have equal := Measure.map_restrict volume Dedekind.neg neg_measurable
    (measurable_ioi Dedekind.zero)
  rw [preimage_neg_ioi_zero, map_volume_neg] at equal
  exact equal

public theorem lintegral_volume_restrict_neg {integrand : Carrier → ENNReal}
    (measurable : ENNRealMeasurable borel integrand) :
    lintegral (volume.restrict (Iio Dedekind.zero))
        (fun value => integrand (Dedekind.neg value)) =
      lintegral (volume.restrict (Ioi Dedekind.zero)) integrand := by
  rw [← lintegral_map _ _ neg_measurable measurable, map_volume_restrict_neg]

/-- An even nonnegative measurable integrand has twice its positive half-line integral.
The identity also holds when the integrals are infinite. -/
public theorem lintegral_volume_even {integrand : Carrier → ENNReal}
    (measurable : ENNRealMeasurable borel integrand)
    (even : ∀ value, integrand (Dedekind.neg value) = integrand value) :
    lintegral volume integrand =
      ENNReal.mul (ENNReal.add ENNReal.one ENNReal.one)
        (lintegral (volume.restrict (Ioi Dedekind.zero)) integrand) := by
  have reflected : lintegral (volume.restrict (Iio Dedekind.zero)) integrand =
      lintegral (volume.restrict (Ioi Dedekind.zero)) integrand :=
    (lintegral_congr _ even).symm.trans (lintegral_volume_restrict_neg measurable)
  calc
    lintegral volume integrand = lintegral
        (Measure.add (volume.restrict (Ioi Dedekind.zero))
          (volume.restrict (Iio Dedekind.zero))) integrand :=
      congrArg (fun measure => lintegral measure integrand) volume_eq_add_halflines
    _ = ENNReal.add (lintegral (volume.restrict (Ioi Dedekind.zero)) integrand)
        (lintegral (volume.restrict (Iio Dedekind.zero)) integrand) :=
      lintegral_add_measure _ _ _
    _ = _ := by rw [reflected, ENNReal.mul_comm, ENNReal.mul_add, ENNReal.mul_one]

/-- Measurability alone does not make the whole-line integral twice the positive half-line integral. -/
public theorem measurability_does_not_imply_even_integral :
    ∃ integrand : Carrier → ENNReal, ENNRealMeasurable borel integrand ∧
      lintegral volume integrand ≠
        ENNReal.mul (ENNReal.add ENNReal.one ENNReal.one)
          (lintegral (volume.restrict (Ioi Dedekind.zero)) integrand) := by
  let region := Ioc (Dedekind.neg Dedekind.one) Dedekind.zero
  have measurable : borel.Measurable region := measurable_ioc _ _
  let integrand := ennrealIndicator region (fun _ => ENNReal.one)
  refine ⟨integrand, ENNRealMeasurable.indicator measurable
    (ENNRealMeasurable.constant borel ENNReal.one), ?_⟩
  have full : lintegral volume integrand = ENNReal.one := by
    rw [show integrand = ennrealIndicator region (fun _ => ENNReal.one) from rfl,
      lintegral_indicator volume region measurable, lintegral_const,
      ENNReal.one_mul, Measure.restrict_apply_univ]
    change volume (Ioc (Dedekind.neg Dedekind.one) Dedekind.zero) = ENNReal.one
    rw [volume_ioc, Dedekind.sub_eq_add_neg, Dedekind.neg_neg, Dedekind.zero_add]
    exact ENNReal.ofReal_toReal_finite NNReal.one
  have disjoint : Set.inter region (Ioi Dedekind.zero) = Set.empty := by
    apply Set.ext
    intro value
    exact ⟨fun member => member.2.2 member.1.2, False.elim⟩
  have half : lintegral (volume.restrict (Ioi Dedekind.zero)) integrand = ENNReal.zero := by
    rw [show integrand = ennrealIndicator region (fun _ => ENNReal.one) from rfl,
      lintegral_indicator _ region measurable, lintegral_const, ENNReal.one_mul,
      Measure.restrict_apply_univ, Measure.restrict_apply _ _ measurable,
      disjoint, Measure.empty_apply]
  rw [full, half, ENNReal.mul_zero]
  exact ENNReal.one_ne_zero

end Problib.Measure.Real
