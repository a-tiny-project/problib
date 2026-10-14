module

public import Problib.Measure.Real.Finiteness
public import Problib.Measure.Real.Order
public import Problib.Measure.Kernel.Product

set_option autoImplicit false

/-
Copyright (c) 2022 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä

The indicator and Tonelli argument is adapted from
Mathlib/MeasureTheory/Integral/Layercake.lean,
lintegral_comp_eq_lintegral_meas_le_mul_of_measurable_of_sigmaFinite,
at commit 15fe1e4eb92a37c66db923a0fa96596d7b504a35.
Here the weight is on the source, the height is a Dedekind real, and interval
volume replaces the primitive. Mathlib is not imported.
-/

namespace Problib.Measure

open Problib.Real Problib.Measure.Real
open Problib.Real.Construction.Dedekind

universe u

variable {alpha : Type u} {space : Space alpha}

/-- The weighted region below a real height, with vertical fiber `(0, height x]`.
Nonpositive heights give empty fibers. The upper endpoint is included. -/
@[expose] public noncomputable def layerCake (height : alpha → Carrier)
    (weight : alpha → ENNReal) : alpha × Carrier → ENNReal :=
  ennrealIndicator (fun point => Ioc zero (height point.1) point.2)
    (fun point => weight point.1)

public theorem layerCake_measurable {height : alpha → Carrier}
    {weight : alpha → ENNReal} (heightMeasurable : MeasurableMap space borel height)
    (weightMeasurable : ENNRealMeasurable space weight) :
    ENNRealMeasurable (Space.product space borel) (layerCake height weight) := by
  apply ENNRealMeasurable.indicator
  · exact (Space.product space borel).inter
      (Space.second_measurable space borel (measurable_ioi zero))
      (measurable_le (Space.second_measurable space borel)
        (MeasurableMap.comp heightMeasurable (Space.first_measurable space borel)))
  · exact weightMeasurable.comp (Space.first_measurable space borel)

/-- A vertical fiber has its height's positive part as volume. Infinite weights
are allowed, including the convention `0 * infinity = 0` at empty fibers. -/
public theorem lintegral_layerCake_fiber (height : alpha → Carrier)
    (weight : alpha → ENNReal) (value : alpha) :
    lintegral volume (fun level => layerCake height weight (value, level)) =
      ENNReal.mul (weight value) (ENNReal.ofReal (height value)) := by
  change lintegral volume
    (ennrealIndicator (Ioc zero (height value)) (fun _ => weight value)) = _
  rw [lintegral_indicator volume _ (measurable_ioc zero (height value)),
    lintegral_const, Measure.restrict_apply_univ, volume_ioc,
    sub_eq_add_neg, neg_zero, add_zero]

/-- Weighted layer cake over an s-finite base measure. Only the base measure
needs a certificate: the proof uses the proved `volumeSFinite` for the other
Tonelli coordinate, without requiring the weighted measure to be s-finite.
Levels at or below zero contribute zero. Heights need not be nonnegative,
since `ENNReal.ofReal` takes their positive part. -/
public theorem lintegral_layer_cake (measure : Measure space)
    (measureFinite : Measure.SFinite measure) {height : alpha → Carrier}
    {weight : alpha → ENNReal} (heightMeasurable : MeasurableMap space borel height)
    (weightMeasurable : ENNRealMeasurable space weight) :
    lintegral measure (fun value =>
      ENNReal.mul (weight value) (ENNReal.ofReal (height value))) =
      lintegral volume (fun level => lintegral measure
        (ennrealIndicator (fun value => Ioc zero (height value) level) weight)) := by
  have measurable := layerCake_measurable heightMeasurable weightMeasurable
  calc
    lintegral measure (fun value =>
        ENNReal.mul (weight value) (ENNReal.ofReal (height value))) =
        lintegral measure (fun value => lintegral volume
          (fun level => layerCake height weight (value, level))) :=
      lintegral_congr measure (fun value => (lintegral_layerCake_fiber height weight value).symm)
    _ = lintegral (Measure.prod measure volume volumeSFinite) (layerCake height weight) :=
      (lintegral_prod measure volume volumeSFinite measurable).symm
    _ = lintegral volume (fun level => lintegral measure
        (fun value => layerCake height weight (value, level))) :=
      lintegral_prod_symm measure volume measureFinite volumeSFinite measurable
    _ = _ := rfl

/-- The unweighted form integrates volumes of the positive superlevel sets. -/
public theorem lintegral_layer_cake_one (measure : Measure space)
    (measureFinite : Measure.SFinite measure) {height : alpha → Carrier}
    (heightMeasurable : MeasurableMap space borel height) :
    lintegral measure (fun value => ENNReal.ofReal (height value)) =
      lintegral volume (fun level => lintegral measure
        (ennrealIndicator (fun value => Ioc zero (height value) level)
          (fun _ => ENNReal.one))) := by
  simpa only [ENNReal.one_mul] using
    lintegral_layer_cake measure measureFinite heightMeasurable
      (ENNRealMeasurable.constant space ENNReal.one)

/-- The lower cutoff at zero is load-bearing: lowering it to minus one gives
positive fiber mass even at height zero. -/
public theorem layer_cake_requires_zero_cutoff :
    lintegral volume (ennrealIndicator (Ioc (neg one) zero)
      (fun _ => ENNReal.one)) ≠ ENNReal.ofReal zero := by
  rw [lintegral_indicator volume _ (measurable_ioc _ _), lintegral_const,
    Measure.restrict_apply_univ, volume_ioc, sub_eq_add_neg, neg_neg, add_comm zero one, add_zero,
    ENNReal.one_mul, ENNReal.ofReal_zero]
  rw [show ENNReal.ofReal one = ENNReal.one from ENNReal.ofReal_toReal_finite NNReal.one]
  exact ENNReal.one_ne_zero

end Problib.Measure
