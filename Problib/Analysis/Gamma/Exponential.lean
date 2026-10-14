module

public import Problib.Analysis.Gamma.Density
public import Problib.Analysis.Exponential.Tail
public import Problib.Measure.Real.Uniqueness
public import Problib.Measure.Uniform

/-! The exponential law: the Gamma law at shape one.

At shape one the Gamma density is `rate e^(-rate x)` on the positive half line
(`density_one`). From a positive threshold `t` its upper tail is `e^(-rate t)`
(`law_one_ici`), so the law puts `1 - e^(-rate t)` below `t` (`law_one_iio`)
and nothing below a nonpositive threshold (`law_one_iio_nonpositive`).

`exponentialQuantile rate u` is `-log(1 - u) / rate`, the inverse of that
distribution function, read through Problib's logarithm, which is zero at zero.
Pushing the uniform law forward through it gives the law
(`uniform01_map_exponentialQuantile`). The quantile takes the logarithm of
`1 - u`, which is zero only at `u = 1`, a point of uniform mass zero, so a
sampler whose uniform excludes 1 never takes the logarithm of zero.
-/

set_option autoImplicit false

namespace Problib.Analysis.Gamma

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind
open Problib.Analysis.Logarithm

noncomputable section

/-! ### The law at shape one -/

/-- At shape one the density is the rate times the decaying exponential. -/
public theorem density_one {rate : Carrier} (nonnegative : le zero rate) {value : Carrier}
    (positive : lt zero value) :
    ENNReal.finite (density one rate value) =
      ENNReal.mul (ENNReal.ofReal rate) (Exponential.weight rate value) := by
  rw [density_product one rate positive, rpow_one nonnegative, gamma_one, div_one]
  unfold weight
  rw [sub_self, rpow_zero, ENNReal.ofReal_one, ENNReal.one_mul]

/-- The same density read as a real number. -/
public theorem density_one_toReal {rate : Carrier} (nonnegative : le zero rate) {value : Carrier}
    (positive : lt zero value) :
    (density one rate value).toReal = mul rate (exp (neg (mul rate value))) := by
  rw [density_of_positive one rate positive, rpow_one nonnegative, gamma_one, div_one, sub_self,
    rpow_zero, one_mul, NNReal.toReal_ofReal (mul_nonnegative nonnegative (exp_positive _).1)]

/-- From a positive threshold the upper tail is `e^(-rate t)`. -/
public theorem law_one_ici {rate : Carrier} (ratePositive : lt zero rate) {threshold : Carrier}
    (positive : lt zero threshold) :
    law one rate (Ici threshold) = Exponential.weight rate threshold := by
  rw [law_apply one_positive ratePositive (measurable_ici threshold)]
  have pointwise : (volume.restrict (Ici threshold)).AEEq
      (fun value => ENNReal.finite (density one rate value))
      (fun value => ENNReal.mul (ENNReal.ofReal rate) (Exponential.weight rate value)) :=
    (volume.ae_restrict_mem (measurable_ici threshold)).mono fun _ above =>
      density_one ratePositive.1 (lt_of_lt_of_le positive above)
  rw [lintegral_congr_ae pointwise, lintegral_smul _ _ (Exponential.weight_measurable rate),
    Exponential.tail_closed rate threshold ratePositive, ENNReal.mul_comm, ENNReal.mul_assoc,
    ENNReal.mul_comm (ENNReal.ofReal (inverse rate)), ofReal_mul_ofReal_inverse ratePositive,
    ENNReal.mul_one]

/-- The law holds `1 - e^(-rate t)` below a positive threshold `t`. -/
public theorem law_one_iio {rate : Carrier} (ratePositive : lt zero rate) {threshold : Carrier}
    (positive : lt zero threshold) :
    law one rate (Iio threshold) =
      ENNReal.ofReal (sub one (exp (neg (mul rate threshold)))) := by
  have cover : Set.union (Iio threshold) (Ici threshold) = Set.univ :=
    Set.ext fun value => ⟨fun _ => trivial, fun _ =>
      (Classical.em (lt value threshold)).elim Or.inl fun above => Or.inr (not_lt_iff_le.mp above)⟩
  have split := Measure.union_disjoint (law one rate) (measurable_iio threshold) (measurable_ici threshold)
    fun _ below above => below.2 above
  rw [cover, (law_isProbability one rate).univ_eq_one, law_one_ici ratePositive positive] at split
  have decayed : le (exp (neg (mul rate threshold))) one := by
    rw [← exp_zero]
    apply exp_monotone
    rw [← neg_zero]
    exact neg_le_neg_iff.mpr (mul_positive ratePositive positive).1
  apply ENNReal.add_right_cancel_of_finite (ENNReal.ofReal_finite (exp (neg (mul rate threshold))))
  unfold Exponential.weight at split
  rw [← split, ← ENNReal.ofReal_add (sub_nonnegative decayed) (exp_positive _).1, sub_add_cancel,
    ENNReal.ofReal_one]

/-- The law holds nothing below a nonpositive threshold. -/
public theorem law_one_iio_nonpositive {rate : Carrier} (ratePositive : lt zero rate)
    {threshold : Carrier} (nonpositive : le threshold zero) :
    law one rate (Iio threshold) = ENNReal.zero := by
  rw [law_apply one_positive ratePositive (measurable_iio threshold)]
  have pointwise : (volume.restrict (Iio threshold)).AEEq
      (fun value => ENNReal.finite (density one rate value)) (fun _ => ENNReal.zero) :=
    (volume.ae_restrict_mem (measurable_iio threshold)).mono fun _ below => by
      show ENNReal.finite (density one rate _) = ENNReal.finite NNReal.zero
      rw [density_of_nonpositive one rate (le_trans below.1 nonpositive)]
  rw [lintegral_congr_ae pointwise, lintegral_zero]

/-! ### The quantile -/

/-- The exponential quantile `-log(1 - u) / rate`. At `u = 1` Problib's
logarithm of zero is zero, so the quantile is zero there. -/
@[expose] public def exponentialQuantile (rate : Carrier) (point : UnitInterval) : Carrier :=
  div (neg (logIntegral (sub one point.val))) rate

public theorem exponentialQuantile_measurable (rate : Carrier) :
    MeasurableMap unitBorel borel (exponentialQuantile rate) :=
  measurable_div (MeasurableMap.comp neg_measurable (MeasurableMap.comp log_measurable
      (measurable_sub (MeasurableMap.constant _ borel one) unitInclusion_measurable)))
    (MeasurableMap.constant _ borel rate)

/-- The quantile lies below `t` exactly when the logarithm exceeds `-rate t`. -/
private theorem quantile_lt_iff {rate : Carrier} (ratePositive : lt zero rate)
    (point : UnitInterval) (threshold : Carrier) :
    lt (exponentialQuantile rate point) threshold ↔
      lt (neg (mul rate threshold)) (logIntegral (sub one point.val)) := by
  have scaled := mul_lt_mul_left_iff (left := exponentialQuantile rate point)
    (right := threshold) ratePositive
  unfold exponentialQuantile at scaled ⊢
  rw [mul_div_cancel _ (nonzero_of_positive ratePositive)] at scaled
  rw [← scaled, ← neg_lt_neg_iff, neg_neg]

/-- Moving the point across the threshold's difference from one. -/
private theorem below_complement (point value : Carrier) :
    lt point (sub one value) ↔ lt value (sub one point) := by
  rw [← sub_positive_iff, ← sub_positive_iff (left := value)]
  have swap : sub (sub one value) point = sub (sub one point) value := by
    rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, add_assoc,
      add_comm (neg value), ← add_assoc]
  rw [swap]

/-- The difference from one of a point of the unit interval is at most one. -/
private theorem complement_le_one (point : UnitInterval) : le (sub one point.val) one := by
  have shifted := add_le_add (le_refl one) (neg_nonpositive_iff.mp point.property.1)
  rwa [add_zero, ← sub_eq_add_neg] at shifted

/-- A point whose difference from one is not positive is one. -/
private theorem eq_one_of_complement (point : UnitInterval)
    (nonpositive : ¬lt zero (sub one point.val)) : point.val = one :=
  le_antisymm point.property.2
    (not_lt_iff_le.mp fun below => nonpositive (sub_positive_iff.mpr below))

/-- The uniform mass the quantile sends below `t` is `1 - e^(-rate t)`, read as
zero when it is negative.
The preimage differs from the initial interval below `1 - e^(-rate t)` only at
the point one. -/
private theorem uniform01_quantile_iio {rate : Carrier} (ratePositive : lt zero rate)
    (threshold : Carrier) :
    uniform01 (Set.preimage (exponentialQuantile rate) (Iio threshold)) =
      ENNReal.ofReal (sub one (exp (neg (mul rate threshold)))) := by
  have atMostOne : le (sub one (exp (neg (mul rate threshold)))) one :=
    le_of_lt (sub_positive_iff.mp (by rw [sub_sub_cancel]; exact exp_positive _))
  refine (Measure.measure_eq_of_null_difference ?_ ?_).trans
    (uniform01_real_initial _ atMostOne)
  · -- A preimage point off the initial interval is the point one.
    apply Measure.NullSet.mono (show uniform01.NullSet
      (Set.singleton (⟨one, one_positive.1, le_refl one⟩ : UnitInterval)) from uniform01_singleton _)
    intro point member
    apply Subtype.ext
    refine Classical.byContradiction fun different => member.2 ?_
    have inside : lt zero (sub one point.val) := Classical.byContradiction fun nonpositive =>
      different (eq_one_of_complement point nonpositive)
    have logged := (quantile_lt_iff ratePositive point threshold).mp member.1
    have raised := exp_strict logged
    rw [exp_log _ inside] at raised
    exact (below_complement point.val _).mpr raised
  · apply uniform01.null_empty.mono
    intro point member
    apply member.2
    show lt (exponentialQuantile rate point) threshold
    rw [quantile_lt_iff ratePositive]
    have inside : lt (exp (neg (mul rate threshold))) (sub one point.val) :=
      (below_complement point.val _).mp member.1
    have logged := log_strict _ _ (exp_positive _) inside
    rwa [log_exp] at logged

/-- The quantile is nonnegative, so it sends nothing below a nonpositive `t`. -/
private theorem uniform01_quantile_iio_nonpositive {rate : Carrier} (ratePositive : lt zero rate)
    {threshold : Carrier} (nonpositive : le threshold zero) :
    uniform01 (Set.preimage (exponentialQuantile rate) (Iio threshold)) = ENNReal.zero := by
  have empty : Set.preimage (exponentialQuantile rate) (Iio threshold) = Set.empty := by
    apply Set.ext
    intro point
    refine ⟨fun below => ?_, fun member => member.elim⟩
    have logged := (quantile_lt_iff ratePositive point threshold).mp below
    have scaled : le (mul rate threshold) zero := by
      have reflected := (mul_le_mul_left_iff ratePositive).mpr nonpositive
      rwa [mul_zero] at reflected
    have start : le zero (neg (mul rate threshold)) := neg_nonnegative_iff.mpr scaled
    have capped : le (logIntegral (sub one point.val)) zero := by
      by_cases inside : lt zero (sub one point.val)
      · have bounded := log_monotone _ _ inside (complement_le_one point)
        rwa [log_one] at bounded
      · rw [log_of_nonpositive _ (not_lt_iff_le.mp inside)]
        exact le_refl zero
    exact logged.2 (le_trans capped start)
  rw [empty, Measure.empty_apply]

/-- Pushing the uniform law through the quantile gives the exponential law. -/
public theorem uniform01_map_exponentialQuantile {rate : Carrier} (ratePositive : lt zero rate) :
    uniform01.map (exponentialQuantile rate) (exponentialQuantile_measurable rate) =
      law one rate := by
  have mapped := uniform01_isProbability.map (exponentialQuantile rate)
    (exponentialQuantile_measurable rate)
  have target := law_isProbability one rate
  refine finite_measure_ext_iio mapped.to_finite target.to_finite
    (mapped.univ_eq_one.trans target.univ_eq_one.symm) fun threshold => ?_
  rw [Measure.map_apply _ _ _ (measurable_iio threshold)]
  by_cases positive : lt zero threshold
  · rw [uniform01_quantile_iio ratePositive threshold, law_one_iio ratePositive positive]
  · have nonpositive := not_lt_iff_le.mp positive
    rw [uniform01_quantile_iio_nonpositive ratePositive nonpositive,
      law_one_iio_nonpositive ratePositive nonpositive]

end
end Problib.Analysis.Gamma
