module

public import Problib.Analysis.Sqrt
public import Problib.Measure.Real.Moment
public import Problib.Measure.Integral.Density.Change

set_option autoImplicit false

namespace Problib.Analysis.SquareIntegral

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

/-- Squaring reflects strict order on the nonnegative ray. -/
public theorem square_lt_iff (left right : NNReal) :
    lt (mul left.val left.val) (mul right.val right.val) ↔ lt left.val right.val :=
  ⟨fun ordered => ⟨(square_le_iff left right).mp ordered.1,
      fun reverse => ordered.2 ((square_le_iff right left).mpr reverse)⟩,
    fun ordered => ⟨(square_le_iff left right).mpr ordered.1,
      fun reverse => ordered.2 ((square_le_iff right left).mp reverse)⟩⟩

/-- Positive volume weighted by its coordinate: the Jacobian measure for squaring. -/
@[expose] public def weightedVolume : Measure borel :=
  (volume.restrict (Ioi zero)).withDensity ENNReal.ofReal

private theorem positive_ray_mass (upper : Carrier) :
    (volume.restrict (Ioi zero)) (Iio upper) = ENNReal.ofReal upper := by
  rw [Measure.restrict_apply _ _ (measurable_iio upper)]
  have intersection : Set.inter (Iio upper) (Ioi zero) = Ioo zero upper :=
    Set.ext (fun _ => and_comm)
  rw [intersection, volume_ioo, sub_eq_add_neg, neg_zero, add_zero]

/-- The weighted square pushforward is exactly half of positive volume, on every measurable set. -/
public theorem map_square :
    weightedVolume.map (fun value => mul value value)
      (measurable_mul (MeasurableMap.identity borel) (MeasurableMap.identity borel)) =
        Measure.smul (ENNReal.ofReal (inverse (selection.ofRat 2))) (volume.restrict (Ioi zero)) := by
  apply measure_ext_iio
  · intro upper
    rw [Measure.smul_apply_measurable _ _ (measurable_iio upper), positive_ray_mass]
    exact ENNReal.mul_finite (ENNReal.ofReal_finite _) (ENNReal.ofReal_finite _)
  · intro upper
    have squareMeasurable : MeasurableMap borel borel (fun value => mul value value) := measurable_mul (MeasurableMap.identity borel) (MeasurableMap.identity borel)
    rw [Measure.map_apply _ _ _ (measurable_iio upper), weightedVolume,
      Measure.withDensity_apply _ _ (squareMeasurable (measurable_iio upper)),
      Measure.restrict_restrict volume _ (squareMeasurable (measurable_iio upper)),
      Measure.smul_apply_measurable _ _ (measurable_iio upper), positive_ray_mass]
    by_cases positive : lt zero upper
    · let endpoint : NNReal := ⟨upper, positive.1⟩
      let root := sqrt endpoint
      have squared : mul root.val root.val = upper := congrArg NNReal.toReal (sqrt_square endpoint)
      have intersection : Set.inter (Set.preimage (fun value => mul value value) (Iio upper)) (Ioi zero) =
          Ioo zero root.val := by
        apply Set.ext
        intro value
        constructor
        · intro member
          refine ⟨member.2, ?_⟩
          apply (square_lt_iff ⟨value, member.2.1⟩ root).mp
          exact squared.symm ▸ member.1
        · intro member
          refine ⟨?_, member.1⟩
          exact squared ▸ (square_lt_iff ⟨value, member.1.1⟩ root).mpr member.2
      rw [intersection, restrict_volume_ioo, first_moment root.val root.property, squared,
        div_eq_mul_inverse, mul_comm,
        ofReal_mul (inverse_of_positive_positive ofRat_two_positive).1 positive.1]
    · have nonpositive := not_lt_iff_le.mp positive
      have empty : Set.inter (Set.preimage (fun value => mul value value) (Iio upper)) (Ioi zero) = Set.empty := by
        apply Set.ext
        intro value
        exact ⟨fun member => member.1.2 (le_trans nonpositive (mul_nonnegative member.2.1 member.2.1)), False.elim⟩
      rw [empty, Measure.restrict_empty, lintegral_zero_measure,
        ENNReal.ofReal_eq_zero_iff.mpr nonpositive, ENNReal.mul_zero]

/-- Nonnegative square substitution, justified by the whole-measure Jacobian law. -/
public theorem integral {integrand : Carrier → ENNReal} (measurable : ENNRealMeasurable borel integrand) :
    lintegral (volume.restrict (Ioi zero))
      (fun value => ENNReal.mul (ENNReal.ofReal value) (integrand (mul value value))) =
        ENNReal.mul (ENNReal.ofReal (inverse (selection.ofRat 2)))
          (lintegral (volume.restrict (Ioi zero)) integrand) := by
  have squareMeasurable : MeasurableMap borel borel (fun value => mul value value) := measurable_mul (MeasurableMap.identity borel) (MeasurableMap.identity borel)
  rw [← lintegral_withDensity _ ofReal_measurable (measurable.comp squareMeasurable)]
  change lintegral weightedVolume (fun value => integrand (mul value value)) = _
  rw [← lintegral_map weightedVolume _ squareMeasurable measurable, map_square, lintegral_smul_measure]

end
end Problib.Analysis.SquareIntegral
