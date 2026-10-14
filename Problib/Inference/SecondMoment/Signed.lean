import Problib.Inference.Necessity.SecondMoment

set_option autoImplicit false

/-! A signed reading with a nonzero mean and centered moment. Splitting each
finite row into two equal rows preserves the law and its variance. -/

namespace Problib.Inference.SecondMomentSigned

open Problib.Real Problib.Measure Problib.Inference
open Problib.Real.Construction
open Problib.Measure.Real (Carrier)
open Problib.Inference.Necessity.Weighting
open Problib.Inference.Necessity.Density (two)
open Problib.Inference.SecondMomentWitnesses
open Problib.Inference.Necessity.SecondMoment

noncomputable def positive (b : Bool) : NNReal := if b then NNReal.one else NNReal.zero
noncomputable def negative (b : Bool) : NNReal := if b then NNReal.zero else NNReal.one

/-- Minus one on false and plus one on true. -/
noncomputable def signedReading (b : Bool) : Carrier :=
  Dedekind.sub (positive b).toReal (negative b).toReal

theorem signedReading_pin : signedReading =
    (fun b => Dedekind.sub (positive b).toReal (negative b).toReal) := rfl

noncomputable def signedTarget : Measure bools :=
  (fair bools false true).withDensity (fun b => ENNReal.finite (density b))

theorem signed_mean : HasRealIntegral signedTarget signedReading (Dedekind.selection.ofRat (1 / 2)) := by
  have pos := nnreal_integral (measure := signedTarget)
    (MeasurableMap.from_discrete weightSpace positive) NNReal.one (by
      rw [signedTarget, lintegral_withDensity _ (finite_weight_measurable density_measurable)
        (finite_weight_measurable (MeasurableMap.from_discrete weightSpace positive)),
        lintegral_fair _ _ _ ((finite_weight_measurable density_measurable).mul
          (finite_weight_measurable (MeasurableMap.from_discrete weightSpace positive)))]
      show ENNReal.mul halfMass (ENNReal.add (ENNReal.mul ENNReal.one ENNReal.zero)
        (ENNReal.mul (ENNReal.ofRat 2 (by decide +kernel)) ENNReal.one)) = ENNReal.one
      rw [ENNReal.mul_zero, ENNReal.mul_one, ENNReal.zero_add,
        half_ofRat 2 1 _ (by decide +kernel) (by decide +kernel), ENNReal.ofRat_one])
  have neg := nnreal_integral (measure := signedTarget)
    (MeasurableMap.from_discrete weightSpace negative) (rationalWeight (1 / 2) (by decide +kernel)) (by
      rw [signedTarget, lintegral_withDensity _ (finite_weight_measurable density_measurable)
        (finite_weight_measurable (MeasurableMap.from_discrete weightSpace negative)),
        lintegral_fair _ _ _ ((finite_weight_measurable density_measurable).mul
          (finite_weight_measurable (MeasurableMap.from_discrete weightSpace negative)))]
      show ENNReal.mul halfMass (ENNReal.add (ENNReal.mul ENNReal.one ENNReal.one)
        (ENNReal.mul (ENNReal.ofRat 2 (by decide +kernel)) ENNReal.zero)) = halfMass
      rw [ENNReal.mul_one, ENNReal.mul_zero, ENNReal.add_zero, ENNReal.mul_one])
  have combined := pos.sub neg
  have value : Dedekind.sub NNReal.one.toReal
      (rationalWeight (1 / 2) (by decide +kernel)).toReal = Dedekind.selection.ofRat (1 / 2) := by
    rw [NNReal.toReal_one, rationalWeight, NNReal.toReal_ofRat,
      ← Dedekind.ofRat_one, ← Dedekind.ofRat_sub]
    exact congrArg Dedekind.selection.ofRat (by decide +kernel)
  rw [value] at combined
  exact combined

theorem square_signedReading (b : Bool) :
    Dedekind.mul (signedReading b) (signedReading b) = Dedekind.one := by
  cases b
  · change Dedekind.mul (Dedekind.sub Dedekind.zero Dedekind.one)
      (Dedekind.sub Dedekind.zero Dedekind.one) = Dedekind.one
    rw [Dedekind.sub_eq_add_neg, Dedekind.zero_add, Dedekind.neg_mul_neg, Dedekind.mul_one]
  · change Dedekind.mul (Dedekind.sub Dedekind.one Dedekind.zero)
      (Dedekind.sub Dedekind.one Dedekind.zero) = Dedekind.one
    rw [Dedekind.sub_zero, Dedekind.mul_one]

theorem signed_raw : HasRealIntegral (secondMoment deterministicLaw)
    (fun b => Dedekind.mul (signedReading b) (signedReading b)) (Dedekind.selection.ofRat (5 / 2)) := by
  have raw := one_integral (rationalWeight (5 / 2) (by decide +kernel)) deterministic_mass
  have square := raw.congr (fun b => (square_signedReading b).symm)
  simpa only [rationalWeight, NNReal.toReal_ofRat] using square

/-- Weighted reading is minus one or plus two, fairly. Its mean is one half,
raw moment five halves and variance nine quarters. -/
theorem signed_variance : HasRealIntegral deterministicLaw
    (fun draw => Dedekind.mul
      (Dedekind.sub (Dedekind.mul (signedReading draw.1) draw.2.toReal) (Dedekind.selection.ofRat (1 / 2)))
      (Dedekind.sub (Dedekind.mul (signedReading draw.1) draw.2.toReal) (Dedekind.selection.ofRat (1 / 2))))
    (Dedekind.selection.ofRat (9 / 4)) := by
  have centered := centered_of_secondMoment common_target.1 signed_mean signed_raw
  rw [← Dedekind.ofRat_mul, ← Dedekind.ofRat_sub] at centered
  have value : Dedekind.selection.ofRat (5 / 2 - (1 / 2) * (1 / 2)) = Dedekind.selection.ofRat (9 / 4) :=
    congrArg Dedekind.selection.ofRat (by decide +kernel)
  rw [value] at centered
  exact centered

/-- Four rows: each of the two delivered rows appears twice at half its mass. -/
noncomputable def splitRows : Measure (Space.product bools weightSpace) :=
  Measure.smul halfMass (Measure.add deterministicLaw deterministicLaw)

theorem splitRows_pin : splitRows =
    Measure.smul halfMass (Measure.add deterministicLaw deterministicLaw) := rfl

theorem splitRows_same_law : splitRows = deterministicLaw := by
  refine (Measure.eq_iff_lintegral _ _).mpr fun function _ => ?_
  rw [splitRows, lintegral_smul_measure, lintegral_add_measure]
  have normalize : ENNReal.mul halfMass (ENNReal.add ENNReal.one ENNReal.one) = ENNReal.one := by
    rw [← ENNReal.ofRat_one]
    exact half_sum_ofRat 1 1 1 _ _ _ (by decide +kernel)
  have same := half_sum_scale ENNReal.one ENNReal.one (lintegral deterministicLaw function)
  simpa only [ENNReal.one_mul, normalize] using same

theorem splitRows_variance : HasRealIntegral splitRows
    (fun draw => Dedekind.mul
      (Dedekind.sub (Dedekind.mul (signedReading draw.1) draw.2.toReal) (Dedekind.selection.ofRat (1 / 2)))
      (Dedekind.sub (Dedekind.mul (signedReading draw.1) draw.2.toReal) (Dedekind.selection.ofRat (1 / 2))))
    (Dedekind.selection.ofRat (9 / 4)) := by
  rw [splitRows_same_law]
  exact signed_variance

end Problib.Inference.SecondMomentSigned
