module

public import Problib.Inference.Resampling
public import Problib.Inference.Necessity.Weighting
set_option autoImplicit false

/-! Necessity for resampling.

A child must carry the mean parent weight `W/N`. Resetting the weight to one
breaks calibration outright: a one-lane law with weights `1` and `3` is
calibrated for `(1/2)δ_false + (3/2)δ_true`, and after the reset it is
calibrated for no positive multiple of that target
(`reset_weight_uncalibrated`). At one lane the mean weight is the weight, so
`resample` keeps it. A normalizable target does not make a sampled population's
total weight positive, which is why the zero-weight policy is declared rather
than assumed away (`zero_total_positive_target`). -/

namespace Problib.Inference.Necessity.Resampling

open Problib.Real Problib.Measure
open Problib.Inference.Necessity.Weighting (bools fair halfMass rationalWeight fair_probability
  lintegral_fair half_ofRat)
open Problib.Measure.SimpleFunction (finiteSum)

public section

/-! ### Necessity 1: the reset weight -/

/-- A fair draw with weight `1` at `false` and `3` at `true`. -/
@[expose] noncomputable def unevenLaw : Measure (Space.product bools weightSpace) :=
  fair (Space.product bools weightSpace)
    (false, rationalWeight 1 (by decide +kernel)) (true, rationalWeight 3 (by decide +kernel))

/-- The target it is calibrated for, `(1/2)δ_false + (3/2)δ_true`. -/
@[expose] noncomputable def unevenTarget : Measure bools :=
  Measure.add (Measure.smul halfMass (Measure.dirac bools false))
    (Measure.smul (ENNReal.ofRat (3 / 2) (by decide +kernel)) (Measure.dirac bools true))

/-- Reset every weight to one. -/
theorem reset_measurable :
    MeasurableMap (Space.product bools weightSpace) (Space.product bools weightSpace)
      (fun draw => (draw.1, NNReal.one)) :=
  Space.pair_measurable (Space.first_measurable bools weightSpace)
    (MeasurableMap.constant _ weightSpace NNReal.one)

/-- The law is calibrated for the uneven target. After the reset it is
calibrated for `(1/2)δ_false + (1/2)δ_true`, which is no multiple of the uneven
target, so no scale of the target is calibrated. -/
theorem reset_weight_uncalibrated :
    Calibrated unevenTarget unevenLaw ∧
      ∀ scale : ENNReal,
        ¬Calibrated (Measure.smul scale unevenTarget)
          (unevenLaw.map (fun draw => (draw.1, NNReal.one)) reset_measurable) := by
  have targetIntegral : ∀ function : Bool → ENNReal, lintegral unevenTarget function =
      ENNReal.add (ENNReal.mul halfMass (function false))
        (ENNReal.mul (ENNReal.ofRat (3 / 2) (by decide +kernel)) (function true)) := by
    intro function
    have measurable := ENNRealMeasurable.of_measurableMap
      (MeasurableMap.from_discrete ennrealBorel function)
    rw [unevenTarget, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
      lintegral_dirac _ _ measurable, lintegral_dirac _ _ measurable]
  have calibrated : Calibrated unevenTarget unevenLaw := by
    refine calibrated_iff_lintegral.mpr ⟨fair_probability _ _ _, fun function measurable => ?_⟩
    rw [unevenLaw, lintegral_fair _ _ _ (weighted_integrand_measurable measurable),
      targetIntegral]
    show ENNReal.mul halfMass (ENNReal.add
        (ENNReal.mul (ENNReal.ofRat 1 (by decide +kernel)) (function false))
        (ENNReal.mul (ENNReal.ofRat 3 (by decide +kernel)) (function true))) = _
    rw [ENNReal.mul_add, ← ENNReal.mul_assoc, ← ENNReal.mul_assoc,
      half_ofRat 1 (1 / 2) _ (by decide +kernel) (by decide +kernel),
      half_ofRat 3 (3 / 2) _ (by decide +kernel) (by decide +kernel)]
    rfl
  refine ⟨calibrated, fun scale reset => ?_⟩
  -- The reset law is the fair choice of `(false, 1)` and `(true, 1)`. Reading it
  -- at the indicator of `false` gives `1/2 = c/2`, and at the indicator of
  -- `true` it gives `1/2 = 3c/2`, so `1/2 = 3/2`.
  have resetLaw : unevenLaw.map (fun draw => (draw.1, NNReal.one)) reset_measurable =
      fair (Space.product bools weightSpace) (false, NNReal.one) (true, NNReal.one) := by
    rw [unevenLaw, fair, Measure.map_smul, Measure.map_add, Measure.map_dirac, Measure.map_dirac]
    rfl
  rw [resetLaw] at reset
  have indicator : ∀ function : Bool → ENNReal,
      ENNReal.mul halfMass (ENNReal.add (ENNReal.mul ENNReal.one (function false))
          (ENNReal.mul ENNReal.one (function true))) =
        ENNReal.mul scale (ENNReal.add (ENNReal.mul halfMass (function false))
          (ENNReal.mul (ENNReal.ofRat (3 / 2) (by decide +kernel)) (function true))) := by
    intro function
    have measurable := ENNRealMeasurable.of_measurableMap
      (MeasurableMap.from_discrete ennrealBorel function)
    have equation := reset.lintegral measurable
    rw [lintegral_fair _ _ _ (weighted_integrand_measurable measurable), lintegral_smul_measure,
      targetIntegral] at equation
    exact equation
  have falseEquation := indicator fun value => if value then ENNReal.zero else ENNReal.one
  have trueEquation := indicator fun value => if value then ENNReal.one else ENNReal.zero
  change ENNReal.mul halfMass (ENNReal.add (ENNReal.mul ENNReal.one ENNReal.one)
      (ENNReal.mul ENNReal.one ENNReal.zero)) =
    ENNReal.mul scale (ENNReal.add (ENNReal.mul halfMass ENNReal.one)
      (ENNReal.mul (ENNReal.ofRat (3 / 2) (by decide +kernel)) ENNReal.zero)) at falseEquation
  change ENNReal.mul halfMass (ENNReal.add (ENNReal.mul ENNReal.one ENNReal.zero)
      (ENNReal.mul ENNReal.one ENNReal.one)) =
    ENNReal.mul scale (ENNReal.add (ENNReal.mul halfMass ENNReal.zero)
      (ENNReal.mul (ENNReal.ofRat (3 / 2) (by decide +kernel)) ENNReal.one)) at trueEquation
  simp only [ENNReal.mul_one, ENNReal.mul_zero, ENNReal.add_zero, ENNReal.zero_add]
    at falseEquation trueEquation
  rw [← half_ofRat 3 (3 / 2) (by decide +kernel) (by decide +kernel) (by decide +kernel),
    ENNReal.mul_comm halfMass, ← ENNReal.mul_assoc, ENNReal.mul_comm scale,
    ENNReal.mul_assoc, ← falseEquation, ENNReal.mul_comm,
    half_ofRat 3 (3 / 2) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
    at trueEquation
  have bound : ENNReal.le (ENNReal.ofRat (3 / 2) (by decide +kernel))
      (ENNReal.ofRat (1 / 2) (by decide +kernel)) := by
    rw [← trueEquation]
    exact ENNReal.le_refl _
  exact absurd ((ENNReal.ofRat_le_iff _ _ _ _).mp bound) (by decide +kernel)

/-! ### Necessity 7: a zero total with a positive target -/

/-- One lane. -/
@[expose] def oneLane : Lanes (Fin 1) := Lanes.fin 1

/-- One-lane importance draws from the fair coin for `δ_true`: weight `0` at
`false` and `2` at `true`. -/
@[expose] noncomputable def zeroOrTwo : Measure (populationSpace (Fin 1) bools) :=
  fair (populationSpace (Fin 1) bools)
    (fun _ => (false, NNReal.zero)) (fun _ => (true, rationalWeight 2 (by decide +kernel)))

/-- The population is invariant for `δ_true`, whose mass is one, and its total
weight is zero with probability one half. -/
theorem zero_total_positive_target :
    EmpiricalInvariant oneLane (Measure.dirac bools true) zeroOrTwo ∧
      zeroOrTwo (fun draws => totalWeight oneLane draws = NNReal.zero) = halfMass := by
  have single : ∀ values : Fin 1 → ENNReal,
      ENNReal.mul (ENNReal.finite oneLane.share) (finiteSum (oneLane.list.map values)) =
        values 0 :=
    fun values => oneLane.average_const (values 0)
  refine ⟨⟨fair_probability _ _ _, ?_⟩, ?_⟩
  · refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
    rw [Measure.lintegral_bind _ _ measurable, zeroOrTwo,
      lintegral_fair _ _ _ (Kernel.lintegral_measurable _ measurable),
      lintegral_empirical oneLane _ measurable, lintegral_empirical oneLane _ measurable,
      single, single, lintegral_dirac _ _ measurable]
    show ENNReal.mul halfMass (ENNReal.add (ENNReal.mul ENNReal.zero (function false))
        (ENNReal.mul (ENNReal.ofRat 2 (by decide +kernel)) (function true))) = function true
    rw [ENNReal.zero_mul, ENNReal.zero_add, ← ENNReal.mul_assoc,
      half_ofRat 2 1 _ (by decide +kernel) (by decide +kernel), ENNReal.ofRat_one,
      ENNReal.one_mul]
  · have region : (populationSpace (Fin 1) bools).Measurable
        (fun draws => totalWeight oneLane draws = NNReal.zero) := by
      have preimage := (finite_weight_measurable
        (totalWeight_measurable oneLane bools)).singleton ENNReal.zero
      have same : (fun draws : Fin 1 → Bool × NNReal => totalWeight oneLane draws = NNReal.zero) =
          Set.preimage (fun draws => ENNReal.finite (totalWeight oneLane draws))
            (ennrealSingleton ENNReal.zero) :=
        funext fun draws =>
          propext ⟨congrArg ENNReal.finite, fun equal => ENNReal.finite_injective equal⟩
      rw [same]
      exact preimage
    rw [zeroOrTwo, fair, Measure.smul_apply_measurable _ _ region,
      Measure.add_apply_measurable _ _ region,
      Measure.dirac_apply_of_mem _ _ region (by
        show NNReal.add NNReal.zero NNReal.zero = NNReal.zero
        exact NNReal.add_zero _),
      Measure.dirac_apply_of_not_mem _ _ region (by
        intro zero
        have ordered := (NNReal.ofRat_lt_iff 0 2 (by decide +kernel) (by decide +kernel)).mpr
          (by decide +kernel)
        have same : NNReal.ofRat 2 (by decide +kernel) = NNReal.zero :=
          (NNReal.add_zero _).symm.trans zero
        rw [NNReal.ofRat_zero, same] at ordered
        exact NNReal.lt_irrefl _ ordered),
      ENNReal.add_zero, ENNReal.mul_one]

end

end Problib.Inference.Necessity.Resampling
