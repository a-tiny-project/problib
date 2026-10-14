import Problib.Inference.SecondMoment.Witnesses

set_option autoImplicit false

/-! Two premises that first moments cannot replace.

A continuation that reads the incoming weight can correlate the two weights.
An unbiased density estimate can have a larger second moment than its mean.
Both counterexamples evaluate the actual delivered joint law. -/

namespace Problib.Inference.Necessity.SecondMoment

open Problib.Real Problib.Measure Problib.Inference
open Problib.Inference.Necessity.Weighting
open Problib.Inference.Necessity.Density (two zeroOrTwo)
open Problib.Inference.SecondMomentWitnesses

/-- The continuation returns the incoming weight: the final weight is u*u. -/
noncomputable def correlatedLaw : Measure (Space.product point weightSpace) :=
  (zeroOrTwo ()).map squareWeight (squareWeight_measurable point)

theorem correlatedLaw_pin : correlatedLaw =
    (zeroOrTwo ()).map (fun draw => (draw.1, NNReal.mul draw.2 draw.2))
      (squareWeight_measurable point) := rfl

/-- True squared product has mass eight. Multiplying the two marginal second
moments gives four, so unconditional multiplication is unsound. -/
theorem weight_dependent_continuation :
    (secondMoment correlatedLaw) Set.univ = ENNReal.ofRat 8 (by decide +kernel) ∧
    ENNReal.mul ((secondMoment (zeroOrTwo ())) Set.univ)
      ((secondMoment (zeroOrTwo ())) Set.univ) = ENNReal.ofRat 4 (by decide +kernel) ∧
    ENNReal.ofRat 8 (by decide +kernel) ≠ ENNReal.ofRat 4 (by decide +kernel) := by
  have mass : (secondMoment (zeroOrTwo ())) Set.univ = ENNReal.ofRat 2 (by decide +kernel) := by
    rw [split_moment, Measure.smul_apply_measurable _ _ point.univ,
      Measure.dirac_apply_univ, ENNReal.mul_one]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [correlatedLaw, Necessity.Density.zeroOrTwo, Kernel.const_apply, map_fair, moment_fair,
      Measure.smul_apply_measurable _ _ point.univ,
      Measure.add_apply_measurable _ _ point.univ,
      Measure.smul_apply_measurable _ _ point.univ,
      Measure.smul_apply_measurable _ _ point.univ, Measure.dirac_apply_univ]
    simp only [ENNReal.mul_one]
    show ENNReal.mul halfMass (ENNReal.add
      (ENNReal.mul (ENNReal.mul ENNReal.zero ENNReal.zero) (ENNReal.mul ENNReal.zero ENNReal.zero))
      (ENNReal.mul (ENNReal.mul (ENNReal.ofRat 2 (by decide +kernel)) (ENNReal.ofRat 2 (by decide +kernel)))
        (ENNReal.mul (ENNReal.ofRat 2 (by decide +kernel)) (ENNReal.ofRat 2 (by decide +kernel))))) = _
    rw [ENNReal.zero_mul, ENNReal.zero_mul, ENNReal.zero_add,
      ← ENNReal.ofRat_mul, ← ENNReal.ofRat_mul]
    exact half_ofRat ((2 * 2) * (2 * 2)) 8 _ (by decide +kernel) (by decide +kernel)
  · rw [mass, ← ENNReal.ofRat_mul]
    exact ofRat_congr (by decide +kernel) _ _
  · intro same
    have below : ENNReal.le (ENNReal.ofRat 8 (by decide +kernel))
        (ENNReal.ofRat 4 (by decide +kernel)) := by
      rw [same]
      exact ENNReal.le_refl _
    exact absurd ((ENNReal.ofRat_le_iff _ _ _ _).mp below) (by decide +kernel)

/-- The split product's raw moment is four, while duplicating one lane gives
eight. The duplicated law also has a different mean, so this compares raw
moments rather than centered variances about a common mean. -/
theorem independent_against_duplicated :
    (secondMoment independentLaw) Set.univ = ENNReal.ofRat 4 (by decide +kernel) ∧
    (secondMoment correlatedLaw) Set.univ = ENNReal.ofRat 8 (by decide +kernel) ∧
    (secondMoment independentLaw) Set.univ ≠ (secondMoment correlatedLaw) Set.univ := by
  refine ⟨independent_mass, weight_dependent_continuation.1, ?_⟩
  rw [independent_mass, weight_dependent_continuation.1]
  exact fun same => weight_dependent_continuation.2.2 same.symm

/-- A two-point proposal has density one on false and two on true. -/
noncomputable def density (b : Bool) : NNReal := if b then two else NNReal.one

theorem density_measurable : MeasurableMap bools weightSpace density :=
  MeasurableMap.from_discrete weightSpace density

/-- Deterministic importance with the nonconstant two-point density. -/
noncomputable def deterministicLaw : Measure (Space.product bools weightSpace) :=
  (fair bools false true).map (fun b => (b, density b))
    (Space.pair_measurable (MeasurableMap.identity bools) density_measurable)

theorem deterministicLaw_pin : deterministicLaw =
    (fair bools false true).map (fun b => (b, density b))
      (Space.pair_measurable (MeasurableMap.identity bools) density_measurable) := rfl

/-- Conditional estimates are zero or twice their conditional mean. -/
noncomputable def randomEstimate : Kernel bools weightSpace where
  toFun := fun b => fair weightSpace NNReal.zero (NNReal.mul two (density b))
  measurable := fun {_} _ => ENNRealMeasurable.of_measurableMap
    (MeasurableMap.from_discrete ennrealBorel _)

theorem randomEstimate_pin (b : Bool) : randomEstimate b =
    fair weightSpace NNReal.zero (NNReal.mul two (density b)) := rfl

theorem randomEstimate_unbiased :
    UnbiasedEstimate (fun b => ENNReal.finite (density b)) randomEstimate := by
  refine ⟨fun _ => fair_probability _ _ _, fun b => ?_⟩
  change lintegral (fair weightSpace NNReal.zero (NNReal.mul two (density b))) _ = _
  rw [lintegral_fair _ _ _ (finite_weight_measurable (MeasurableMap.identity weightSpace))]
  cases b
  · show ENNReal.mul halfMass (ENNReal.add ENNReal.zero
      (ENNReal.mul (ENNReal.ofRat 2 (by decide +kernel)) ENNReal.one)) = ENNReal.one
    rw [ENNReal.zero_add, ENNReal.mul_one, half_ofRat 2 1 _ (by decide +kernel) (by decide +kernel),
      ENNReal.ofRat_one]
  · show ENNReal.mul halfMass (ENNReal.add ENNReal.zero
      (ENNReal.mul (ENNReal.ofRat 2 (by decide +kernel)) (ENNReal.ofRat 2 (by decide +kernel)))) = _
    rw [ENNReal.zero_add, ← ENNReal.ofRat_mul]
    exact half_ofRat (2 * 2) 2 _ (by decide +kernel) (by decide +kernel)

/-- Draw the value fairly, then its unbiased random density estimate. -/
noncomputable def randomizedLaw : Measure (Space.product bools weightSpace) :=
  (fair bools false true).semiproduct randomEstimate
    (Kernel.IsSFinite.ofMarkov randomEstimate_unbiased.probability)

theorem randomizedLaw_pin : randomizedLaw =
    (fair bools false true).semiproduct randomEstimate
      (Kernel.IsSFinite.ofMarkov randomEstimate_unbiased.probability) := rfl

theorem common_target :
    ProperlyWeighted ((fair bools false true).withDensity (fun b => ENNReal.finite (density b)))
      deterministicLaw ∧
    ProperlyWeighted ((fair bools false true).withDensity (fun b => ENNReal.finite (density b)))
      randomizedLaw :=
  ⟨importance_weighted (fair_probability _ _ _) density_measurable rfl,
    importance_estimated_weighted (fair_probability _ _ _)
      (Kernel.IsSFinite.ofMarkov randomEstimate_unbiased.probability) randomEstimate_unbiased rfl⟩

/-- The deterministic shortcut is valid for the deterministic joint law. -/
theorem deterministic_shortcut :
    secondMoment deterministicLaw =
      ((fair bools false true).withDensity (fun b => ENNReal.finite (density b))).withDensity
        (fun b => ENNReal.finite (density b)) :=
  secondMoment_importance_target density_measurable rfl

/-- Raw mass of deterministic importance is five halves. -/
theorem deterministic_mass : (secondMoment deterministicLaw) Set.univ =
    ENNReal.ofRat (5 / 2) (by decide +kernel) := by
  rw [moment_mass, deterministicLaw,
    lintegral_map _ _ (Space.pair_measurable (MeasurableMap.identity bools) density_measurable)
      ((drawWeight_measurable bools).mul (drawWeight_measurable bools))]
  simp only [drawWeight]
  rw [lintegral_fair _ _ _ ((finite_weight_measurable density_measurable).mul
      (finite_weight_measurable density_measurable))]
  show ENNReal.mul halfMass (ENNReal.add (ENNReal.mul ENNReal.one ENNReal.one)
    (ENNReal.mul (ENNReal.ofRat 2 (by decide +kernel)) (ENNReal.ofRat 2 (by decide +kernel)))) = _
  rw [ENNReal.mul_one, ← ENNReal.ofRat_one, ← ENNReal.ofRat_mul]
  exact half_sum_ofRat 1 (2 * 2) (5 / 2) _ _ _ (by decide +kernel)

/-- Random unbiased estimates double the conditional second moment here. -/
theorem randomized_mass : (secondMoment randomizedLaw) Set.univ =
    ENNReal.ofRat 5 (by decide +kernel) := by
  rw [moment_mass, randomizedLaw,
    lintegral_semiproduct _ _ _ ((drawWeight_measurable bools).mul (drawWeight_measurable bools))]
  have inner : ∀ b : Bool, lintegral (randomEstimate b)
      (fun w => ENNReal.mul (ENNReal.finite w) (ENNReal.finite w)) =
      ENNReal.mul (ENNReal.finite two)
        (ENNReal.mul (ENNReal.finite (density b)) (ENNReal.finite (density b))) := by
    intro b
    change lintegral (fair weightSpace NNReal.zero (NNReal.mul two (density b))) _ = _
    rw [lintegral_fair _ _ _ ((finite_weight_measurable (MeasurableMap.identity weightSpace)).mul
      (finite_weight_measurable (MeasurableMap.identity weightSpace)))]
    cases b
    · show ENNReal.mul halfMass (ENNReal.add (ENNReal.mul ENNReal.zero ENNReal.zero)
        (ENNReal.mul (ENNReal.mul (ENNReal.ofRat 2 (by decide +kernel)) ENNReal.one)
          (ENNReal.mul (ENNReal.ofRat 2 (by decide +kernel)) ENNReal.one))) = _
      rw [ENNReal.zero_mul, ENNReal.zero_add, ENNReal.mul_one,
        ← ENNReal.ofRat_mul, half_ofRat (2 * 2) 2 _ (by decide +kernel) (by decide +kernel)]
      change ENNReal.ofRat 2 (by decide +kernel) =
        ENNReal.mul (ENNReal.ofRat 2 (by decide +kernel)) (ENNReal.mul ENNReal.one ENNReal.one)
      simp only [ENNReal.mul_one]
    · show ENNReal.mul halfMass (ENNReal.add (ENNReal.mul ENNReal.zero ENNReal.zero)
        (ENNReal.mul (ENNReal.mul (ENNReal.ofRat 2 (by decide +kernel)) (ENNReal.ofRat 2 (by decide +kernel)))
          (ENNReal.mul (ENNReal.ofRat 2 (by decide +kernel)) (ENNReal.ofRat 2 (by decide +kernel))))) = _
      rw [ENNReal.zero_mul, ENNReal.zero_add, ← ENNReal.ofRat_mul,
        ← ENNReal.ofRat_mul, half_ofRat ((2 * 2) * (2 * 2)) 8 _ (by decide +kernel) (by decide +kernel)]
      change ENNReal.ofRat 8 (by decide +kernel) =
        ENNReal.mul (ENNReal.ofRat 2 (by decide +kernel))
          (ENNReal.mul (ENNReal.ofRat 2 (by decide +kernel)) (ENNReal.ofRat 2 (by decide +kernel)))
      rw [← ENNReal.ofRat_mul, ← ENNReal.ofRat_mul]
      exact ofRat_congr (by decide +kernel) _ _
  simp only [drawWeight]
  rw [lintegral_congr _ inner,
    lintegral_fair _ _ _ (ENNRealMeasurable.of_measurableMap
      (MeasurableMap.from_discrete ennrealBorel _))]
  show ENNReal.mul halfMass (ENNReal.add
    (ENNReal.mul (ENNReal.ofRat 2 (by decide +kernel)) (ENNReal.mul ENNReal.one ENNReal.one))
    (ENNReal.mul (ENNReal.ofRat 2 (by decide +kernel))
      (ENNReal.mul (ENNReal.ofRat 2 (by decide +kernel)) (ENNReal.ofRat 2 (by decide +kernel))))) = _
  rw [ENNReal.mul_one, ENNReal.mul_one, ← ENNReal.ofRat_mul, ← ENNReal.ofRat_mul]
  exact half_sum_ofRat 2 (2 * (2 * 2)) 5 _ _ _ (by decide +kernel)

/-- The same conditional mean does not justify the deterministic shortcut. -/
theorem random_density_shortcut_wrong :
    ENNReal.lt ((secondMoment deterministicLaw) Set.univ) ((secondMoment randomizedLaw) Set.univ) ∧
    secondMoment randomizedLaw ≠
      ((fair bools false true).withDensity (fun b => ENNReal.finite (density b))).withDensity
        (fun b => ENNReal.finite (density b)) := by
  have smaller : ENNReal.lt ((secondMoment deterministicLaw) Set.univ)
      ((secondMoment randomizedLaw) Set.univ) := by
    rw [deterministic_mass, randomized_mass]
    exact (ENNReal.ofRat_lt_iff _ _ _ _).mpr (by decide +kernel)
  refine ⟨smaller, fun same => ?_⟩
  have equal : (secondMoment deterministicLaw) Set.univ = (secondMoment randomizedLaw) Set.univ :=
    congrArg (fun law => law Set.univ) (deterministic_shortcut.trans same.symm)
  rw [equal] at smaller
  exact smaller.2 (ENNReal.le_refl _)

end Problib.Inference.Necessity.SecondMoment
