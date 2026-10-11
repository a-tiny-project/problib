module

public import Problib.Inference.Density
public import Problib.Inference.Necessity.Weighting
set_option autoImplicit false

/-! Necessity for the estimated bind.

The estimated bind asks for an estimate that is unbiased given the whole
weighted draw `(a, W)`. An estimate that is unbiased only after the weight is
forgotten can be correlated with the weight, and then `W·e` is biased.

The weighted draw here has one value, with weight `0` or `2` at probability one
half each, so it is properly weighted for the unit Dirac target. The estimate is
`2` at weight `0` and `0` at weight `2`. Averaged over the weighted draw its
mean is `1 = b`, which is what conditioning on the value alone sees. But `W·e`
is `0` at both draws, so `weightTimes` has mean `0`, not `1`
(`value_conditioning_insufficient`). The estimate that reads the whole draw
and has conditional mean `b` passes `unbiased_density_bind`
(`full_conditioning_sufficient`).

Proofs are finite evaluations of Dirac sums. -/

namespace Problib.Inference.Necessity.Density

open Problib.Real Problib.Measure Problib.Inference
open Problib.Inference.Necessity.Weighting

public section

/-- The weight two. -/
@[expose] def two : NNReal := rationalWeight 2 (by decide +kernel)

theorem two_ne_zero : two ≠ NNReal.zero := by
  intro same
  have bound : ENNReal.le (ENNReal.ofRat 2 (by decide +kernel))
      (ENNReal.ofRat 0 (by decide +kernel)) := by
    rw [ENNReal.ofRat_zero]
    show ENNReal.le (ENNReal.finite two) (ENNReal.finite NNReal.zero)
    rw [same]
    exact ENNReal.le_refl _
  exact absurd ((ENNReal.ofRat_le_iff _ _ _ _).mp bound) (by decide +kernel)

/-- The unit Dirac target at every input. -/
@[expose] noncomputable def unitTarget : Kernel point point :=
  Kernel.const point (Measure.dirac point ())

/-- The one value, with weight zero or two, fairly. -/
@[expose] noncomputable def zeroOrTwo : Kernel point (Space.product point weightSpace) :=
  Kernel.const point (fair (Space.product point weightSpace) ((), NNReal.zero) ((), two))

theorem zeroOrTwo_properlyWeighted (input : Unit) :
    ProperlyWeighted (unitTarget input) (zeroOrTwo input) := by
  refine properlyWeighted_iff_lintegral.mpr ⟨fair_probability _ _ _, fun function measurable => ?_⟩
  rw [zeroOrTwo, Kernel.const_apply,
    lintegral_fair _ _ _ (weighted_integrand_measurable measurable),
    unitTarget, Kernel.const_apply, lintegral_dirac _ _ measurable]
  show ENNReal.mul halfMass (ENNReal.add (ENNReal.mul ENNReal.zero (function ()))
      (ENNReal.mul (ENNReal.ofRat 2 (by decide +kernel)) (function ()))) = function ()
  rw [ENNReal.zero_mul, ENNReal.zero_add, ← ENNReal.mul_assoc,
    half_ofRat 2 1 _ (by decide +kernel) (by decide +kernel), ENNReal.ofRat_one,
    ENNReal.one_mul]

open Classical in
/-- Two at weight zero, and zero at any other weight. -/
@[expose] noncomputable def correlated (weight : NNReal) : NNReal :=
  if weight = NNReal.zero then two else NNReal.zero

theorem correlated_measurable : MeasurableMap weightSpace weightSpace correlated := by
  apply weight_measurable_of_finite
  have region := weight_value_measurable.singleton ENNReal.zero
  have same : (fun weight => ENNReal.finite (correlated weight)) = ennrealPiecewise
      (Set.preimage (fun weight : NNReal => ENNReal.finite weight)
        (ennrealSingleton ENNReal.zero))
      (fun _ => ENNReal.finite two) (fun _ => ENNReal.finite NNReal.zero) := by
    funext weight
    unfold correlated ennrealPiecewise
    by_cases zero : weight = NNReal.zero
    · have atZero : Set.preimage (fun weight : NNReal => ENNReal.finite weight)
          (ennrealSingleton ENNReal.zero) weight := congrArg ENNReal.finite zero
      rw [ite_eq_left zero, ite_eq_left atZero]
    · have away : ¬Set.preimage (fun weight : NNReal => ENNReal.finite weight)
          (ennrealSingleton ENNReal.zero) weight :=
        fun atZero => zero (ENNReal.finite_injective atZero)
      rw [ite_eq_right zero, ite_eq_right away]
  rw [same]
  exact ENNRealMeasurable.piecewise region (ENNRealMeasurable.constant _ _)
    (ENNRealMeasurable.constant _ _)

theorem dirac_probability {α : Type} (space : Space α) (value : α) :
    Measure.IsProbability (Measure.dirac space value) :=
  ⟨Measure.dirac_apply_univ space value⟩

/-- The deterministic estimate `correlated W`, read from the whole input. -/
@[expose] noncomputable def correlatedEstimate :
    Kernel (bindEstimateInput point point point) weightSpace :=
  Kernel.deterministic (fun input => correlated input.2.2)
    (MeasurableMap.comp correlated_measurable
      (MeasurableMap.comp (Space.second_measurable point weightSpace)
        (Space.second_measurable (Space.product point point)
          (Space.product point weightSpace))))

theorem correlatedEstimate_mean (input : (Unit × Unit) × (Unit × NNReal)) :
    lintegral (correlatedEstimate input) (fun weight => ENNReal.finite weight) =
      ENNReal.finite (correlated input.2.2) := by
  show lintegral (Measure.dirac weightSpace (correlated input.2.2)) _ = _
  rw [lintegral_dirac _ _ weight_value_measurable]

/-- The mean of the correlated estimate over the weighted draw, where the
estimate at `(a, W)` is averaged with the weight forgotten. -/
theorem correlated_value_mean (pair : Unit × Unit) :
    lintegral (zeroOrTwo pair.1) (fun draw =>
      lintegral (correlatedEstimate (pair, draw)) (fun weight => ENNReal.finite weight)) =
      ENNReal.one := by
  have estimateMeasurable : ENNRealMeasurable (Space.product point weightSpace)
      (fun draw : Unit × NNReal => ENNReal.finite (correlated draw.2)) :=
    finite_weight_measurable (MeasurableMap.comp correlated_measurable
      (Space.second_measurable point weightSpace))
  rw [lintegral_congr _ (fun draw => correlatedEstimate_mean (pair, draw)),
    zeroOrTwo, Kernel.const_apply, lintegral_fair _ _ _ estimateMeasurable]
  show ENNReal.mul halfMass (ENNReal.add (ENNReal.finite (correlated NNReal.zero))
    (ENNReal.finite (correlated two))) = ENNReal.one
  rw [correlated, ite_eq_left rfl, correlated, ite_eq_right two_ne_zero]
  show ENNReal.mul halfMass (ENNReal.add (ENNReal.ofRat 2 (by decide +kernel))
    ENNReal.zero) = ENNReal.one
  rw [ENNReal.add_zero, half_ofRat 2 1 _ (by decide +kernel) (by decide +kernel),
    ENNReal.ofRat_one]

theorem correlatedEstimate_markov (input : (Unit × Unit) × (Unit × NNReal)) :
    Measure.IsProbability (correlatedEstimate input) :=
  dirac_probability _ _

theorem zeroOrTwo_markov (input : Unit) : Measure.IsProbability (zeroOrTwo input) :=
  (zeroOrTwo_properlyWeighted input).probability

/-- Case E. The weighted draw is properly weighted, and the correlated estimate
has the right mean `1` once the weight is forgotten, yet `W·e` estimates `0`
rather than `∫ 1 dδ = 1`. -/
theorem value_conditioning_insufficient :
    (∀ input, ProperlyWeighted (unitTarget input) (zeroOrTwo input)) ∧
      (∀ pair, lintegral (zeroOrTwo pair.1) (fun draw =>
        lintegral (correlatedEstimate (pair, draw))
          (fun weight => ENNReal.finite weight)) = ENNReal.one) ∧
      ¬UnbiasedEstimate
        (fun pair : Unit × Unit => lintegral (unitTarget pair.1) (fun _ => ENNReal.one))
        (weightTimes zeroOrTwo (Kernel.IsSFinite.ofMarkov zeroOrTwo_markov)
          correlatedEstimate (Kernel.IsSFinite.ofMarkov correlatedEstimate_markov)) := by
  refine ⟨zeroOrTwo_properlyWeighted, correlated_value_mean, fun unbiased => ?_⟩
  have atUnit := unbiased.mean_eq ((), ())
  have productMeasurable : ENNRealMeasurable (Space.product point weightSpace)
      (fun draw : Unit × NNReal =>
        ENNReal.mul (drawWeight draw) (ENNReal.finite (correlated draw.2))) :=
    ENNRealMeasurable.mul (drawWeight_measurable point)
      (finite_weight_measurable (MeasurableMap.comp correlated_measurable
        (Space.second_measurable point weightSpace)))
  rw [lintegral_weightTimes,
    lintegral_congr _ (fun draw => congrArg (ENNReal.mul (drawWeight draw))
      (correlatedEstimate_mean (((), ()), draw))),
    zeroOrTwo, Kernel.const_apply] at atUnit
  dsimp only at atUnit
  rw [lintegral_fair _ _ _ productMeasurable,
    unitTarget, Kernel.const_apply,
    lintegral_dirac _ _ (ENNRealMeasurable.constant _ _)] at atUnit
  have vanishes : ENNReal.mul halfMass
      (ENNReal.add (ENNReal.mul ENNReal.zero (ENNReal.finite (correlated NNReal.zero)))
        (ENNReal.mul (ENNReal.finite two) (ENNReal.finite (correlated two)))) =
      ENNReal.zero := by
    rw [ENNReal.zero_mul, ENNReal.zero_add, correlated, ite_eq_right two_ne_zero]
    show ENNReal.mul halfMass (ENNReal.mul (ENNReal.finite two) ENNReal.zero) = ENNReal.zero
    rw [ENNReal.mul_zero, ENNReal.mul_zero]
  exact ENNReal.one_ne_zero ((vanishes.symm.trans atUnit).symm)

/-- The unit estimate, which reads the whole draw. -/
@[expose] noncomputable def unitEstimate :
    Kernel (bindEstimateInput point point point) weightSpace :=
  Kernel.deterministic (fun _ => NNReal.one)
    (MeasurableMap.constant _ weightSpace NNReal.one)

theorem unitEstimate_unbiased :
    UnbiasedEstimate (fun _ => ENNReal.one) unitEstimate := by
  refine ⟨fun _ => dirac_probability _ _, fun input => ?_⟩
  show lintegral (Measure.dirac weightSpace NNReal.one) _ = _
  rw [lintegral_dirac _ _ weight_value_measurable]
  rfl

/-- The same weighted draw with an estimate whose mean given `(a, W)` is `b = 1`
passes the estimated bind rule. -/
theorem full_conditioning_sufficient :
    UnbiasedEstimate
      (fun pair : Unit × Unit => lintegral (unitTarget pair.1) (fun _ => ENNReal.one))
      (weightTimes zeroOrTwo
        (Kernel.IsSFinite.ofMarkov fun input => (zeroOrTwo_properlyWeighted input).probability)
        unitEstimate (Kernel.IsSFinite.ofMarkov unitEstimate_unbiased.probability)) :=
  unbiased_density_bind (b := fun _ _ => ENNReal.one) zeroOrTwo_properlyWeighted
    unitEstimate_unbiased

end

end Problib.Inference.Necessity.Density
