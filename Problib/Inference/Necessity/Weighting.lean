module

public import Problib.Inference.Weighting
set_option autoImplicit false

/-! Necessity for calibrated weighting.

Calibration carries the target's scale, so the weaker readings fail. A ratio of
an exact density to an unbiased estimate is not an unbiased weight: splitting
the proposal density `q = 1` into `1/2` or `3/2` with equal probability makes
the reciprocal weight calibrated for `(4/3)μ`, not `μ`
(`reciprocal_estimate_biased`). A law calibrated for `μ` is not calibrated for
`2μ`, although both normalize to the same probability
(`proportional_target_uncalibrated`). The one-draw self-normalized estimate is
biased even when the weighted law is calibrated (`self_normalized_biased`).

Proofs are finite evaluations of Dirac sums. -/

namespace Problib.Inference.Necessity.Weighting

open Problib.Real Problib.Measure

public section

/-- Booleans with every set measurable. -/
abbrev bools : Space Bool := Space.discrete Bool

/-- The one-point space. -/
abbrev point : Space Unit := Space.discrete Unit

/-- One half, as a measure scale. -/
@[expose] noncomputable def halfMass : ENNReal := ENNReal.ofRat (1 / 2) (by decide +kernel)

/-- A rational weight. -/
@[expose] def rationalWeight (value : Rat) (nonnegative : 0 ≤ value) : NNReal :=
  NNReal.ofRat value nonnegative

/-- The fair choice between two points of any space. -/
@[expose] noncomputable def fair {α : Type} (space : Space α) (first second : α) : Measure space :=
  Measure.smul halfMass (Measure.add (Measure.dirac space first) (Measure.dirac space second))

/-- Equal rationals embed as equal scales. -/
theorem ofRat_congr {left right : Rat} (same : left = right) (leftNonnegative : 0 ≤ left)
    (rightNonnegative : 0 ≤ right) :
    ENNReal.ofRat left leftNonnegative = ENNReal.ofRat right rightNonnegative := by
  subst same
  rfl

/-- Half the sum of two rational scales, computed in the rationals. -/
theorem half_sum_ofRat (first second total : Rat) (firstNonnegative : 0 ≤ first)
    (secondNonnegative : 0 ≤ second) (totalNonnegative : 0 ≤ total)
    (same : 1 / 2 * (first + second) = total) :
    ENNReal.mul halfMass
        (ENNReal.add (ENNReal.ofRat first firstNonnegative)
          (ENNReal.ofRat second secondNonnegative)) =
      ENNReal.ofRat total totalNonnegative := by
  rw [halfMass, ← ENNReal.ofRat_add first second firstNonnegative secondNonnegative,
    ← ENNReal.ofRat_mul (1 / 2) (first + second) (by decide +kernel)
      (Rat.add_nonneg firstNonnegative secondNonnegative)]
  exact ofRat_congr same _ _

/-- Half of a rational scale, computed in the rationals. -/
theorem half_ofRat (value result : Rat) (valueNonnegative : 0 ≤ value)
    (resultNonnegative : 0 ≤ result) (same : 1 / 2 * value = result) :
    ENNReal.mul halfMass (ENNReal.ofRat value valueNonnegative) =
      ENNReal.ofRat result resultNonnegative := by
  rw [halfMass, ← ENNReal.ofRat_mul (1 / 2) value (by decide +kernel) valueNonnegative]
  exact ofRat_congr same _ _

/-- Half the sum of two scalings of one value is the value scaled by half their
sum. -/
theorem half_sum_scale (first second value : ENNReal) :
    ENNReal.mul halfMass (ENNReal.add (ENNReal.mul first value) (ENNReal.mul second value)) =
      ENNReal.mul (ENNReal.mul halfMass (ENNReal.add first second)) value := by
  rw [ENNReal.mul_comm first value, ENNReal.mul_comm second value, ← ENNReal.mul_add,
    ENNReal.mul_comm value (ENNReal.add first second), ← ENNReal.mul_assoc]

/-- The fair choice is a probability. -/
theorem fair_probability {α : Type} (space : Space α) (first second : α) :
    Measure.IsProbability (fair space first second) := by
  constructor
  rw [fair, Measure.smul_apply_measurable _ _ space.univ,
    Measure.add_apply_measurable _ _ space.univ, Measure.dirac_apply_univ,
    Measure.dirac_apply_univ, ← ENNReal.ofRat_one]
  exact half_sum_ofRat 1 1 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- One half is not zero. -/
theorem halfMass_ne_zero : halfMass ≠ ENNReal.zero := by
  intro zero
  have bound : ENNReal.le (ENNReal.ofRat (1 / 2) (by decide +kernel))
      (ENNReal.ofRat 0 (by decide +kernel)) := by
    rw [ENNReal.ofRat_zero]
    rw [halfMass] at zero
    rw [zero]
    exact ENNReal.le_refl _
  exact absurd ((ENNReal.ofRat_le_iff _ _ _ _).mp bound) (by decide +kernel)

/-- Integrating against the fair choice averages the two points. -/
theorem lintegral_fair {α : Type} (space : Space α) (first second : α)
    {function : α → ENNReal} (measurable : ENNRealMeasurable space function) :
    lintegral (fair space first second) function =
      ENNReal.mul halfMass (ENNReal.add (function first) (function second)) := by
  rw [fair, lintegral_smul_measure, lintegral_add_measure, lintegral_dirac _ _ measurable,
    lintegral_dirac _ _ measurable]

/-! ### Necessity 2: a reciprocal of an unbiased estimate is biased -/

/-- The estimate of the proposal density `q = 1` that draws `1/2` or `3/2`, each
with probability one half. -/
@[expose] noncomputable def splitEstimate : Measure weightSpace :=
  fair weightSpace (rationalWeight (1 / 2) (by decide +kernel)) (rationalWeight (3 / 2) (by decide +kernel))

/-- The target `δ()` weighed by `p / q̂` with `p = 1`: weight `2` or `2/3`, each
with probability one half. -/
@[expose] noncomputable def reciprocalLaw : Measure (Space.product point weightSpace) :=
  fair (Space.product point weightSpace)
    ((), rationalWeight 2 (by decide +kernel)) ((), rationalWeight (2 / 3) (by decide +kernel))

/-- The split estimate is unbiased for `q = 1`, yet the reciprocal weight is
calibrated for `(4/3)δ()` and so for no other target, `δ()` included.
By hand: `E[q̂] = (1/2)(1/2) + (1/2)(3/2) = 1`, and
`E[1/q̂] = (1/2)·2 + (1/2)·(2/3) = 4/3`. -/
theorem reciprocal_estimate_biased :
    UnbiasedEstimate (fun _ => ENNReal.one) (Kernel.const point splitEstimate) ∧
      Calibrated (Measure.smul (ENNReal.ofRat (4 / 3) (by decide +kernel)) (Measure.dirac point ()))
        reciprocalLaw ∧
      ¬Calibrated (Measure.dirac point ()) reciprocalLaw := by
  have scaled : Calibrated
      (Measure.smul (ENNReal.ofRat (4 / 3) (by decide +kernel)) (Measure.dirac point ()))
      reciprocalLaw := by
    refine calibrated_iff_lintegral.mpr ⟨fair_probability _ _ _, fun function measurable => ?_⟩
    rw [reciprocalLaw, lintegral_fair _ _ _ (weighted_integrand_measurable measurable),
      lintegral_smul_measure, lintegral_dirac _ _ measurable]
    show ENNReal.mul halfMass (ENNReal.add
        (ENNReal.mul (ENNReal.ofRat 2 (by decide +kernel)) (function ()))
        (ENNReal.mul (ENNReal.ofRat (2 / 3) (by decide +kernel)) (function ()))) = _
    rw [half_sum_scale, half_sum_ofRat 2 (2 / 3) (4 / 3) _ _ _ (by decide +kernel)]
  refine ⟨⟨fun _ => fair_probability _ _ _, fun _ => ?_⟩, scaled, fun exact => ?_⟩
  · show lintegral splitEstimate (fun weight => ENNReal.finite weight) = ENNReal.one
    rw [splitEstimate, lintegral_fair _ _ _
      (finite_weight_measurable (MeasurableMap.identity weightSpace)), ← ENNReal.ofRat_one]
    exact half_sum_ofRat (1 / 2) (3 / 2) 1 _ _ _ (by decide +kernel)
  · have atUniv : (Measure.smul (ENNReal.ofRat (4 / 3) (by decide +kernel)) (Measure.dirac point ()))
        Set.univ = (Measure.dirac point ()) Set.univ := by
      rw [calibrated_target_unique scaled exact]
    rw [Measure.smul_apply_measurable _ _ point.univ, Measure.dirac_apply_univ, ENNReal.mul_one,
      ← ENNReal.ofRat_one] at atUniv
    have bound : ENNReal.le (ENNReal.ofRat (4 / 3) (by decide +kernel)) (ENNReal.ofRat 1 (by decide +kernel)) := by
      rw [atUniv]
      exact ENNReal.le_refl _
    exact absurd ((ENNReal.ofRat_le_iff _ _ _ _).mp bound) (by decide +kernel)

/-! ### Necessity 8: calibration carries the scale -/

/-- A law calibrated for a target of positive finite mass is not calibrated for
twice the target. Both targets normalize to the same probability, so a
proportional final measure cannot close a target sequence
(`sequential_targets_sound` asks for equality). -/
theorem proportional_target_uncalibrated {α : Type} {space : Space α}
    {target : Measure space} {weighted : Measure (Space.product space weightSpace)}
    (calibrated : Calibrated target weighted)
    (positive : target Set.univ ≠ ENNReal.zero) (finite : target Set.univ ≠ ENNReal.top) :
    ¬Calibrated (Measure.smul (ENNReal.ofRat 2 (by decide +kernel)) target) weighted := by
  intro doubled
  -- At `univ`: m = 2m with 0 < m < ⊤, which is false.
  have atUniv : target Set.univ =
      (Measure.smul (ENNReal.ofRat 2 (by decide +kernel)) target) Set.univ := by
    rw [← calibrated_target_unique calibrated doubled]
  rw [Measure.smul_apply_measurable _ _ space.univ,
    ofRat_congr (show (2 : Rat) = 1 + 1 by decide +kernel) _ (by decide +kernel),
    ENNReal.ofRat_add 1 1 (by decide +kernel) (by decide +kernel), ENNReal.ofRat_one, ENNReal.mul_comm,
    ENNReal.mul_add, ENNReal.mul_one] at atUniv
  have zero : ENNReal.zero = target Set.univ :=
    ENNReal.add_left_cancel_of_finite (ENNReal.finite_iff_ne_top.mpr finite)
      (by rw [ENNReal.add_zero]; exact atUniv)
  exact positive zero.symm

/-! ### Necessity 9: one-draw self-normalization is biased -/

open Classical in
/-- The one-draw self-normalized estimate `w f(x) / w`: the integrand at the draw,
or zero at weight zero. -/
@[expose] noncomputable def oneDrawSelfNormalized {α : Type} (function : α → ENNReal)
    (draw : α × NNReal) : ENNReal :=
  if draw.2 = NNReal.zero then ENNReal.zero else function draw.1

/-- The indicator of `true`. -/
@[expose] noncomputable def atTrue (value : Bool) : ENNReal := if value then ENNReal.one else ENNReal.zero

/-- The probability target `(1/4)δ_false + (3/4)δ_true`. -/
@[expose] noncomputable def skewed : Measure bools :=
  Measure.add
    (Measure.smul (ENNReal.ofRat (1 / 4) (by decide +kernel)) (Measure.dirac bools false))
    (Measure.smul (ENNReal.ofRat (3 / 4) (by decide +kernel)) (Measure.dirac bools true))

/-- Importance draws for `skewed` from the fair proposal: weight `1/2` at
`false` and `3/2` at `true`. -/
@[expose] noncomputable def skewedLaw : Measure (Space.product bools weightSpace) :=
  fair (Space.product bools weightSpace)
    (false, rationalWeight (1 / 2) (by decide +kernel)) (true, rationalWeight (3 / 2) (by decide +kernel))

/-- The law is calibrated for `skewed`, a probability, whose mass at `true` is
`3/4`. The one-draw self-normalized estimate of the indicator of `true` has mean
`1/2`. By hand: every weight is positive, so the estimate is the indicator at
the draw, and the draw is fair. -/
theorem self_normalized_biased :
    Calibrated skewed skewedLaw ∧
      lintegral skewed atTrue = ENNReal.ofRat (3 / 4) (by decide +kernel) ∧
      lintegral skewedLaw (oneDrawSelfNormalized atTrue) = halfMass := by
  have skewedIntegral : ∀ function : Bool → ENNReal, lintegral skewed function =
      ENNReal.add (ENNReal.mul (ENNReal.ofRat (1 / 4) (by decide +kernel)) (function false))
        (ENNReal.mul (ENNReal.ofRat (3 / 4) (by decide +kernel)) (function true)) := by
    intro function
    have measurable := ENNRealMeasurable.of_measurableMap
      (MeasurableMap.from_discrete ennrealBorel function)
    rw [skewed, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
      lintegral_dirac _ _ measurable, lintegral_dirac _ _ measurable]
  refine ⟨calibrated_iff_lintegral.mpr ⟨fair_probability _ _ _, fun function measurable => ?_⟩,
    ?_, ?_⟩
  · rw [skewedLaw, lintegral_fair _ _ _ (weighted_integrand_measurable measurable),
      skewedIntegral]
    show ENNReal.mul halfMass (ENNReal.add
        (ENNReal.mul (ENNReal.ofRat (1 / 2) (by decide +kernel)) (function false))
        (ENNReal.mul (ENNReal.ofRat (3 / 2) (by decide +kernel)) (function true))) = _
    rw [ENNReal.mul_add, ← ENNReal.mul_assoc, ← ENNReal.mul_assoc,
      half_ofRat (1 / 2) (1 / 4) _ (by decide +kernel) (by decide +kernel),
      half_ofRat (3 / 2) (3 / 4) _ (by decide +kernel) (by decide +kernel)]
  · rw [skewedIntegral]
    show ENNReal.add (ENNReal.mul _ ENNReal.zero) (ENNReal.mul _ ENNReal.one) = _
    rw [ENNReal.mul_zero, ENNReal.mul_one, ENNReal.zero_add]
  · have region := (drawWeight_measurable bools).singleton ENNReal.zero
    have same : oneDrawSelfNormalized atTrue = ennrealPiecewise
        (Set.preimage drawWeight (ennrealSingleton ENNReal.zero)) (fun _ => ENNReal.zero)
        (fun draw => atTrue draw.1) := by
      funext draw
      unfold oneDrawSelfNormalized ennrealPiecewise
      by_cases zero : draw.2 = NNReal.zero
      · have weightZero : Set.preimage drawWeight (ennrealSingleton ENNReal.zero) draw :=
          congrArg ENNReal.finite zero
        rw [if_pos zero, if_pos weightZero]
      · have weightPositive : ¬Set.preimage drawWeight (ennrealSingleton ENNReal.zero) draw :=
          fun weightZero => zero (ENNReal.finite_injective weightZero)
        rw [if_neg zero, if_neg weightPositive]
    have measurable : ENNRealMeasurable (Space.product bools weightSpace)
        (oneDrawSelfNormalized atTrue) := by
      rw [same]
      exact ENNRealMeasurable.piecewise region (ENNRealMeasurable.constant _ _)
        ((ENNRealMeasurable.of_measurableMap
          (MeasurableMap.from_discrete ennrealBorel atTrue)).comp (Space.first_measurable _ _))
    have positive : ∀ (value : Rat) (nonnegative : 0 ≤ value), 0 < value →
        rationalWeight value nonnegative ≠ NNReal.zero := by
      intro value nonnegative less same
      have ordered := (NNReal.ofRat_lt_iff 0 value (by decide +kernel) nonnegative).mpr less
      unfold rationalWeight at same
      rw [NNReal.ofRat_zero, same] at ordered
      exact NNReal.lt_irrefl _ ordered
    rw [skewedLaw, lintegral_fair _ _ _ measurable]
    unfold oneDrawSelfNormalized
    rw [if_neg (positive (1 / 2) _ (by decide +kernel)),
      if_neg (positive (3 / 2) _ (by decide +kernel))]
    show ENNReal.mul halfMass (ENNReal.add ENNReal.zero ENNReal.one) = halfMass
    rw [ENNReal.zero_add, ENNReal.mul_one]

end

end Problib.Inference.Necessity.Weighting
