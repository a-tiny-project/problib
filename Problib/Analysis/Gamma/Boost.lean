module

public import Problib.Analysis.Gamma.Cheng
public import Problib.Analysis.Gamma.Rate
public import Problib.Analysis.Exponential.Tail
public import Problib.Measure.Kernel.Product
public import Problib.Measure.Kernel.Measurable
public import Problib.Measure.Extended.Algebra.Binary
import Problib.Real.Grind

/-! The boost: a Gamma law below shape one from a Gamma law above it.

A draw `x` from the Gamma law at shape `a + 1` and rate one, times
`(1 − u)^{1/a} = exp(log(1 − u)/a)` for a uniform `u`, has the Gamma law at
shape `a` (`boost_law`). Cheng's sampler needs a shape of at least one, so a
sampler below shape one draws at `a + 1` and boosts.

The proof writes the uniform as `t = −log(1 − u)/a`, an increasing
substitution from `(0, 1)` onto `(0, ∞)` (`stretchSubstitution`) under which
`u` has density `a·e^{−at}`. The boosted point is then `x/eᵗ`, and dividing a
rate-one Gamma draw by `eᵗ` gives the Gamma law at rate `eᵗ`
(`law_map_div`). Tonelli swaps the order of integration, and what remains at a
point `y > 0` is `∫_{t>0} eᵗ·e^{−y·eᵗ} dt = e^{−y}/y`, which the substitution
`s = eᵗ` (`expSubstitution`) turns into the exponential tail.
-/

set_option autoImplicit false

open scoped Problib.Real.AC

namespace Problib.Analysis.Gamma.Boost

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real Problib.Analysis.Logarithm

noncomputable section

/-- The boosted point `x·exp(log(1 − u)/a)`. -/
@[expose] public def boost (shape first second : Carrier) : Carrier :=
  mul first (exp (div (logIntegral (sub one second)) shape))

/-- The stretch `−log(1 − u)/a`. -/
@[expose] public def stretch (shape value : Carrier) : Carrier :=
  neg (div (logIntegral (sub one value)) shape)

/-- The stretch's derivative, `1/(a(1 − u))`. -/
@[expose] public def stretchSlope (shape value : Carrier) : Carrier :=
  div one (mul shape (sub one value))

/-- The stretch's inverse, `1 − e^{−at}`. -/
@[expose] public def stretchInverse (shape value : Carrier) : Carrier :=
  sub one (exp (neg (mul shape value)))

private theorem complement_positive {value : Carrier} (member : Ioo zero one value) :
    lt zero (sub one value) := sub_positive_iff.mpr member.2

private theorem hasDerivative_eq' {function : Carrier → Carrier} {point derivative other : Carrier}
    (differentiable : HasDerivative function point derivative) (same : derivative = other) :
    HasDerivative function point other :=
  same ▸ differentiable

private theorem complement_measurable : MeasurableMap borel borel (fun value => sub one value) :=
  measurable_sub (MeasurableMap.constant borel borel one) (MeasurableMap.identity borel)

public theorem boost_measurable (shape : Carrier) :
    MeasurableMap (Space.product borel borel) borel (fun pair => boost shape pair.1 pair.2) :=
  measurable_mul (Space.first_measurable borel borel) (MeasurableMap.comp exp_measurable
    (measurable_div (MeasurableMap.comp log_measurable
      (MeasurableMap.comp complement_measurable (Space.second_measurable borel borel)))
      (MeasurableMap.constant _ borel shape)))

public theorem stretch_measurable (shape : Carrier) : MeasurableMap borel borel (stretch shape) :=
  MeasurableMap.comp neg_measurable (measurable_div
    (MeasurableMap.comp log_measurable complement_measurable) (MeasurableMap.constant borel borel shape))

public theorem stretchSlope_measurable (shape : Carrier) :
    MeasurableMap borel borel (stretchSlope shape) :=
  measurable_div (MeasurableMap.constant borel borel one)
    (measurable_mul (MeasurableMap.constant borel borel shape) complement_measurable)

/-! ### The stretch as a substitution -/

private theorem hasDerivative_stretch {shape : Carrier} (shapePositive : lt zero shape)
    {value : Carrier} (member : Ioo zero one value) :
    HasDerivative (stretch shape) value (stretchSlope shape value) := by
  have complement := complement_positive member
  have inner : HasDerivative (fun point => sub one point) value (sub zero one) :=
    hasDerivative_sub (hasDerivative_const one value) (hasDerivative_identity value)
  have logged := hasDerivative_comp (hasDerivative_log complement) inner
  have scaled := hasDerivative_neg (hasDerivative_smul (inverse shape) logged)
  have same : stretch shape =
      fun point => neg (mul (inverse shape) (logIntegral (sub one point))) := by
    funext point
    unfold stretch
    rw [div_eq_mul_inverse, mul_comm]
  rw [same]
  refine hasDerivative_eq' scaled ?_
  unfold stretchSlope
  have shapeCancel := mul_inverse_cancel (nonzero_of_positive shapePositive)
  have complementCancel := mul_inverse_cancel (nonzero_of_positive complement)
  rw [div_eq_mul_inverse, inverse_mul (nonzero_of_positive shapePositive)
    (nonzero_of_positive complement)]
  real_grind

private theorem stretchSlope_positive {shape : Carrier} (shapePositive : lt zero shape)
    {value : Carrier} (member : Ioo zero one value) : lt zero (stretchSlope shape value) := by
  unfold stretchSlope
  rw [div_eq_mul_inverse, one_mul]
  exact inverse_of_positive_positive (mul_positive shapePositive (complement_positive member))

/-- The stretch is an increasing substitution from `(0, 1)` onto `(0, ∞)`. -/
public def stretchSubstitution {shape : Carrier} (shapePositive : lt zero shape) :
    IncreasingSubstitution (Ioo zero one) (Ioi zero) where
  function := stretch shape
  derivative := stretchSlope shape
  inverse := stretchInverse shape
  functionMeasurable := stretch_measurable shape
  derivativeMeasurable := stretchSlope_measurable shape
  domainConvex := fun _ _ _ firstIn secondIn firstMiddle middleSecond =>
    ⟨lt_of_lt_of_le firstIn.1 firstMiddle, lt_of_le_of_lt middleSecond secondIn.2⟩
  domainOpen := fun value member => by
    have two := ofRat_two_positive
    have half : lt zero (inverse (selection.ofRat 2)) := inverse_of_positive_positive two
    have halfCancel := mul_inverse_cancel (nonzero_of_positive two)
    refine ⟨mul value (inverse (selection.ofRat 2)),
      mul (add one value) (inverse (selection.ofRat 2)), ⟨mul_positive member.1 half, ?_⟩,
      ⟨mul_positive (by have := member.1; have := one_positive; real_grind) half, ?_⟩, ?_, ?_⟩
    · have := mul_lt_mul_positive_right member.2 half; have := member.1; real_grind
    · have := mul_lt_mul_positive_right member.2 half; real_grind
    · have := mul_lt_mul_positive_right member.1 half; real_grind
    · have := mul_lt_mul_positive_right member.2 half; real_grind
  rangeExhaustion := Exhaustion.positive
  maps := fun value member => by
    have complement := complement_positive member
    have below : lt (sub one value) one := by have := member.1; real_grind
    have negative := log_strict _ _ complement below
    rw [log_one] at negative
    have scaled := mul_lt_mul_positive_right negative (inverse_of_positive_positive shapePositive)
    show lt zero (neg (div (logIntegral (sub one value)) shape))
    rw [div_eq_mul_inverse]
    real_grind
  inverseIn := fun value positive => by
    have exponent : lt (neg (mul shape value)) zero := by
      have := mul_positive shapePositive positive; real_grind
    have below := exp_strict exponent
    rw [exp_zero] at below
    have above := exp_positive (neg (mul shape value))
    show lt zero (sub one (exp (neg (mul shape value)))) ∧
      lt (sub one (exp (neg (mul shape value)))) one
    exact ⟨by real_grind, by real_grind⟩
  rightInverse := fun value _ => by
    show neg (div (logIntegral (sub one (sub one (exp (neg (mul shape value)))))) shape) = value
    have back : sub one (sub one (exp (neg (mul shape value)))) = exp (neg (mul shape value)) := by
      real_grind
    rw [back, log_exp, div_eq_mul_inverse]
    have shapeCancel := mul_inverse_cancel (nonzero_of_positive shapePositive)
    real_grind
  increasing := fun first second firstIn secondIn ordered => by
    have reversed : lt (sub one second) (sub one first) := by
      have := ordered; real_grind
    have logged := log_strict _ _ (complement_positive secondIn) reversed
    have scaled := mul_lt_mul_positive_right logged (inverse_of_positive_positive shapePositive)
    show lt (neg (div (logIntegral (sub one first)) shape))
      (neg (div (logIntegral (sub one second)) shape))
    rw [div_eq_mul_inverse, div_eq_mul_inverse]
    real_grind
  differentiable := fun _ member => hasDerivative_stretch shapePositive member
  continuous := fun value member => by
    have complement := complement_positive member
    have denominator : HasDerivative (fun point => mul shape (sub one point)) value
        (mul shape (sub zero one)) :=
      hasDerivative_smul shape (hasDerivative_sub (hasDerivative_const one value)
        (hasDerivative_identity value))
    exact hasDerivative_continuous (hasDerivative_div (hasDerivative_const one value)
      denominator (nonzero_of_positive (mul_positive shapePositive complement)))
  nonnegative := fun _ member => le_of_lt (stretchSlope_positive shapePositive member)

/-- The exponential is an increasing substitution from the line onto `(0, ∞)`. -/
public def expSubstitution : IncreasingSubstitution Set.univ (Ioi zero) where
  function := exp
  derivative := exp
  inverse := logIntegral
  functionMeasurable := exp_measurable
  derivativeMeasurable := exp_measurable
  domainConvex := fun _ _ _ _ _ _ _ => True.intro
  domainOpen := fun value _ =>
    ⟨sub value one, add value one, True.intro, True.intro,
      by have := one_positive; real_grind, by have := one_positive; real_grind⟩
  rangeExhaustion := Exhaustion.positive
  maps := fun value _ => exp_positive value
  inverseIn := fun _ _ => True.intro
  rightInverse := fun value positive => exp_log value positive
  increasing := fun _ _ _ _ ordered => exp_strict ordered
  differentiable := fun value _ => hasDerivative_exp value
  continuous := fun value _ => hasDerivative_continuous (hasDerivative_exp value)
  nonnegative := fun value _ => le_of_lt (exp_positive value)

/-! ### The stretched exponential tail -/

private theorem one_lt_exp_iff (value : Carrier) : lt zero value ↔ lt one (exp value) := by
  constructor
  · intro positive
    have rising := exp_strict positive
    rwa [exp_zero] at rising
  · intro above
    refine Classical.byContradiction fun notPositive => ?_
    have falling := exp_monotone (not_lt_iff_le.mp notPositive)
    rw [exp_zero] at falling
    exact not_le_of_lt above falling

/-- `∫_{t>0} eᵗ·e^{−y·eᵗ} dt = e^{−y}/y` at a positive `y`. -/
public theorem stretched_tail {rate : Carrier} (ratePositive : lt zero rate) :
    lintegral volume (ennrealIndicator (Ioi zero) (fun value =>
        ENNReal.mul (ENNReal.ofReal (exp value)) (Exponential.weight rate (exp value)))) =
      ENNReal.mul (Exponential.weight rate one) (ENNReal.ofReal (inverse rate)) := by
  classical
  have weightMeasurable := Exponential.weight_measurable rate
  have pointwise : ennrealIndicator (Ioi zero) (fun value =>
        ENNReal.mul (ENNReal.ofReal (exp value)) (Exponential.weight rate (exp value))) =
      fun value => ENNReal.mul (ENNReal.ofReal (exp value))
        (ennrealIndicator (Ioi one) (Exponential.weight rate) (exp value)) := by
    funext value
    by_cases positive : Ioi zero value
    · rw [ennrealIndicator_of_mem positive,
        ennrealIndicator_of_mem (show Ioi one (exp value) from (one_lt_exp_iff value).mp positive)]
    · rw [ennrealIndicator_of_not_mem positive,
        ennrealIndicator_of_not_mem (show ¬Ioi one (exp value) from
          fun above => positive ((one_lt_exp_iff value).mpr above)), ENNReal.mul_zero]
  have nested : ennrealIndicator (Ioi zero) (ennrealIndicator (Ioi one) (Exponential.weight rate)) =
      ennrealIndicator (Ioi one) (Exponential.weight rate) := by
    funext value
    by_cases above : Ioi one value
    · have positive : Ioi zero value := lt_trans one_positive above
      rw [ennrealIndicator_of_mem positive]
    · rw [ennrealIndicator_of_not_mem above]
      by_cases positive : Ioi zero value
      · rw [ennrealIndicator_of_mem positive, ennrealIndicator_of_not_mem above]
      · rw [ennrealIndicator_of_not_mem positive]
  have tailMeasurable := ENNRealMeasurable.indicator (measurable_ioi one) weightMeasurable
  rw [pointwise, ← volume.restrict_univ]
  refine (expSubstitution.lintegral_eq tailMeasurable).trans ?_
  rw [← lintegral_indicator _ _ (measurable_ioi zero), nested,
    lintegral_indicator _ _ (measurable_ioi one), Exponential.tail rate one ratePositive]

/-! ### The mixture's density -/

/-- The stretch's density, `a·e^{−at}` on the positive half line. -/
@[expose] public def stretchDensity (shape : Carrier) : Carrier → ENNReal :=
  ennrealIndicator (Ioi zero) (fun value => ENNReal.ofReal (mul shape (exp (neg (mul shape value)))))

public theorem stretchDensity_measurable (shape : Carrier) :
    ENNRealMeasurable borel (stretchDensity shape) :=
  ENNRealMeasurable.indicator (measurable_ioi zero) (ofReal_measurable.comp
    (measurable_mul (MeasurableMap.constant borel borel shape) (MeasurableMap.comp exp_measurable
      (MeasurableMap.comp neg_measurable (measurable_mul (MeasurableMap.constant borel borel shape)
        (MeasurableMap.identity borel))))))

/-- Mixing the Gamma laws at shape `a + 1` and rate `eᵗ` over the stretch's
density gives the Gamma density at shape `a`. -/
public theorem mixture_density {shape : Carrier} (shapePositive : lt zero shape) (value : Carrier) :
    lintegral volume (fun stretched => ENNReal.mul (stretchDensity shape stretched)
        (ENNReal.finite (density (add shape one) (exp stretched) value))) =
      ENNReal.finite (density shape one value) := by
  classical
  by_cases valuePositive : lt zero value
  · let constant := div (mul shape (rpow value shape)) (gamma (add shape one))
    have gammaPositive := gamma_positive shapePositive
    have liftedPositive : lt zero (add shape one) := by have := one_positive; real_grind
    have liftedGamma := gamma_positive liftedPositive
    have constantNonnegative : le zero constant :=
      div_nonnegative (mul_nonnegative shapePositive.1 (rpow_nonnegative value shape))
        (le_of_lt liftedGamma)
    have pointwise : (fun stretched => ENNReal.mul (stretchDensity shape stretched)
          (ENNReal.finite (density (add shape one) (exp stretched) value))) =
        fun stretched => ENNReal.mul (ENNReal.ofReal constant)
          (ennrealIndicator (Ioi zero) (fun point =>
            ENNReal.mul (ENNReal.ofReal (exp point)) (Exponential.weight value (exp point)))
            stretched) := by
      funext stretched
      unfold stretchDensity
      by_cases positive : Ioi zero stretched
      · rw [ennrealIndicator_of_mem positive, ennrealIndicator_of_mem positive,
          density_of_positive _ _ valuePositive]
        change ENNReal.mul _ (ENNReal.ofReal _) =
          ENNReal.mul _ (ENNReal.mul _ (ENNReal.ofReal _))
        have stretchedRate : rpow (exp stretched) (add shape one) =
            exp (mul (add shape one) stretched) := by
          rw [rpow_of_positive (exp_positive stretched), log_exp]
        have shifted : sub (add shape one) one = shape := by real_grind
        have product : mul (exp (neg (mul shape stretched))) (exp (mul (add shape one) stretched)) =
            exp stretched := by
          rw [← exp_add]; congr 1; real_grind
        have stretchedNonnegative := (exp_positive stretched).1
        have weightNonnegative := (exp_positive (neg (mul value (exp stretched)))).1
        have shapeWeight := mul_nonnegative shapePositive.1
          (exp_positive (neg (mul shape stretched))).1
        have densityNonnegative : le zero (div (mul (rpow (exp stretched) (add shape one))
            (mul (rpow value (sub (add shape one) one))
              (exp (neg (mul (exp stretched) value))))) (gamma (add shape one))) :=
          div_nonnegative (mul_nonnegative (rpow_nonnegative _ _)
            (mul_nonnegative (rpow_nonnegative _ _) (exp_positive _).1)) (le_of_lt liftedGamma)
        rw [← ofReal_mul shapeWeight densityNonnegative,
          ← ofReal_mul stretchedNonnegative weightNonnegative,
          ← ofReal_mul constantNonnegative (mul_nonnegative stretchedNonnegative weightNonnegative)]
        congr 1
        rw [stretchedRate, shifted, mul_comm (exp stretched) value]
        simp only [constant, div_eq_mul_inverse]
        real_grind
      · rw [ennrealIndicator_of_not_mem positive, ennrealIndicator_of_not_mem positive,
          ENNReal.zero_mul, ENNReal.mul_zero]
    have tailMeasurable : ENNRealMeasurable borel (ennrealIndicator (Ioi zero) (fun point =>
        ENNReal.mul (ENNReal.ofReal (exp point)) (Exponential.weight value (exp point)))) :=
      ENNRealMeasurable.indicator (measurable_ioi zero)
        ((ofReal_measurable.comp exp_measurable).mul
          ((Exponential.weight_measurable value).comp exp_measurable))
    rw [pointwise, lintegral_smul _ _ tailMeasurable, stretched_tail valuePositive,
      density_of_positive _ _ valuePositive]
    unfold Exponential.weight
    have weightNonnegative := (exp_positive (neg (mul value one))).1
    have inverseNonnegative := le_of_lt (inverse_of_positive_positive valuePositive)
    rw [← ofReal_mul weightNonnegative inverseNonnegative,
      ← ofReal_mul constantNonnegative (mul_nonnegative weightNonnegative inverseNonnegative)]
    change ENNReal.ofReal _ = ENNReal.ofReal _
    congr 1
    have raised : rpow value shape = mul value (rpow value (sub shape one)) := by
      calc rpow value shape = rpow value (add one (sub shape one)) := by rw [add_sub_cancel]
        _ = mul (rpow value one) (rpow value (sub shape one)) := rpow_add valuePositive _ _
        _ = mul value (rpow value (sub shape one)) := by rw [rpow_one valuePositive.1]
    have valueCancel := mul_inverse_cancel (nonzero_of_positive valuePositive)
    have shapeCancel := mul_inverse_cancel (nonzero_of_positive shapePositive)
    have gammaCancel := mul_inverse_cancel (nonzero_of_positive gammaPositive)
    simp only [constant, div_eq_mul_inverse]
    rw [raised, gamma_add_one shapePositive, one_rpow,
      inverse_mul (nonzero_of_positive shapePositive) (nonzero_of_positive gammaPositive),
      mul_comm one value]
    real_grind
  · have nonpositive := not_lt_iff_le.mp valuePositive
    have pointwise : (fun stretched => ENNReal.mul (stretchDensity shape stretched)
          (ENNReal.finite (density (add shape one) (exp stretched) value))) =
        fun _ => ENNReal.zero := by
      funext stretched
      rw [density_of_nonpositive _ _ nonpositive]
      exact ENNReal.mul_zero _
    rw [pointwise, lintegral_zero, density_of_nonpositive _ _ nonpositive]
    rfl

/-! ### The boost -/

/-- The integrand on (Gamma draw, stretch): the stretch's density at `t`, and
whether `x/eᵗ` lies in the region. -/
private def joint (shape : Carrier) (region : Set Carrier) (pair : Carrier × Carrier) : ENNReal :=
  ENNReal.mul (stretchDensity shape pair.2)
    (ennrealIndicator region (fun _ => ENNReal.one) (div pair.1 (exp pair.2)))

private theorem joint_measurable (shape : Carrier) {region : Set Carrier}
    (measurable : borel.Measurable region) :
    ENNRealMeasurable (Space.product borel borel) (joint shape region) :=
  ((stretchDensity_measurable shape).comp (Space.second_measurable borel borel)).mul
    ((ENNRealMeasurable.indicator measurable (ENNRealMeasurable.constant borel ENNReal.one)).comp
      (measurable_div (Space.first_measurable borel borel)
        (MeasurableMap.comp exp_measurable (Space.second_measurable borel borel))))

/-- At a fixed Gamma draw `x`, the uniform's chance that the boosted point lies
in the region is the stretch's chance that `x/eᵗ` does. -/
private theorem section_eq {shape : Carrier} (shapePositive : lt zero shape) {region : Set Carrier}
    (measurable : borel.Measurable region) (first : Carrier) :
    restrictedUnit (Set.preimage (boost shape first) region) =
      lintegral volume (fun stretched => joint shape region (first, stretched)) := by
  classical
  have boostMeasurable : MeasurableMap borel borel (boost shape first) :=
    MeasurableMap.comp (boost_measurable shape)
      (Space.pair_measurable (MeasurableMap.constant borel borel first) (MeasurableMap.identity borel))
  have preimageMeasurable := boostMeasurable measurable
  let integrand : Carrier → ENNReal := fun stretched =>
    ENNReal.mul (ENNReal.ofReal (mul shape (exp (neg (mul shape stretched)))))
      (ennrealIndicator region (fun _ => ENNReal.one) (div first (exp stretched)))
  have integrandMeasurable : ENNRealMeasurable borel integrand :=
    (ofReal_measurable.comp (measurable_mul (MeasurableMap.constant borel borel shape)
      (MeasurableMap.comp exp_measurable (MeasurableMap.comp neg_measurable
        (measurable_mul (MeasurableMap.constant borel borel shape)
          (MeasurableMap.identity borel)))))).mul
      ((ENNRealMeasurable.indicator measurable (ENNRealMeasurable.constant borel ENNReal.one)).comp
        (measurable_div (MeasurableMap.constant borel borel first) exp_measurable))
  have mass : restrictedUnit (Set.preimage (boost shape first) region) =
      lintegral restrictedUnit (ennrealIndicator (Set.preimage (boost shape first) region)
        (fun _ => ENNReal.one)) := by
    rw [lintegral_indicator _ _ preimageMeasurable, lintegral_const, ENNReal.one_mul,
      Measure.restrict_apply_univ]
  have pointwise : (volume.restrict (Ioo zero one)).AEEq
      (ennrealIndicator (Set.preimage (boost shape first) region) (fun _ => ENNReal.one))
      (fun value => ENNReal.mul (ENNReal.ofReal (stretchSlope shape value))
        (integrand (stretch shape value))) :=
    (volume.ae_restrict_mem (measurable_ioo zero one)).mono fun value member => by
      have complement := complement_positive member
      have point : div first (exp (stretch shape value)) = boost shape first value := by
        unfold stretch boost
        rw [div_eq_mul_inverse, exp_neg, inverse_inverse]
      have decay : mul shape (exp (neg (mul shape (stretch shape value)))) =
          mul shape (sub one value) := by
        have exponent : neg (mul shape (stretch shape value)) = logIntegral (sub one value) := by
          unfold stretch
          rw [div_eq_mul_inverse]
          have shapeCancel := mul_inverse_cancel (nonzero_of_positive shapePositive)
          real_grind
        rw [exponent, exp_log _ complement]
      have slopeNonnegative := le_of_lt (stretchSlope_positive shapePositive member)
      have scaledNonnegative := mul_nonnegative shapePositive.1 complement.1
      have cancel : mul (stretchSlope shape value) (mul shape (sub one value)) = one := by
        unfold stretchSlope
        have denominatorCancel :=
          mul_inverse_cancel (nonzero_of_positive (mul_positive shapePositive complement))
        rw [div_eq_mul_inverse]
        real_grind
      show _ = ENNReal.mul _ (ENNReal.mul
        (ENNReal.ofReal (mul shape (exp (neg (mul shape (stretch shape value))))))
        (ennrealIndicator region (fun _ => ENNReal.one) (div first (exp (stretch shape value)))))
      rw [decay, point, ← ENNReal.mul_assoc, ← ofReal_mul slopeNonnegative scaledNonnegative, cancel,
        ENNReal.ofReal_one, ENNReal.one_mul]
      rfl
  rw [mass, Cheng.restrictedUnit_eq]
  refine (lintegral_congr_ae pointwise).trans
    (((stretchSubstitution shapePositive).lintegral_eq integrandMeasurable).trans ?_)
  rw [← lintegral_indicator _ _ (measurable_ioi zero)]
  apply congrArg (lintegral volume)
  funext stretched
  unfold joint stretchDensity
  by_cases positive : Ioi zero stretched
  · rw [ennrealIndicator_of_mem positive, ennrealIndicator_of_mem positive]
  · rw [ennrealIndicator_of_not_mem positive, ennrealIndicator_of_not_mem positive,
      ENNReal.zero_mul]

/-- A Gamma draw at shape `a + 1` and rate one, boosted by an independent
uniform, has the Gamma law at shape `a`. -/
public theorem boost_law {shape : Carrier} (shapePositive : lt zero shape) {region : Set Carrier}
    (measurable : borel.Measurable region) :
    lintegral (law (add shape one) one)
        (fun first => restrictedUnit (Set.preimage (boost shape first) region)) =
      law shape one region := by
  classical
  have liftedPositive : lt zero (add shape one) := by have := one_positive; real_grind
  have lawFinite : Measure.SFinite (law (add shape one) one) :=
    Measure.SFinite.ofFinite (law_isProbability _ _).to_finite
  have jointMeasurable := joint_measurable shape measurable
  have indicatorMeasurable : ENNRealMeasurable borel
      (ennrealIndicator region (fun _ => ENNReal.one)) :=
    ENNRealMeasurable.indicator measurable (ENNRealMeasurable.constant borel ENNReal.one)
  let mixed : Carrier × Carrier → ENNReal := fun pair =>
    ENNReal.mul (stretchDensity shape pair.1)
      (ENNReal.mul (ENNReal.finite (density (add shape one) (exp pair.1) pair.2))
        (ennrealIndicator region (fun _ => ENNReal.one) pair.2))
  have densityMeasurable : ENNRealMeasurable (Space.product borel borel)
      (fun pair : Carrier × Carrier => ENNReal.finite (density (add shape one) (exp pair.1) pair.2)) :=
    density_measurable.comp (Space.pair_measurable
      (Space.pair_measurable (MeasurableMap.constant _ borel (add shape one))
        (MeasurableMap.comp exp_measurable (Space.first_measurable borel borel)))
      (Space.second_measurable borel borel))
  have mixedMeasurable : ENNRealMeasurable (Space.product borel borel) mixed :=
    ((stretchDensity_measurable shape).comp (Space.first_measurable borel borel)).mul
      (densityMeasurable.mul (indicatorMeasurable.comp (Space.second_measurable borel borel)))
  have column (stretched : Carrier) :
      lintegral (law (add shape one) one) (fun first => joint shape region (first, stretched)) =
        lintegral volume (fun value => mixed (stretched, value)) := by
    show lintegral _ (fun first => ENNReal.mul (stretchDensity shape stretched)
      (ennrealIndicator region (fun _ => ENNReal.one) (div first (exp stretched)))) = _
    rw [lintegral_smul _ _ (indicatorMeasurable.comp (div_rate_measurable (exp stretched))),
      ← lintegral_map _ _ (div_rate_measurable (exp stretched)) indicatorMeasurable,
      law_map_div liftedPositive (exp_positive stretched),
      law_integral liftedPositive (exp_positive stretched) indicatorMeasurable,
      ← lintegral_smul _ _ ((density_measurable_slice (add shape one) (exp stretched)).mul
        indicatorMeasurable)]
  have row (value : Carrier) :
      lintegral volume (fun stretched => mixed (stretched, value)) =
        ENNReal.mul (ennrealIndicator region (fun _ => ENNReal.one) value)
          (ENNReal.finite (density shape one value)) := by
    have rearranged : (fun stretched => mixed (stretched, value)) = fun stretched =>
        ENNReal.mul (ennrealIndicator region (fun _ => ENNReal.one) value)
          (ENNReal.mul (stretchDensity shape stretched)
            (ENNReal.finite (density (add shape one) (exp stretched) value))) := by
      funext stretched
      show ENNReal.mul _ (ENNReal.mul _ _) = _
      ac_rfl
    have sliceMeasurable : ENNRealMeasurable borel (fun stretched =>
        ENNReal.mul (stretchDensity shape stretched)
          (ENNReal.finite (density (add shape one) (exp stretched) value))) :=
      (stretchDensity_measurable shape).mul (densityMeasurable.comp (Space.pair_measurable
        (MeasurableMap.identity borel) (MeasurableMap.constant borel borel value)))
    rw [rearranged, lintegral_smul _ _ sliceMeasurable, mixture_density shapePositive]
  calc lintegral (law (add shape one) one)
        (fun first => restrictedUnit (Set.preimage (boost shape first) region))
      = lintegral (law (add shape one) one) (fun first =>
          lintegral volume (fun stretched => joint shape region (first, stretched))) :=
        congrArg (lintegral _) (funext fun first => section_eq shapePositive measurable first)
    _ = lintegral volume (fun stretched =>
          lintegral (law (add shape one) one) (fun first => joint shape region (first, stretched))) := by
        rw [← lintegral_prod _ _ volumeSFinite jointMeasurable]
        exact lintegral_prod_symm _ _ lawFinite volumeSFinite jointMeasurable
    _ = lintegral volume (fun stretched => lintegral volume (fun value => mixed (stretched, value))) :=
        congrArg (lintegral volume) (funext column)
    _ = lintegral volume (fun value => lintegral volume (fun stretched => mixed (stretched, value))) := by
        rw [← lintegral_prod _ _ volumeSFinite mixedMeasurable]
        exact lintegral_prod_symm _ _ volumeSFinite volumeSFinite mixedMeasurable
    _ = lintegral volume (ennrealIndicator region (fun value => ENNReal.finite (density shape one value))) := by
        apply congrArg (lintegral volume)
        funext value
        rw [row]
        by_cases inside : region value
        · rw [ennrealIndicator_of_mem inside, ennrealIndicator_of_mem inside, ENNReal.one_mul]
        · rw [ennrealIndicator_of_not_mem inside, ennrealIndicator_of_not_mem inside,
            ENNReal.zero_mul]
    _ = law shape one region := by
        rw [lintegral_indicator _ _ measurable, law_apply shapePositive one_positive measurable]

/-- The boosted draw divided by a positive rate has the Gamma law at shape `a`
and that rate. -/
public theorem boost_rate_law {shape rate : Carrier} (shapePositive : lt zero shape)
    (ratePositive : lt zero rate) {region : Set Carrier} (measurable : borel.Measurable region) :
    lintegral (law (add shape one) one) (fun first => restrictedUnit
        (Set.preimage (fun second => div (boost shape first second) rate) region)) =
      law shape rate region := by
  rw [← law_map_div shapePositive ratePositive, Measure.map_apply _ _ _ measurable]
  exact boost_law shapePositive (div_rate_measurable rate measurable)

/-- The boosted section's mass is measurable in the Gamma draw. -/
public theorem boost_section_measurable (shape rate : Carrier) {region : Set Carrier}
    (measurable : borel.Measurable region) :
    ENNRealMeasurable borel (fun first => restrictedUnit
      (Set.preimage (fun second => div (boost shape first second) rate) region)) := by
  have pointMeasurable : MeasurableMap (Space.product borel borel) borel
      (fun pair : Carrier × Carrier => div (boost shape pair.1 pair.2) rate) :=
    measurable_div (boost_measurable shape) (MeasurableMap.constant _ borel rate)
  have joint := Kernel.lintegral_measurable_joint (Kernel.const borel restrictedUnit)
    (Kernel.IsSFinite.const borel (Measure.SFinite.ofFinite restrictedUnit_isProbability.to_finite))
    (function := fun first second => ennrealIndicator region (fun _ => ENNReal.one)
      (div (boost shape first second) rate))
    ((ENNRealMeasurable.indicator measurable (ENNRealMeasurable.constant borel ENNReal.one)).comp
      pointMeasurable)
  refine (congrArg (ENNRealMeasurable borel) ?_).mp joint
  funext first
  have sectionMeasurable : borel.Measurable
      (Set.preimage (fun second => div (boost shape first second) rate) region) :=
    (MeasurableMap.comp pointMeasurable (Space.pair_measurable
      (MeasurableMap.constant borel borel first) (MeasurableMap.identity borel))) measurable
  change lintegral restrictedUnit (ennrealIndicator
    (Set.preimage (fun second => div (boost shape first second) rate) region)
    (fun _ => ENNReal.one)) = _
  rw [lintegral_indicator _ _ sectionMeasurable, lintegral_const, ENNReal.one_mul,
    Measure.restrict_apply_univ]

end

end Problib.Analysis.Gamma.Boost
