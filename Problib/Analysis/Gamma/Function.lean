module

public import Problib.Analysis.RealPower.Integral
public import Problib.Measure.Kernel.Measurable
import Problib.Measure.Kernel.Product
import Problib.Measure.Measurability.Real

/-! Euler's Gamma integral.

`gammaIntegral shape` is `∫₀^∞ x^(shape-1) e^(-x) dx` in the extended
nonnegative reals. It is one at shape one, finite and positive at every positive
shape, and infinite at shape zero.

The recurrence `Γ(shape+1) = shape·Γ(shape)` comes from Tonelli. At a positive
point the factor `e^(-x)` is its own tail integral, so `Γ(shape)` is a double
integral over `0 < x ≤ t`. Integrating `x` first gives `∫₀ᵗ x^(shape-1) dx =
t^shape/shape`, and what remains is `Γ(shape+1)/shape`. No integration by parts
or derivative is used. The recurrence makes every natural shape finite, and
comparison above one carries finiteness to every positive shape. `gamma` is the
real value, faithful at positive shapes.
-/

set_option autoImplicit false

open scoped Problib.Real.AC

namespace Problib.Analysis

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind
open Logarithm

noncomputable section

namespace Gamma

/-- The unnormalized Gamma density `x^(shape-1) e^(-rate x)`. It is meant for the
positive half line, where every integral against it is taken. -/
@[expose] public def weight (shape rate value : Carrier) : ENNReal :=
  ENNReal.mul (ENNReal.ofReal (rpow value (sub shape one))) (Exponential.weight rate value)

public theorem weight_measurable (shape rate : Carrier) :
    ENNRealMeasurable borel (weight shape rate) :=
  (ofReal_measurable.comp (rpow_measurable (sub shape one))).mul
    (Exponential.weight_measurable rate)

/-- The weight is jointly measurable in the shape and the value. -/
public theorem weight_jointly_measurable (rate : Carrier) :
    ENNRealMeasurable (Space.product borel borel)
      (fun pair : Carrier × Carrier => weight pair.1 rate pair.2) := by
  unfold weight
  measurability [rpow_jointly_measurable, Exponential.weight_measurable rate]

/-- At a positive point the rate-one exponential is its own closed tail integral
over the positive half line. -/
private theorem exponential_tail {point : Carrier} (positive : lt zero point) :
    Exponential.weight one point =
      lintegral (volume.restrict (Ioi zero))
        (ennrealIndicator (Ici point) (Exponential.weight one)) := by
  rw [lintegral_indicator _ _ (measurable_ici point),
    Measure.restrict_restrict _ _ (measurable_ici point)]
  have same : Set.inter (Ici point) (Ioi zero) = Ici point :=
    Set.ext (fun _ => ⟨fun member => member.1,
      fun member => ⟨member, lt_of_lt_of_le positive member⟩⟩)
  rw [same, Exponential.tail_closed one point one_positive, inverse_one, ENNReal.ofReal_one,
    ENNReal.mul_one]

/-- Below a positive bound, the power integral over the positive half line is
`bound^shape/shape`. -/
private theorem power_below {shape bound : Carrier} (positive : lt zero shape)
    (boundPositive : lt zero bound) :
    lintegral (volume.restrict (Ioi zero))
        (ennrealIndicator (Iic bound) (fun value => ENNReal.ofReal (rpow value (sub shape one)))) =
      ENNReal.ofReal (div (rpow bound shape) shape) := by
  rw [lintegral_indicator _ _ (measurable_iic bound),
    Measure.restrict_restrict _ _ (measurable_iic bound)]
  have same : Set.inter (Iic bound) (Ioi zero) = Ioc zero bound :=
    Set.ext (fun _ => ⟨fun member => ⟨member.2, member.1⟩,
      fun member => ⟨member.2, member.1⟩⟩)
  rw [same, rpow_interval_integral shape bound positive boundPositive]

/-- The Tonelli integrand: the power at the first coordinate, times the rate-one
exponential at the second coordinate when the second is at least the first. -/
private def tonelli (shape : Carrier) (pair : Carrier × Carrier) : ENNReal :=
  ENNReal.mul (ENNReal.ofReal (rpow pair.1 (sub shape one)))
    (ennrealIndicator (fun pair : Carrier × Carrier => le pair.1 pair.2)
      (fun pair => Exponential.weight one pair.2) pair)

private theorem tonelli_measurable (shape : Carrier) :
    ENNRealMeasurable (Space.product borel borel) (tonelli shape) := by
  unfold tonelli
  measurability [rpow_measurable (sub shape one), Exponential.weight_measurable one]

/-- Integrating the second coordinate first recovers the Gamma weight. -/
private theorem tonelli_row (shape : Carrier) {point : Carrier} (positive : lt zero point) :
    lintegral (volume.restrict (Ioi zero)) (fun value => tonelli shape (point, value)) =
      weight shape one point := by
  have same : (fun value => tonelli shape (point, value)) = (fun value =>
      ENNReal.mul (ENNReal.ofReal (rpow point (sub shape one)))
        (ennrealIndicator (Ici point) (Exponential.weight one) value)) := rfl
  rw [same, lintegral_smul _ _ (ENNRealMeasurable.indicator (measurable_ici point)
    (Exponential.weight_measurable one)), ← exponential_tail positive]
  rfl

/-- Integrating the first coordinate first gives the weight at the next shape,
divided by the shape. -/
private theorem tonelli_column {shape bound : Carrier} (positive : lt zero shape)
    (boundPositive : lt zero bound) :
    lintegral (volume.restrict (Ioi zero)) (fun value => tonelli shape (value, bound)) =
      ENNReal.mul (ENNReal.ofReal (inverse shape)) (weight (add shape one) one bound) := by
  have same : (fun value => tonelli shape (value, bound)) = (fun value =>
      ENNReal.mul (Exponential.weight one bound)
        (ennrealIndicator (Iic bound) (fun value => ENNReal.ofReal (rpow value (sub shape one)))
          value)) := by
    funext value
    unfold tonelli
    by_cases below : le value bound
    · rw [ennrealIndicator_of_mem (region := fun pair : Carrier × Carrier => le pair.1 pair.2)
          (point := (value, bound)) below,
        ennrealIndicator_of_mem (region := Iic bound) (point := value) below, ENNReal.mul_comm]
    · rw [ennrealIndicator_of_not_mem (region := fun pair : Carrier × Carrier => le pair.1 pair.2)
          (point := (value, bound)) below,
        ennrealIndicator_of_not_mem (region := Iic bound) (point := value) below, ENNReal.mul_zero,
        ENNReal.mul_zero]
  rw [same, lintegral_smul _ _ (ENNRealMeasurable.indicator (measurable_iic bound)
      (ofReal_measurable.comp (rpow_measurable (sub shape one)))),
    power_below positive boundPositive]
  have exponent : sub (add shape one) one = shape := by
    rw [sub_eq_add_neg, add_assoc, add_neg, add_zero]
  unfold weight
  rw [exponent, div_eq_mul_inverse,
    ofReal_mul (rpow_nonnegative _ _) (inverse_of_positive_positive positive).1]
  ac_rfl

/-- Above one, powers grow with the exponent. -/
private theorem rpow_le_rpow_of_exponent_le {base first second : Carrier} (above : le one base)
    (included : le first second) : le (rpow base first) (rpow base second) := by
  have positive : lt zero base := lt_of_lt_of_le one_positive above
  have logNonnegative : le zero (logIntegral base) := by
    have monotone := log_monotone one base one_positive above
    rwa [log_one] at monotone
  rw [rpow_of_positive positive, rpow_of_positive positive]
  exact exp_monotone (mul_le_mul_nonnegative_right included logNonnegative)

/-- On the nonnegative half line the rate-one exponential is at most one. -/
private theorem exponential_le_one {value : Carrier} (nonnegative : le zero value) :
    ENNReal.le (Exponential.weight one value) ENNReal.one := by
  unfold Exponential.weight
  rw [one_mul, ← ENNReal.ofReal_one]
  apply ENNReal.ofReal_monotone
  have bound := exp_monotone (neg_le_neg_iff.mpr nonnegative)
  rwa [neg_zero, exp_zero] at bound

/-- The rate-one exponential decreases. -/
private theorem exponential_antitone {first second : Carrier} (included : le first second) :
    ENNReal.le (Exponential.weight one second) (Exponential.weight one first) := by
  unfold Exponential.weight
  rw [one_mul, one_mul]
  exact ENNReal.ofReal_monotone (exp_monotone (neg_le_neg_iff.mpr included))

private theorem exponential_ne_zero (value : Carrier) :
    Exponential.weight one value ≠ ENNReal.zero :=
  fun vanishing => (exp_positive _).2 (ENNReal.ofReal_eq_zero_iff.mp vanishing)

end Gamma

/-- Euler's integral `∫₀^∞ x^(shape-1) e^(-x) dx` in the extended nonnegative
reals. -/
@[expose] public def gammaIntegral (shape : Carrier) : ENNReal :=
  lintegral (volume.restrict (Ioi zero)) (Gamma.weight shape one)

/-- Euler's integral is Borel measurable in the shape. -/
public theorem gammaIntegral_measurable : ENNRealMeasurable borel gammaIntegral :=
  Kernel.lintegral_measurable_joint (Kernel.const borel (volume.restrict (Ioi zero)))
    (Kernel.IsSFinite.const borel (volumeSFinite.restrict (measurable_ioi zero)))
    (function := fun shape value => Gamma.weight shape one value)
    (Gamma.weight_jointly_measurable one)

/-- `Γ(1) = 1`: at shape one the integrand is the rate-one exponential. -/
public theorem gammaIntegral_one : gammaIntegral one = ENNReal.one := by
  have same : Gamma.weight one one = Exponential.weight one := by
    funext value
    unfold Gamma.weight
    rw [sub_self, rpow_zero, ENNReal.ofReal_one, ENNReal.one_mul]
  unfold gammaIntegral
  rw [same, Exponential.integral one one_positive, inverse_one, ENNReal.ofReal_one]

/-- The recurrence `Γ(shape+1) = shape·Γ(shape)` at every positive shape, by
Tonelli. It holds whether or not the integrals are finite. -/
public theorem gammaIntegral_add_one {shape : Carrier} (positive : lt zero shape) :
    gammaIntegral (add shape one) = ENNReal.mul (ENNReal.ofReal shape) (gammaIntegral shape) := by
  have rayFinite := volumeSFinite.restrict (measurable_ioi zero)
  have swapped : gammaIntegral shape =
      ENNReal.mul (ENNReal.ofReal (inverse shape)) (gammaIntegral (add shape one)) := by
    calc gammaIntegral shape
        = lintegral (volume.restrict (Ioi zero)) (fun point =>
            lintegral (volume.restrict (Ioi zero))
              (fun value => Gamma.tonelli shape (point, value))) := by
          apply lintegral_congr_ae
          exact (volume.ae_restrict_mem (measurable_ioi zero)).mono
            (fun point member => (Gamma.tonelli_row shape member).symm)
      _ = lintegral (Measure.prod (volume.restrict (Ioi zero)) (volume.restrict (Ioi zero))
            rayFinite) (Gamma.tonelli shape) :=
          (lintegral_prod _ _ rayFinite (Gamma.tonelli_measurable shape)).symm
      _ = lintegral (volume.restrict (Ioi zero)) (fun bound =>
            lintegral (volume.restrict (Ioi zero))
              (fun value => Gamma.tonelli shape (value, bound))) :=
          lintegral_prod_symm _ _ rayFinite rayFinite (Gamma.tonelli_measurable shape)
      _ = lintegral (volume.restrict (Ioi zero)) (fun bound =>
            ENNReal.mul (ENNReal.ofReal (inverse shape))
              (Gamma.weight (add shape one) one bound)) := by
          apply lintegral_congr_ae
          exact (volume.ae_restrict_mem (measurable_ioi zero)).mono
            (fun bound member => Gamma.tonelli_column positive member)
      _ = ENNReal.mul (ENNReal.ofReal (inverse shape)) (gammaIntegral (add shape one)) :=
          lintegral_smul _ _ (Gamma.weight_measurable _ _)
  rw [swapped, ← ENNReal.mul_assoc, ofReal_mul_ofReal_inverse positive, ENNReal.one_mul]

/-- The recurrence from `Γ(1) = 1` makes every natural shape finite. -/
private theorem gammaIntegral_succ_finite (count : Nat) :
    ENNReal.Finite (gammaIntegral (selection.ofRat ((count + 1 : Nat) : Rat))) := by
  induction count with
  | zero =>
      rw [show ((0 + 1 : Nat) : Rat) = 1 from rfl, ofRat_one, gammaIntegral_one]
      exact True.intro
  | succ count finite =>
      have positive : lt zero (selection.ofRat ((count + 1 : Nat) : Rat)) :=
        ofRat_succ_positive count
      rw [Rat.natCast_add, ofRat_add, show ((1 : Nat) : Rat) = 1 from rfl, ofRat_one,
        gammaIntegral_add_one positive]
      exact ENNReal.mul_finite (ENNReal.ofReal_finite _) finite

/-- Below one the exponential is at most one, and above one a larger shape gives a
larger power. -/
private theorem gammaIntegral_le {shape larger : Carrier} (included : le shape larger) :
    ENNReal.le (gammaIntegral shape)
      (ENNReal.add (lintegral (volume.restrict (Ioc zero one))
          (fun value => ENNReal.ofReal (rpow value (sub shape one))))
        (gammaIntegral larger)) := by
  have powerMeasurable : ENNRealMeasurable borel
      (fun value => ENNReal.ofReal (rpow value (sub shape one))) :=
    ofReal_measurable.comp (rpow_measurable (sub shape one))
  have exponentIncluded : le (sub shape one) (sub larger one) := by
    rw [sub_eq_add_neg, sub_eq_add_neg]
    exact add_le_add included (le_refl _)
  have pointwise : (volume.restrict (Ioi zero)).AE (fun value =>
      ENNReal.le (Gamma.weight shape one value)
        (ENNReal.add (ennrealIndicator (Iic one)
            (fun value => ENNReal.ofReal (rpow value (sub shape one))) value)
          (Gamma.weight larger one value))) := by
    refine (volume.ae_restrict_mem (measurable_ioi zero)).mono (fun value positive => ?_)
    by_cases below : le value one
    · rw [ennrealIndicator_of_mem (region := Iic one) (point := value) below]
      have bounded : ENNReal.le (Gamma.weight shape one value)
          (ENNReal.ofReal (rpow value (sub shape one))) := by
        have scaled := ENNReal.mul_le_mul_left (Gamma.exponential_le_one positive.1)
          (ENNReal.ofReal (rpow value (sub shape one)))
        rwa [ENNReal.mul_one] at scaled
      have raised := ENNReal.add_le_add_left (ENNReal.zero_le (Gamma.weight larger one value))
        (ENNReal.ofReal (rpow value (sub shape one)))
      rw [ENNReal.add_zero] at raised
      exact ENNReal.le_trans bounded raised
    · rw [ennrealIndicator_of_not_mem (region := Iic one) (point := value) below, ENNReal.zero_add]
      exact ENNReal.mul_le_mul_right (ENNReal.ofReal_monotone
        (Gamma.rpow_le_rpow_of_exponent_le (not_le_iff_lt.mp below).1 exponentIncluded)) _
  have split : lintegral (volume.restrict (Ioi zero)) (fun value =>
      ENNReal.add (ennrealIndicator (Iic one)
          (fun value => ENNReal.ofReal (rpow value (sub shape one))) value)
        (Gamma.weight larger one value)) =
      ENNReal.add (lintegral (volume.restrict (Ioc zero one))
          (fun value => ENNReal.ofReal (rpow value (sub shape one))))
        (gammaIntegral larger) := by
    rw [lintegral_add _ (ENNRealMeasurable.indicator (measurable_iic one) powerMeasurable)
        (Gamma.weight_measurable larger one),
      lintegral_indicator _ _ (measurable_iic one),
      Measure.restrict_restrict _ _ (measurable_iic one)]
    have same : Set.inter (Iic one) (Ioi zero) = Ioc zero one :=
      Set.ext (fun _ => ⟨fun member => ⟨member.2, member.1⟩,
        fun member => ⟨member.2, member.1⟩⟩)
    rw [same]
    rfl
  rw [← split]
  exact lintegral_mono_ae pointwise

/-- On the unit interval the exponential is at least its value at one. -/
private theorem gammaIntegral_ge (shape : Carrier) :
    ENNReal.le (ENNReal.mul (Exponential.weight one one)
        (lintegral (volume.restrict (Ioc zero one))
          (fun value => ENNReal.ofReal (rpow value (sub shape one)))))
      (gammaIntegral shape) := by
  rw [← lintegral_smul _ _ (ofReal_measurable.comp (rpow_measurable (sub shape one)))]
  refine ENNReal.le_trans (lintegral_mono_ae
    ((volume.ae_restrict_mem (measurable_ioc zero one)).mono (fun value member => ?_)))
    (lintegral_mono_measure (Gamma.weight shape one) _ _ (fun set setMeasurable => ?_))
  · show ENNReal.le (ENNReal.mul (Exponential.weight one one)
      (ENNReal.ofReal (rpow value (sub shape one)))) (Gamma.weight shape one value)
    unfold Gamma.weight
    rw [ENNReal.mul_comm]
    exact ENNReal.mul_le_mul_left (Gamma.exponential_antitone member.2) _
  · rw [Measure.restrict_apply _ _ setMeasurable, Measure.restrict_apply _ _ setMeasurable]
    exact volume.mono (fun _ member => ⟨member.1, member.2.1⟩)

/-- Euler's integral is finite at every positive shape. -/
public theorem gammaIntegral_finite {shape : Carrier} (positive : lt zero shape) :
    ENNReal.Finite (gammaIntegral shape) := by
  rcases exists_nat_strict_upper shape with ⟨count, below⟩
  cases count with
  | zero =>
      rw [show ((0 : Nat) : Rat) = 0 from rfl, ofRat_zero] at below
      exact False.elim (lt_irrefl zero (lt_trans positive below))
  | succ count =>
      apply ENNReal.finite_of_le (gammaIntegral_le below.1)
      rw [rpow_unit_integral shape positive]
      exact ENNReal.add_finite (ENNReal.ofReal_finite _) (gammaIntegral_succ_finite count)

/-- Euler's integral is positive at every positive shape. -/
public theorem gammaIntegral_positive {shape : Carrier} (positive : lt zero shape) :
    ENNReal.lt ENNReal.zero (gammaIntegral shape) := by
  have bound := gammaIntegral_ge shape
  rw [rpow_unit_integral shape positive] at bound
  apply ENNReal.zero_lt_iff_ne_zero.mpr
  intro vanishing
  rw [vanishing] at bound
  rcases ENNReal.mul_eq_zero_iff.mp (ENNReal.le_antisymm bound (ENNReal.zero_le _)) with
    weightZero | inverseZero
  · exact Gamma.exponential_ne_zero one weightZero
  · exact (inverse_of_positive_positive positive).2 (ENNReal.ofReal_eq_zero_iff.mp inverseZero)

/-- `Γ(0) = ∞`: the integrand near zero is at least a multiple of `1/x`. -/
public theorem gammaIntegral_zero_eq_top : gammaIntegral zero = ENNReal.top := by
  have bound := gammaIntegral_ge zero
  rw [rpow_unit_integral_zero_eq_top,
    ENNReal.mul_top_of_ne_zero (Gamma.exponential_ne_zero one)] at bound
  exact ENNReal.top_le_iff.mp bound

/-- Euler's Gamma function on the real carrier, the real value of
`gammaIntegral`. It is faithful at positive shapes and zero at shape zero. -/
@[expose] public def gamma (shape : Carrier) : Carrier := ENNReal.toReal (gammaIntegral shape)

public theorem gamma_measurable : MeasurableMap borel borel gamma :=
  MeasurableMap.comp toReal_measurable gammaIntegral_measurable.measurableMap

public theorem gamma_nonnegative (shape : Carrier) : le zero (gamma shape) :=
  ENNReal.toReal_nonnegative _

public theorem ofReal_gamma {shape : Carrier} (positive : lt zero shape) :
    ENNReal.ofReal (gamma shape) = gammaIntegral shape :=
  ENNReal.ofReal_toReal (gammaIntegral_finite positive)

public theorem gamma_positive {shape : Carrier} (positive : lt zero shape) :
    lt zero (gamma shape) := by
  have integralPositive := gammaIntegral_positive positive
  rw [← ofReal_gamma positive, ← ENNReal.ofReal_zero] at integralPositive
  exact (ENNReal.ofReal_lt_ofReal_iff (le_refl zero) (gamma_nonnegative shape)).mp
    integralPositive

public theorem gamma_one : gamma one = one := by
  unfold gamma
  rw [gammaIntegral_one]
  exact ENNReal.toReal_one

public theorem gamma_add_one {shape : Carrier} (positive : lt zero shape) :
    gamma (add shape one) = mul shape (gamma shape) := by
  have value : gammaIntegral (add shape one) = ENNReal.ofReal (mul shape (gamma shape)) := by
    rw [gammaIntegral_add_one positive, ofReal_mul positive.1 (gamma_nonnegative shape),
      ofReal_gamma positive]
  show ENNReal.toReal (gammaIntegral (add shape one)) = _
  rw [value, ENNReal.toReal_ofReal (mul_nonnegative positive.1 (gamma_nonnegative shape))]

/-- The real projection sends the divergent integral at shape zero to zero. -/
public theorem gamma_zero : gamma zero = zero := by
  unfold gamma
  rw [gammaIntegral_zero_eq_top]
  exact ENNReal.toReal_top

end
end Problib.Analysis
