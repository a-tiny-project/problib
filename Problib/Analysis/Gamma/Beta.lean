module

public import Problib.Analysis.Gamma.Function
import Problib.Measure.Kernel.Product

/-! Euler's Beta integral.

`shapePower shape value` is `value^(shape-1)` on the positive half line and zero
elsewhere. `Beta.weight first second budget` multiplies the shape powers of `x`
and `budget - x`, so it vanishes outside `0 < x < budget`. `betaIntegral first
second` is its full-line integral at budget one, `∫₀¹ x^(first-1)
(1-x)^(second-1) dx`, in the extended nonnegative reals.

Scaling `x` by the budget gives the integral at every budget as
`budget^(first+second-1)` times the Beta integral (`Beta.lintegral_weight`).
Tonelli then proves `Γ(first)·Γ(second) = Γ(first+second)·B(first, second)`
(`gammaIntegral_mul_gammaIntegral`). The double integral of `x^(first-1)
(t-x)^(second-1) e^(-t)` over `0 < x < t` is the Gamma product after
translating `t` by `x`. It is the Gamma integral at the summed shape times the
Beta integral after scaling `x` by `t`. The identity holds at every pair of
shapes, whether or not the integrals are finite. It makes the Beta integral
finite and positive at positive shapes and infinite at a zero shape. No
nonlinear change of variables is used. -/

set_option autoImplicit false

open scoped Problib.Real.AC

namespace Problib.Analysis

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

/-- The shape power `value^(shape-1)` on the positive half line, zero
elsewhere. -/
@[expose] public def shapePower (shape : Carrier) : Carrier → ENNReal :=
  ennrealIndicator (Ioi zero) (fun value => ENNReal.ofReal (rpow value (sub shape one)))

public theorem shapePower_measurable (shape : Carrier) :
    ENNRealMeasurable borel (shapePower shape) :=
  ENNRealMeasurable.indicator (measurable_ioi zero)
    (ofReal_measurable.comp (rpow_measurable (sub shape one)))

/-- The shape power is jointly measurable in the shape and the value. -/
public theorem shapePower_jointly_measurable :
    ENNRealMeasurable (Space.product borel borel)
      (fun pair : Carrier × Carrier => shapePower pair.1 pair.2) := by
  have power : ENNRealMeasurable (Space.product borel borel)
      (fun pair : Carrier × Carrier => ENNReal.ofReal (rpow pair.2 (sub pair.1 one))) :=
    ofReal_measurable.comp (MeasurableMap.comp rpow_jointly_measurable
      (Space.pair_measurable (Space.second_measurable borel borel)
        (measurable_sub (Space.first_measurable borel borel)
          (MeasurableMap.constant _ borel one))))
  have equal : (fun pair : Carrier × Carrier => shapePower pair.1 pair.2) =
      ennrealIndicator (Set.preimage (fun pair : Carrier × Carrier => pair.2) (Ioi zero))
        (fun pair => ENNReal.ofReal (rpow pair.2 (sub pair.1 one))) := by
    classical
    funext pair
    unfold shapePower ennrealIndicator ennrealPiecewise Set.preimage
    rfl
  rw [equal]
  exact power.indicator (Space.second_measurable borel borel (measurable_ioi zero))

public theorem shapePower_of_positive (shape : Carrier) {value : Carrier}
    (positive : lt zero value) :
    shapePower shape value = ENNReal.ofReal (rpow value (sub shape one)) := by
  unfold shapePower ennrealIndicator ennrealPiecewise
  exact ite_eq_left positive

public theorem shapePower_of_nonpositive (shape : Carrier) {value : Carrier}
    (nonpositive : le value zero) : shapePower shape value = ENNReal.zero := by
  unfold shapePower ennrealIndicator ennrealPiecewise
  exact ite_eq_right (fun positive : lt zero value => positive.2 nonpositive)

/-- One more unit of shape multiplies the shape power by the value. -/
public theorem shapePower_add_one (shape value : Carrier) :
    shapePower (add shape one) value =
      ENNReal.mul (shapePower shape value) (ENNReal.ofReal value) := by
  classical
  by_cases positive : lt zero value
  · rw [shapePower_of_positive _ positive, shapePower_of_positive _ positive,
      ← ofReal_mul (rpow_nonnegative _ _) positive.1]
    congr 1
    calc rpow value (sub (add shape one) one)
        = rpow value (add (sub shape one) one) := by
          rw [sub_eq_add_neg, sub_eq_add_neg]
          ac_rfl
      _ = mul (rpow value (sub shape one)) value := by
          rw [rpow_add positive, rpow_one positive.1]
  · rw [shapePower_of_nonpositive _ (not_lt_iff_le.mp positive),
      shapePower_of_nonpositive _ (not_lt_iff_le.mp positive), ENNReal.zero_mul]

/-- A positive factor leaves the shape power as its own power. -/
public theorem shapePower_mul {factor : Carrier} (positive : lt zero factor)
    (shape value : Carrier) :
    shapePower shape (mul factor value) =
      ENNReal.mul (ENNReal.ofReal (rpow factor (sub shape one))) (shapePower shape value) := by
  classical
  by_cases valuePositive : lt zero value
  · rw [shapePower_of_positive _ (mul_positive positive valuePositive),
      shapePower_of_positive _ valuePositive, mul_rpow positive.1 valuePositive.1,
      ofReal_mul (rpow_nonnegative _ _) (rpow_nonnegative _ _)]
  · have nonpositive := not_lt_iff_le.mp valuePositive
    have productNonpositive := mul_le_mul_nonnegative_left nonpositive positive.1
    rw [mul_zero] at productNonpositive
    rw [shapePower_of_nonpositive _ productNonpositive, shapePower_of_nonpositive _ nonpositive,
      ENNReal.mul_zero]

namespace Beta

/-- The Beta integrand `x^(first-1) (budget-x)^(second-1)`, zero outside
`0 < x < budget`. -/
@[expose] public def weight (first second budget value : Carrier) : ENNReal :=
  ENNReal.mul (shapePower first value) (shapePower second (sub budget value))

public theorem weight_measurable (first second budget : Carrier) :
    ENNRealMeasurable borel (weight first second budget) :=
  (shapePower_measurable first).mul ((shapePower_measurable second).comp
    (measurable_sub (MeasurableMap.constant borel borel budget) (MeasurableMap.identity borel)))

/-- A budget that is not positive leaves no room for the integrand. -/
private theorem weight_of_nonpositive (first second : Carrier) {budget : Carrier}
    (nonpositive : le budget zero) (value : Carrier) :
    weight first second budget value = ENNReal.zero := by
  classical
  unfold weight
  by_cases positive : lt zero value
  · have gap : le (sub budget value) zero := by
      apply not_lt_iff_le.mp
      intro gapPositive
      have below := lt_of_lt_of_le (sub_positive_iff.mp gapPositive) nonpositive
      exact lt_irrefl zero (lt_trans positive below)
    rw [shapePower_of_nonpositive _ gap, ENNReal.mul_zero]
  · rw [shapePower_of_nonpositive _ (not_lt_iff_le.mp positive), ENNReal.zero_mul]

/-- Scaling the point by the budget factors the budget's powers out of the
unit-budget weight. -/
private theorem weight_scale {budget : Carrier} (positive : lt zero budget)
    (first second value : Carrier) :
    weight first second budget (mul budget value) =
      ENNReal.mul (ENNReal.mul (ENNReal.ofReal (rpow budget (sub first one)))
          (ENNReal.ofReal (rpow budget (sub second one))))
        (weight first second one value) := by
  unfold weight
  have gap : sub budget (mul budget value) = mul budget (sub one value) := by
    rw [mul_sub, mul_one]
  rw [gap, shapePower_mul positive, shapePower_mul positive]
  ac_rfl

private theorem exponent_split (first second : Carrier) :
    sub (add first second) one = add one (add (sub first one) (sub second one)) := by
  rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg]
  calc add (add first second) (neg one)
      = add (add (add first second) (neg one)) zero := (add_zero _).symm
    _ = add (add (add first second) (neg one)) (add one (neg one)) := by rw [add_neg]
    _ = add one (add (add first (neg one)) (add second (neg one))) := by ac_rfl

end Beta

/-- Euler's Beta integral `∫₀¹ x^(first-1) (1-x)^(second-1) dx` in the extended
nonnegative reals. -/
@[expose] public def betaIntegral (first second : Carrier) : ENNReal :=
  lintegral volume (Beta.weight first second one)

namespace Beta

/-- At every budget, the Beta integrand integrates to `budget^(first+second-1)`
times the Beta integral, and to zero at a budget that is not positive. -/
public theorem lintegral_weight (first second budget : Carrier) :
    lintegral volume (weight first second budget) =
      ENNReal.mul (shapePower (add first second) budget) (betaIntegral first second) := by
  classical
  by_cases positive : lt zero budget
  · have scaled := lintegral_volume_scale budget positive (weight_measurable first second budget)
    have pointwise : (fun value => weight first second budget (mul budget value)) =
        (fun value => ENNReal.mul (ENNReal.mul (ENNReal.ofReal (rpow budget (sub first one)))
            (ENNReal.ofReal (rpow budget (sub second one))))
          (weight first second one value)) :=
      funext (weight_scale positive first second)
    rw [pointwise, lintegral_smul _ _ (weight_measurable first second one)] at scaled
    have recovered : lintegral volume (weight first second budget) =
        ENNReal.mul (ENNReal.ofReal budget)
          (ENNReal.mul (ENNReal.mul (ENNReal.ofReal (rpow budget (sub first one)))
              (ENNReal.ofReal (rpow budget (sub second one))))
            (betaIntegral first second)) := by
      unfold betaIntegral
      rw [scaled, ← ENNReal.mul_assoc, ofReal_mul_ofReal_inverse positive, ENNReal.one_mul]
    rw [recovered, shapePower_of_positive _ positive, ← ENNReal.mul_assoc,
      ← ofReal_mul (rpow_nonnegative _ _) (rpow_nonnegative _ _),
      ← ofReal_mul positive.1 (mul_nonnegative (rpow_nonnegative _ _) (rpow_nonnegative _ _)),
      exponent_split, rpow_add positive, rpow_add positive, rpow_one positive.1]
  · have nonpositive := not_lt_iff_le.mp positive
    have vanishing : weight first second budget = fun _ => ENNReal.zero :=
      funext (weight_of_nonpositive first second nonpositive)
    rw [vanishing, lintegral_zero, shapePower_of_nonpositive _ nonpositive, ENNReal.zero_mul]

/-- The Tonelli integrand `x^(first-1) (t-x)^(second-1) e^(-t)` at `(x, t)`. -/
private def tonelli (first second : Carrier) (pair : Carrier × Carrier) : ENNReal :=
  ENNReal.mul (weight first second pair.2 pair.1) (Exponential.weight one pair.2)

private theorem tonelli_measurable (first second : Carrier) :
    ENNRealMeasurable (Space.product borel borel) (tonelli first second) :=
  (((shapePower_measurable first).comp (Space.first_measurable borel borel)).mul
      ((shapePower_measurable second).comp (measurable_sub (Space.second_measurable borel borel)
        (Space.first_measurable borel borel)))).mul
    ((Exponential.weight_measurable one).comp (Space.second_measurable borel borel))

private theorem tail_measurable (second point : Carrier) :
    ENNRealMeasurable borel (fun bound =>
      ENNReal.mul (shapePower second (sub bound point)) (Exponential.weight one bound)) :=
  ((shapePower_measurable second).comp (measurable_sub (MeasurableMap.identity borel)
    (MeasurableMap.constant borel borel point))).mul (Exponential.weight_measurable one)

end Beta

/-- Euler's integral is the full-line integral of the shape power against the
rate-one exponential. -/
public theorem gammaIntegral_eq_lintegral (shape : Carrier) :
    gammaIntegral shape = lintegral volume (fun value =>
      ENNReal.mul (shapePower shape value) (Exponential.weight one value)) := by
  classical
  unfold gammaIntegral
  rw [← lintegral_indicator volume (Ioi zero) (measurable_ioi zero)]
  apply congrArg (lintegral volume)
  funext value
  by_cases positive : lt zero value
  · rw [shapePower_of_positive _ positive]
    unfold ennrealIndicator ennrealPiecewise
    exact ite_eq_left positive
  · rw [shapePower_of_nonpositive _ (not_lt_iff_le.mp positive), ENNReal.zero_mul]
    unfold ennrealIndicator ennrealPiecewise
    exact ite_eq_right positive

private theorem shape_measurable (shape : Carrier) :
    ENNRealMeasurable borel (fun value =>
      ENNReal.mul (shapePower shape value) (Exponential.weight one value)) :=
  (shapePower_measurable shape).mul (Exponential.weight_measurable one)

namespace Beta

/-- Integrating the second coordinate first translates it by the first:
the row is `x^(first-1) e^(-x) Γ(second)`. -/
private theorem tonelli_row (first second point : Carrier) :
    lintegral volume (fun bound => tonelli first second (point, bound)) =
      ENNReal.mul (gammaIntegral second)
        (ENNReal.mul (shapePower first point) (Exponential.weight one point)) := by
  have split : (fun bound => tonelli first second (point, bound)) = (fun bound =>
      ENNReal.mul (shapePower first point)
        (ENNReal.mul (shapePower second (sub bound point)) (Exponential.weight one bound))) := by
    funext bound
    exact ENNReal.mul_assoc _ _ _
  have shifted : (fun value =>
      ENNReal.mul (shapePower second (sub (add point value) point))
        (Exponential.weight one (add point value))) = (fun value =>
      ENNReal.mul (Exponential.weight one point)
        (ENNReal.mul (shapePower second value) (Exponential.weight one value))) := by
    funext value
    rw [add_sub_self, Exponential.weight_add]
    ac_rfl
  rw [split, lintegral_smul _ _ (tail_measurable second point),
    ← lintegral_volume_translate point (tail_measurable second point), shifted,
    lintegral_smul _ _ (shape_measurable second), ← gammaIntegral_eq_lintegral]
  ac_rfl

/-- Integrating the first coordinate first scales it by the second: the column
is `t^(first+second-1) e^(-t) B(first, second)`. -/
private theorem tonelli_column (first second bound : Carrier) :
    lintegral volume (fun point => tonelli first second (point, bound)) =
      ENNReal.mul (betaIntegral first second)
        (ENNReal.mul (shapePower (add first second) bound) (Exponential.weight one bound)) := by
  have swapped : (fun point => tonelli first second (point, bound)) = (fun point =>
      ENNReal.mul (Exponential.weight one bound) (weight first second bound point)) := by
    funext point
    exact ENNReal.mul_comm _ _
  rw [swapped, lintegral_smul _ _ (weight_measurable first second bound), lintegral_weight]
  ac_rfl

end Beta

/-- `Γ(first)·Γ(second) = Γ(first+second)·B(first, second)` at every pair of
shapes, by Tonelli, translation and scaling. It holds whether or not the
integrals are finite. -/
public theorem gammaIntegral_mul_gammaIntegral (first second : Carrier) :
    ENNReal.mul (gammaIntegral first) (gammaIntegral second) =
      ENNReal.mul (gammaIntegral (add first second)) (betaIntegral first second) := by
  calc ENNReal.mul (gammaIntegral first) (gammaIntegral second)
      = ENNReal.mul (gammaIntegral second) (gammaIntegral first) := ENNReal.mul_comm _ _
    _ = lintegral volume (fun point => ENNReal.mul (gammaIntegral second)
          (ENNReal.mul (shapePower first point) (Exponential.weight one point))) := by
        rw [lintegral_smul _ _ (shape_measurable first), ← gammaIntegral_eq_lintegral]
    _ = lintegral volume (fun point =>
          lintegral volume (fun bound => Beta.tonelli first second (point, bound))) :=
        congrArg (lintegral volume) (funext fun point => (Beta.tonelli_row first second point).symm)
    _ = lintegral (Measure.prod volume volume volumeSFinite) (Beta.tonelli first second) :=
        (lintegral_prod _ _ volumeSFinite (Beta.tonelli_measurable first second)).symm
    _ = lintegral volume (fun bound =>
          lintegral volume (fun point => Beta.tonelli first second (point, bound))) :=
        lintegral_prod_symm _ _ volumeSFinite volumeSFinite (Beta.tonelli_measurable first second)
    _ = lintegral volume (fun bound => ENNReal.mul (betaIntegral first second)
          (ENNReal.mul (shapePower (add first second) bound) (Exponential.weight one bound))) :=
        congrArg (lintegral volume) (funext fun bound => Beta.tonelli_column first second bound)
    _ = ENNReal.mul (betaIntegral first second) (gammaIntegral (add first second)) := by
        rw [lintegral_smul _ _ (shape_measurable (add first second)),
          ← gammaIntegral_eq_lintegral]
    _ = ENNReal.mul (gammaIntegral (add first second)) (betaIntegral first second) :=
        ENNReal.mul_comm _ _

/-- The Beta integral is finite at positive shapes. -/
public theorem betaIntegral_finite {first second : Carrier} (firstPositive : lt zero first)
    (secondPositive : lt zero second) : ENNReal.Finite (betaIntegral first second) := by
  have identity := gammaIntegral_mul_gammaIntegral first second
  rw [ENNReal.finite_iff_ne_top]
  intro infinite
  rw [infinite, ENNReal.mul_top_of_ne_zero (ENNReal.zero_lt_iff_ne_zero.mp
    (gammaIntegral_positive (add_positive firstPositive secondPositive)))] at identity
  exact ENNReal.finite_iff_ne_top.mp (ENNReal.mul_finite (gammaIntegral_finite firstPositive)
    (gammaIntegral_finite secondPositive)) identity

/-- The Beta integral is positive at positive shapes. -/
public theorem betaIntegral_positive {first second : Carrier} (firstPositive : lt zero first)
    (secondPositive : lt zero second) :
    ENNReal.lt ENNReal.zero (betaIntegral first second) := by
  apply ENNReal.zero_lt_iff_ne_zero.mpr
  intro vanishing
  have identity := gammaIntegral_mul_gammaIntegral first second
  rw [vanishing, ENNReal.mul_zero] at identity
  rcases ENNReal.mul_eq_zero_iff.mp identity with firstZero | secondZero
  · exact ENNReal.zero_lt_iff_ne_zero.mp (gammaIntegral_positive firstPositive) firstZero
  · exact ENNReal.zero_lt_iff_ne_zero.mp (gammaIntegral_positive secondPositive) secondZero

/-- `B(0, second) = ∞`: the positive-shape premise of `betaIntegral_finite` is
necessary. -/
public theorem betaIntegral_zero_eq_top {second : Carrier} (secondPositive : lt zero second) :
    betaIntegral zero second = ENNReal.top := by
  have identity := gammaIntegral_mul_gammaIntegral zero second
  rw [gammaIntegral_zero_eq_top, ENNReal.top_mul_of_ne_zero (ENNReal.zero_lt_iff_ne_zero.mp
    (gammaIntegral_positive secondPositive)), zero_add] at identity
  apply Classical.byContradiction
  intro finite
  have bounded := ENNReal.mul_finite (gammaIntegral_finite secondPositive)
    (ENNReal.finite_iff_ne_top.mpr finite)
  rw [← identity] at bounded
  exact ENNReal.finite_iff_ne_top.mp bounded rfl

/-- Euler's Beta function on the real carrier, the real value of
`betaIntegral`. -/
@[expose] public def beta (first second : Carrier) : Carrier :=
  ENNReal.toReal (betaIntegral first second)

public theorem ofReal_beta {first second : Carrier} (firstPositive : lt zero first)
    (secondPositive : lt zero second) :
    ENNReal.ofReal (beta first second) = betaIntegral first second :=
  ENNReal.ofReal_toReal (betaIntegral_finite firstPositive secondPositive)

/-- `B(first, second) = Γ(first)·Γ(second)/Γ(first+second)` at positive shapes. -/
public theorem beta_eq {first second : Carrier} (firstPositive : lt zero first)
    (secondPositive : lt zero second) :
    beta first second = div (mul (gamma first) (gamma second)) (gamma (add first second)) := by
  have sumPositive := add_positive firstPositive secondPositive
  have betaNonnegative : le zero (beta first second) := ENNReal.toReal_nonnegative _
  have identity := gammaIntegral_mul_gammaIntegral first second
  rw [← ofReal_gamma firstPositive, ← ofReal_gamma secondPositive, ← ofReal_gamma sumPositive,
    ← ofReal_beta firstPositive secondPositive,
    ← ofReal_mul (gamma_nonnegative _) (gamma_nonnegative _),
    ← ofReal_mul (gamma_nonnegative _) betaNonnegative] at identity
  have projected := congrArg ENNReal.toReal identity
  rw [ENNReal.toReal_ofReal (mul_nonnegative (gamma_nonnegative _) (gamma_nonnegative _)),
    ENNReal.toReal_ofReal (mul_nonnegative (gamma_nonnegative _) betaNonnegative)] at projected
  have nonzero : gamma (add first second) ≠ zero := fun vanishing =>
    (gamma_positive sumPositive).2 (by rw [vanishing]; exact le_refl zero)
  rw [projected, mul_comm (gamma (add first second)), div_eq_mul_inverse, mul_assoc,
    mul_inverse_cancel nonzero, mul_one]

end
end Problib.Analysis
