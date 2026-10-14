module

public import Problib.Analysis.Gamma.Beta
public import Problib.Analysis.Real.FactorialSeries
public import Problib.Analysis.Real.SignedSeries
import Problib.Measure.Real.Arithmetic

/-! The logarithm of Euler's Gamma function.

`lgamma` is `logIntegral ∘ gamma`. Scores and evidence that involve Gamma and
Beta functions are sums of these logarithms, so a model computes them without
forming the Gamma values, which overflow long before their logarithms do.

At a positive shape, `exp_lgamma` returns the Gamma value, and the recurrence
`lgamma (x + 1) = log x + lgamma x` is the logarithm of `gamma_add_one`. Off the
positive ray the composition inherits its convention instead of choosing one:
Euler's integral diverges at every nonpositive shape (`gamma_of_nonpositive`
extends `gamma_zero`), the real projection sends it to zero, and `logIntegral`
is zero off the positive ray, so `lgamma` is zero there.

At the natural shapes, `lgamma (n + 1)` is `log n!` against Poisson's factor
`factorialTerm one n = 1/n!`. `logBeta` is the logarithm of the Beta function
through `beta_eq`, and `logRising a n = lgamma (a + n) - lgamma a` is the
logarithm of the rising factorial `a (a + 1) ⋯ (a + n - 1)`, a finite sum of
logarithms. No derivative is proved here.
-/

set_option autoImplicit false

open scoped Problib.Real.AC

namespace Problib.Analysis

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real.SignedSeries (factorialTerm factorialTerm_zero factorialTerm_succ
  factorialTerm_one_positive partialSum partialSum_zero partialSum_succ)
open Logarithm

noncomputable section

namespace Gamma

/-- Below one, a power shrinks as its exponent grows. -/
private theorem rpow_antitone_exponent {base first second : Carrier} (positive : lt zero base)
    (below : le base one) (included : le first second) :
    le (rpow base second) (rpow base first) := by
  have logNonpositive : le (logIntegral base) zero := by
    have monotone := log_monotone base one positive below
    rwa [log_one] at monotone
  have flipped : le zero (neg (logIntegral base)) := by
    have negated := neg_le_neg_iff.mpr logNonpositive
    rwa [neg_zero] at negated
  have scaled := mul_le_mul_nonnegative_right included flipped
  rw [mul_neg, mul_neg] at scaled
  rw [rpow_of_positive positive, rpow_of_positive positive]
  exact exp_monotone (neg_le_neg_iff.mp scaled)

/-- At a nonpositive shape, the Gamma integrand on the unit interval is at least
the multiple `e⁻¹ x⁻¹`, whose integral diverges. -/
private theorem gammaIntegral_of_nonpositive {shape : Carrier} (nonpositive : le shape zero) :
    gammaIntegral shape = ENNReal.top := by
  have exponentIncluded : le (sub shape one) (sub zero one) := by
    rw [sub_eq_add_neg, sub_eq_add_neg]
    exact add_le_add nonpositive (le_refl _)
  have bound : ENNReal.le (ENNReal.mul (Exponential.weight one one)
      (lintegral (volume.restrict (Ioc zero one))
        (fun value => ENNReal.ofReal (rpow value (sub zero one))))) (gammaIntegral shape) := by
    rw [← lintegral_smul _ _ (ofReal_measurable.comp (rpow_measurable (sub zero one)))]
    refine ENNReal.le_trans (lintegral_mono_ae
      ((volume.ae_restrict_mem (measurable_ioc zero one)).mono (fun value member => ?_)))
      (lintegral_mono_measure (Gamma.weight shape one) _ _ (fun set setMeasurable => ?_))
    · show ENNReal.le (ENNReal.mul (Exponential.weight one one)
        (ENNReal.ofReal (rpow value (sub zero one)))) (Gamma.weight shape one value)
      have exponential : ENNReal.le (Exponential.weight one one) (Exponential.weight one value) := by
        unfold Exponential.weight
        rw [one_mul, one_mul]
        exact ENNReal.ofReal_monotone (exp_monotone (neg_le_neg_iff.mpr member.2))
      unfold Gamma.weight
      rw [ENNReal.mul_comm]
      exact ENNReal.le_trans
        (ENNReal.mul_le_mul_right (ENNReal.ofReal_monotone
          (rpow_antitone_exponent member.1 member.2 exponentIncluded)) _)
        (ENNReal.mul_le_mul_left exponential _)
    · rw [Measure.restrict_apply _ _ setMeasurable, Measure.restrict_apply _ _ setMeasurable]
      exact volume.mono (fun _ member => ⟨member.1, member.2.1⟩)
  have exponentialNonzero : Exponential.weight one one ≠ ENNReal.zero :=
    fun vanishing => (exp_positive _).2 (ENNReal.ofReal_eq_zero_iff.mp vanishing)
  rw [rpow_unit_integral_zero_eq_top, ENNReal.mul_top_of_ne_zero exponentialNonzero] at bound
  exact ENNReal.top_le_iff.mp bound

/-- `1/n! · Γ(n + 1) = 1`, by the recurrence from `Γ(1) = 1`. -/
private theorem factorialTerm_mul_gamma (count : Nat) :
    mul (factorialTerm one count) (gamma (selection.ofRat ((count + 1 : Nat) : Rat))) = one := by
  induction count with
  | zero =>
      rw [factorialTerm_zero, show ((0 + 1 : Nat) : Rat) = 1 from rfl, ofRat_one, gamma_one,
        mul_one]
  | succ count induction =>
      have positive : lt zero (selection.ofRat ((count + 1 : Nat) : Rat)) :=
        ofRat_succ_positive count
      have nonzero : selection.ofRat ((count + 1 : Nat) : Rat) ≠ zero :=
        fun vanishing => positive.2 (by rw [vanishing]; exact le_refl zero)
      have shifted : selection.ofRat ((count + 1 + 1 : Nat) : Rat) =
          add (selection.ofRat ((count + 1 : Nat) : Rat)) one := by
        rw [Rat.natCast_add, ofRat_add, show ((1 : Nat) : Rat) = 1 from rfl, ofRat_one]
      rw [shifted, gamma_add_one positive, factorialTerm_succ, div_eq_mul_inverse, one_mul]
      generalize selection.ofRat ((count + 1 : Nat) : Rat) = natural at nonzero induction ⊢
      calc mul (mul (factorialTerm one count) (inverse natural)) (mul natural (gamma natural))
          = mul (mul (factorialTerm one count) (gamma natural)) (mul (inverse natural) natural) := by
            ac_rfl
        _ = one := by rw [inverse_mul_cancel nonzero, mul_one, induction]

end Gamma

/-- Euler's integral diverges at every nonpositive shape, so its real value is
zero there. -/
public theorem gamma_of_nonpositive {shape : Carrier} (nonpositive : le shape zero) :
    gamma shape = zero := by
  unfold gamma
  rw [Gamma.gammaIntegral_of_nonpositive nonpositive]
  exact ENNReal.toReal_top

/-- `Γ(n + 1) = n!`, against Poisson's factor `factorialTerm one n = 1/n!`. -/
public theorem gamma_nat (count : Nat) :
    gamma (selection.ofRat ((count + 1 : Nat) : Rat)) = inverse (factorialTerm one count) := by
  have nonzero : factorialTerm one count ≠ zero :=
    fun vanishing => (factorialTerm_one_positive count).2 (by rw [vanishing]; exact le_refl zero)
  calc gamma (selection.ofRat ((count + 1 : Nat) : Rat))
      = mul (mul (inverse (factorialTerm one count)) (factorialTerm one count))
          (gamma (selection.ofRat ((count + 1 : Nat) : Rat))) := by
        rw [inverse_mul_cancel nonzero, one_mul]
    _ = inverse (factorialTerm one count) := by
        rw [mul_assoc, Gamma.factorialTerm_mul_gamma count, mul_one]

/-- The logarithm of Euler's Gamma function, `log ∘ Γ`. It is zero off the
positive ray, where `gamma` is zero and `logIntegral` is zero. -/
@[expose] public def lgamma (shape : Carrier) : Carrier := logIntegral (gamma shape)

public theorem lgamma_measurable : MeasurableMap borel borel lgamma :=
  MeasurableMap.comp log_measurable gamma_measurable

public theorem lgamma_of_nonpositive {shape : Carrier} (nonpositive : le shape zero) :
    lgamma shape = zero := by
  unfold lgamma
  rw [gamma_of_nonpositive nonpositive]
  exact log_of_nonpositive zero (le_refl zero)

public theorem exp_lgamma {shape : Carrier} (positive : lt zero shape) :
    exp (lgamma shape) = gamma shape :=
  exp_log _ (gamma_positive positive)

public theorem lgamma_one : lgamma one = zero := by
  unfold lgamma
  rw [gamma_one, log_one]

/-- The recurrence `log Γ(x + 1) = log x + log Γ(x)` at every positive shape. -/
public theorem lgamma_add_one {shape : Carrier} (positive : lt zero shape) :
    lgamma (add shape one) = add (logIntegral shape) (lgamma shape) := by
  unfold lgamma
  rw [gamma_add_one positive, log_mul _ _ positive (gamma_positive positive)]

/-- `log Γ(n + 1) = log n!`, written against Poisson's factor `1/n!`. -/
public theorem lgamma_nat (count : Nat) :
    lgamma (selection.ofRat ((count + 1 : Nat) : Rat)) =
      neg (logIntegral (factorialTerm one count)) := by
  unfold lgamma
  rw [gamma_nat, log_inverse _ (factorialTerm_one_positive count)]

/-- The logarithm of Euler's Beta function, `log Γ(a) + log Γ(b) - log Γ(a + b)`. -/
@[expose] public def logBeta (first second : Carrier) : Carrier :=
  sub (add (lgamma first) (lgamma second)) (lgamma (add first second))

public theorem logBeta_measurable :
    MeasurableMap (Space.product borel borel) borel
      (fun pair : Carrier × Carrier => logBeta pair.1 pair.2) := by
  have first : MeasurableMap (Space.product borel borel) borel
      (Prod.fst : Carrier × Carrier → Carrier) := Space.first_measurable borel borel
  have second : MeasurableMap (Space.product borel borel) borel
      (Prod.snd : Carrier × Carrier → Carrier) := Space.second_measurable borel borel
  unfold logBeta
  intro set measurable
  exact measurable_sub
    (measurable_add (lgamma_measurable.comp first) (lgamma_measurable.comp second))
    (lgamma_measurable.comp (measurable_add first second)) measurable

/-- `exp (logBeta a b) = B(a, b)` at positive shapes, through `beta_eq`. -/
public theorem exp_logBeta {first second : Carrier} (firstPositive : lt zero first)
    (secondPositive : lt zero second) : exp (logBeta first second) = beta first second := by
  unfold logBeta
  rw [sub_eq_add_neg, exp_add, exp_add, exp_neg, exp_lgamma firstPositive,
    exp_lgamma secondPositive, exp_lgamma (add_positive firstPositive secondPositive),
    beta_eq firstPositive secondPositive, div_eq_mul_inverse]

/-- The logarithm of the rising factorial `a (a + 1) ⋯ (a + n - 1)`, as the
difference `log Γ(a + n) - log Γ(a)`. -/
@[expose] public def logRising (shape : Carrier) (count : Nat) : Carrier :=
  sub (lgamma (add shape (selection.ofRat (count : Rat)))) (lgamma shape)

public theorem logRising_measurable (count : Nat) :
    MeasurableMap borel borel (fun shape => logRising shape count) :=
  measurable_sub
    (lgamma_measurable.comp (measurable_add (MeasurableMap.identity borel)
      (MeasurableMap.constant borel borel (selection.ofRat (count : Rat)))))
    lgamma_measurable

public theorem logRising_zero (shape : Carrier) : logRising shape 0 = zero := by
  unfold logRising
  rw [show ((0 : Nat) : Rat) = 0 from rfl, ofRat_zero, add_zero, sub_self]

/-- Each step of the rising factorial adds the logarithm of its next factor. -/
public theorem logRising_succ {shape : Carrier} (positive : lt zero shape) (count : Nat) :
    logRising shape (count + 1) =
      add (logRising shape count) (logIntegral (add shape (selection.ofRat (count : Rat)))) := by
  have stepPositive : lt zero (add shape (selection.ofRat (count : Rat))) := by
    have raised := add_le_add (le_refl shape) (ofRat_nat_nonnegative count)
    rw [add_zero] at raised
    exact lt_of_lt_of_le positive raised
  have shifted : add shape (selection.ofRat ((count + 1 : Nat) : Rat)) =
      add (add shape (selection.ofRat (count : Rat))) one := by
    rw [Rat.natCast_add, ofRat_add, show ((1 : Nat) : Rat) = 1 from rfl, ofRat_one, add_assoc]
  unfold logRising
  rw [shifted, lgamma_add_one stepPositive, sub_eq_add_neg, sub_eq_add_neg]
  ac_rfl

/-- `log (a (a + 1) ⋯ (a + n - 1)) = Σ_{k<n} log (a + k)` at a positive shape. -/
public theorem logRising_eq_partialSum {shape : Carrier} (positive : lt zero shape) (count : Nat) :
    logRising shape count =
      partialSum (fun index => logIntegral (add shape (selection.ofRat (index : Rat)))) count := by
  induction count with
  | zero => rw [logRising_zero, partialSum_zero]
  | succ count induction => rw [logRising_succ positive, partialSum_succ, induction]

end
end Problib.Analysis
