module

public import Problib.Analysis.Gamma.Density
public import Problib.Analysis.Gaussian.Density
public import Problib.Analysis.Real.FactorialSeries

/-! Gamma conjugacy for Poisson, exponential and Gaussian-precision likelihoods.

Read as a function of a positive latent `λ`, each likelihood has the Gamma form
`scale * λ^power * e^(-tilt λ)`. Against a Gamma prior at `(shape, rate)`, such
a likelihood gives the Gamma posterior at `(shape + power, rate + tilt)`. The
prior density times the likelihood is the evidence times the posterior density.
`density_conjugate` proves this once, pointwise in the latent. The Poisson rate
moves to `(shape + count, rate + 1)`, the exponential rate to
`(shape + 1, rate + observation)`, and the Gaussian precision to
`(shape + 1/2, rate + (observation - mean)^2/2)`.

The evidence is the marginal likelihood. The Gamma normalizer is
`Γ(shape)/rate^shape` (`family_normalizer_eq`), and a likelihood of Gamma form
tilts the weight at `(shape, rate)` into `scale` times the weight at
`(shape + power, rate + tilt)`. The normalizer ratio of `Gamma.family` then
gives `∫ likelihood d(law shape rate) = evidence` (`lintegral_law_likelihood`):
the negative binomial mass for a Poisson count (`poisson_evidence`) and the
Lomax density for an exponential observation (`exponential_evidence`).

The exponential likelihood is the Gamma density at shape one. The Poisson mass
is the formula `rate^count e^(-rate) / count!`. That it sums to one over counts
is not proved here, because the exponential series is not connected to the
integral-defined exponential.
-/

set_option autoImplicit false

open scoped Problib.Real.AC

namespace Problib.Analysis.Gamma

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real.SignedSeries (factorialTerm factorialTerm_factor
  factorialTerm_one_positive)
open Logarithm

noncomputable section

private theorem positive_add_nonnegative {left right : Carrier} (positive : lt zero left)
    (nonnegative : le zero right) : lt zero (add left right) := by
  have raised := add_le_add (le_refl left) nonnegative
  rw [add_zero] at raised
  exact lt_of_lt_of_le positive raised

/-- Multiplying by two cancelled factors leaves a value unchanged. -/
private theorem cancel_pair {value first second : Carrier} (firstNonzero : first ≠ zero)
    (secondNonzero : second ≠ zero) :
    value = mul value (mul (mul first (inverse first)) (mul second (inverse second))) := by
  rw [mul_inverse_cancel firstNonzero, mul_inverse_cancel secondNonzero, mul_one, mul_one]

/-! ### The shared identity -/

/-- The evidence of the likelihood `scale * λ^power * e^(-tilt λ)` under the Gamma
prior at `(shape, rate)`:
`scale * rate^shape * Γ(shape+power) / (Γ(shape) * (rate+tilt)^(shape+power))`. -/
@[expose] public def evidence (shape rate scale power tilt : Carrier) : NNReal :=
  NNReal.ofReal (div (mul scale (mul (rpow rate shape) (gamma (add shape power))))
    (mul (gamma shape) (rpow (add rate tilt) (add shape power))))

/-- Gamma conjugacy for a likelihood of Gamma form, pointwise in the latent. The
prior density at `(shape, rate)` times a likelihood equal to
`scale * λ^power * e^(-tilt λ)` at positive latents is the evidence times the
density at `(shape + power, rate + tilt)`. Only the posterior parameters must be
positive. At a nonpositive latent both sides are zero. -/
public theorem density_conjugate {shape rate scale power tilt : Carrier}
    (scaleNonnegative : le zero scale) (posteriorShape : lt zero (add shape power))
    (posteriorRate : lt zero (add rate tilt)) (latent : Carrier) {likelihood : NNReal}
    (form : lt zero latent → likelihood =
      NNReal.ofReal (mul scale (mul (rpow latent power) (exp (neg (mul tilt latent)))))) :
    NNReal.mul (density shape rate latent) likelihood =
      NNReal.mul (evidence shape rate scale power tilt)
        (density (add shape power) (add rate tilt) latent) := by
  classical
  by_cases positive : lt zero latent
  · have priorNonnegative : le zero (div (mul (rpow rate shape) (mul (rpow latent (sub shape one))
        (exp (neg (mul rate latent))))) (gamma shape)) :=
      div_nonnegative (mul_nonnegative (rpow_nonnegative _ _)
        (mul_nonnegative (rpow_nonnegative _ _) (exp_positive _).1)) (gamma_nonnegative _)
    have likelihoodNonnegative : le zero (mul scale (mul (rpow latent power)
        (exp (neg (mul tilt latent))))) :=
      mul_nonnegative scaleNonnegative (mul_nonnegative (rpow_nonnegative _ _) (exp_positive _).1)
    have evidenceNonnegative : le zero (div (mul scale (mul (rpow rate shape)
        (gamma (add shape power)))) (mul (gamma shape) (rpow (add rate tilt) (add shape power)))) :=
      div_nonnegative (mul_nonnegative scaleNonnegative
          (mul_nonnegative (rpow_nonnegative _ _) (gamma_nonnegative _)))
        (mul_nonnegative (gamma_nonnegative _) (rpow_nonnegative _ _))
    have posteriorNonnegative : le zero (div (mul (rpow (add rate tilt) (add shape power))
        (mul (rpow latent (sub (add shape power) one)) (exp (neg (mul (add rate tilt) latent)))))
        (gamma (add shape power))) :=
      div_nonnegative (mul_nonnegative (rpow_nonnegative _ _)
        (mul_nonnegative (rpow_nonnegative _ _) (exp_positive _).1)) (gamma_nonnegative _)
    rw [form positive, density_of_positive _ _ positive, density_of_positive _ _ positive]
    unfold evidence
    rw [← NNReal.ofReal_mul priorNonnegative likelihoodNonnegative,
      ← NNReal.ofReal_mul evidenceNonnegative posteriorNonnegative]
    congr 1
    have exponent : sub (add shape power) one = add (sub shape one) power := by
      rw [sub_eq_add_neg, sub_eq_add_neg, add_assoc, add_comm power (neg one), ← add_assoc]
    rw [exponent, rpow_add positive, add_mul, neg_add, exp_add]
    simp only [div_eq_mul_inverse]
    rw [inverse_mul_total]
    refine (cancel_pair (nonzero_of_positive (gamma_positive posteriorShape))
      (nonzero_of_positive (rpow_positive posteriorRate (add shape power)))).trans ?_
    ac_rfl
  · have nonpositive := not_lt_iff_le.mp positive
    rw [density_of_nonpositive _ _ nonpositive, density_of_nonpositive _ _ nonpositive,
      NNReal.zero_mul, NNReal.mul_zero]

/-! ### Poisson rate -/

/-- The Poisson mass formula `rate^count e^(-rate) / count!`, as a likelihood of
the rate. -/
@[expose] public def poissonMass (rate : Carrier) (count : Nat) : NNReal :=
  NNReal.ofReal (mul (factorialTerm rate count) (exp (neg rate)))

/-- The Poisson evidence, the negative binomial mass
`rate^shape Γ(shape+count) / (count! Γ(shape) (rate+1)^(shape+count))`. -/
@[expose] public def poissonEvidence (shape rate : Carrier) (count : Nat) : NNReal :=
  evidence shape rate (factorialTerm one count) (selection.ofRat (count : Rat)) one

/-- Poisson conjugacy, pointwise in the rate. A Gamma prior density at
`(shape, rate)` times the Poisson mass of `count` at the latent rate equals the
negative binomial evidence times the Gamma density at
`(shape + count, rate + 1)`. -/
public theorem poisson_conjugate {shape rate : Carrier} (shapePositive : lt zero shape)
    (ratePositive : lt zero rate) (count : Nat) (latent : Carrier) :
    NNReal.mul (density shape rate latent) (poissonMass latent count) =
      NNReal.mul (poissonEvidence shape rate count)
        (density (add shape (selection.ofRat (count : Rat))) (add rate one) latent) :=
  density_conjugate (factorialTerm_one_positive count).1
    (positive_add_nonnegative shapePositive (ofRat_nat_nonnegative count))
    (add_positive ratePositive one_positive) latent (fun positive => by
      unfold poissonMass
      rw [factorialTerm_factor latent count, ← rpow_nat positive.1 count, one_mul, mul_assoc])

/-! ### Exponential rate -/

/-- The exponential evidence, the Lomax density
`shape rate^shape / (rate+observation)^(shape+1)`. -/
@[expose] public def exponentialEvidence (shape rate observation : Carrier) : NNReal :=
  NNReal.ofReal (div (mul shape (rpow rate shape)) (rpow (add rate observation) (add shape one)))

/-- The recurrence `Γ(shape+1) = shape·Γ(shape)` turns the general evidence into
the Lomax density. -/
private theorem exponentialEvidence_eq {shape : Carrier} (positive : lt zero shape)
    (rate observation : Carrier) :
    exponentialEvidence shape rate observation = evidence shape rate one one observation := by
  unfold exponentialEvidence evidence
  congr 1
  rw [gamma_add_one positive, div_eq_mul_inverse, div_eq_mul_inverse, inverse_mul_total, one_mul]
  refine (cancel_pair (nonzero_of_positive (gamma_positive positive)) one_ne_zero).trans ?_
  rw [inverse_one, mul_one, mul_one]
  ac_rfl

/-- Exponential conjugacy, pointwise in the rate. The exponential likelihood is
the Gamma density at shape one. A Gamma prior density at `(shape, rate)` times
the exponential density of a positive observation at the latent rate equals the
Lomax evidence times the Gamma density at `(shape + 1, rate + observation)`. -/
public theorem exponential_conjugate {shape rate : Carrier} (shapePositive : lt zero shape)
    (ratePositive : lt zero rate) {observation : Carrier}
    (observationPositive : lt zero observation)
    (latent : Carrier) :
    NNReal.mul (density shape rate latent) (density one latent observation) =
      NNReal.mul (exponentialEvidence shape rate observation)
        (density (add shape one) (add rate observation) latent) := by
  rw [exponentialEvidence_eq shapePositive]
  exact density_conjugate one_nonnegative (add_positive shapePositive one_positive)
    (add_positive ratePositive observationPositive) latent (fun _ => by
      rw [density_of_positive _ _ observationPositive, sub_self, rpow_zero, one_mul, one_mul,
        gamma_one, div_one, mul_comm latent observation])

/-! ### Evidence as a marginal likelihood -/

/-- At positive shape and rate the Gamma normalizer is `Γ(shape)/rate^shape`. -/
public theorem family_normalizer_eq {shape rate : Carrier} (shapePositive : lt zero shape)
    (ratePositive : lt zero rate) :
    family.normalizer (shape, rate) = ENNReal.ofReal (div (gamma shape) (rpow rate shape)) := by
  have scaled := weight_integral shape ratePositive
  rw [← ofReal_gamma shapePositive] at scaled
  have powerPositive := rpow_positive ratePositive shape
  rw [family_normalizer]
  calc lintegral (volume.restrict (Ioi zero)) (weight shape rate)
      = ENNReal.mul (ENNReal.mul (ENNReal.ofReal (inverse (rpow rate shape)))
          (ENNReal.ofReal (rpow rate shape)))
          (lintegral (volume.restrict (Ioi zero)) (weight shape rate)) := by
        rw [ENNReal.mul_comm (ENNReal.ofReal (inverse _)), ofReal_mul_ofReal_inverse powerPositive,
          ENNReal.one_mul]
    _ = ENNReal.mul (ENNReal.ofReal (inverse (rpow rate shape)))
          (ENNReal.ofReal (gamma shape)) := by
        rw [ENNReal.mul_assoc, scaled]
    _ = ENNReal.ofReal (div (gamma shape) (rpow rate shape)) := by
        rw [← ofReal_mul (inverse_nonnegative powerPositive.1) (gamma_nonnegative shape),
          div_eq_mul_inverse, mul_comm]

/-- A likelihood of Gamma form tilts the line weight at `(shape, rate)` into
`scale` times the line weight at `(shape + power, rate + tilt)`. -/
private theorem lineWeight_tilt {shape rate scale power tilt : Carrier}
    (scaleNonnegative : le zero scale) {likelihood : Carrier → NNReal}
    (form : ∀ latent, lt zero latent → likelihood latent =
      NNReal.ofReal (mul scale (mul (rpow latent power) (exp (neg (mul tilt latent))))))
    (latent : Carrier) :
    ENNReal.mul (lineWeight shape rate latent) (ENNReal.finite (likelihood latent)) =
      ENNReal.mul (ENNReal.ofReal scale) (lineWeight (add shape power) (add rate tilt) latent) := by
  classical
  by_cases positive : lt zero latent
  · have real : mul (mul (rpow latent (sub shape one)) (exp (neg (mul rate latent))))
        (mul scale (mul (rpow latent power) (exp (neg (mul tilt latent))))) =
        mul scale (mul (rpow latent (sub (add shape power) one))
          (exp (neg (mul (add rate tilt) latent)))) := by
      have exponent : sub (add shape power) one = add (sub shape one) power := by
        rw [sub_eq_add_neg, sub_eq_add_neg, add_assoc, add_comm power (neg one), ← add_assoc]
      rw [exponent, rpow_add positive, add_mul, neg_add, exp_add]
      ac_rfl
    have likelihoodNonnegative : le zero (mul scale (mul (rpow latent power)
        (exp (neg (mul tilt latent))))) :=
      mul_nonnegative scaleNonnegative (mul_nonnegative (rpow_nonnegative _ _) (exp_positive _).1)
    unfold lineWeight Exponential.weight
    rw [shapePower_of_positive _ positive, shapePower_of_positive _ positive, form latent positive]
    change ENNReal.mul (ENNReal.mul (ENNReal.ofReal _) (ENNReal.ofReal _)) (ENNReal.ofReal _) = _
    rw [← ofReal_mul (rpow_nonnegative _ _) (exp_positive _).1,
      ← ofReal_mul (mul_nonnegative (rpow_nonnegative _ _) (exp_positive _).1)
        likelihoodNonnegative,
      ← ofReal_mul (rpow_nonnegative _ _) (exp_positive _).1,
      ← ofReal_mul scaleNonnegative (mul_nonnegative (rpow_nonnegative _ _) (exp_positive _).1),
      real]
  · have nonpositive := not_lt_iff_le.mp positive
    unfold lineWeight
    rw [shapePower_of_nonpositive _ nonpositive, shapePower_of_nonpositive _ nonpositive,
      ENNReal.zero_mul, ENNReal.zero_mul, ENNReal.zero_mul, ENNReal.mul_zero]

/-- The evidence is the marginal likelihood. Under the Gamma law at
`(shape, rate)`, a measurable likelihood equal to `scale * λ^power * e^(-tilt λ)`
at positive latents integrates to `evidence shape rate scale power tilt`. -/
public theorem lintegral_law_likelihood {shape rate scale power tilt : Carrier}
    (shapePositive : lt zero shape) (ratePositive : lt zero rate)
    (scaleNonnegative : le zero scale) (posteriorShape : lt zero (add shape power))
    (posteriorRate : lt zero (add rate tilt)) {likelihood : Carrier → NNReal}
    (measurable : ENNRealMeasurable borel (fun latent => ENNReal.finite (likelihood latent)))
    (form : ∀ latent, lt zero latent → likelihood latent =
      NNReal.ofReal (mul scale (mul (rpow latent power) (exp (neg (mul tilt latent)))))) :
    lintegral (law shape rate) (fun latent => ENNReal.finite (likelihood latent)) =
      ENNReal.finite (evidence shape rate scale power tilt) := by
  have ratioPositive : lt zero (div (gamma shape) (rpow rate shape)) :=
    div_positive (gamma_positive shapePositive) (rpow_positive ratePositive shape)
  have cancel : ENNReal.mul (ENNReal.ofReal (inverse (div (gamma shape) (rpow rate shape))))
      (family.normalizer (shape, rate)) = ENNReal.one := by
    rw [family_normalizer_eq shapePositive ratePositive, ENNReal.mul_comm]
    exact ofReal_mul_ofReal_inverse ratioPositive
  have marginal := family.lintegral_law_of_scale (parameter := (shape, rate))
    (updated := (add shape power, add rate tilt)) measurable cancel
    (fun latent => lineWeight_tilt scaleNonnegative form latent)
  have posteriorPower := rpow_positive posteriorRate (add shape power)
  rw [family_normalizer_eq posteriorShape posteriorRate,
    ← ofReal_mul scaleNonnegative (div_nonnegative (gamma_nonnegative _) posteriorPower.1),
    ← ofReal_mul (inverse_nonnegative ratioPositive.1)
      (mul_nonnegative scaleNonnegative (div_nonnegative (gamma_nonnegative _) posteriorPower.1))]
    at marginal
  show lintegral (law shape rate) _ = ENNReal.ofReal _
  rw [show law shape rate = family.law (shape, rate) from rfl, marginal]
  congr 1
  simp only [div_eq_mul_inverse]
  rw [inverse_mul_total, inverse_mul_total, inverse_inverse]
  ac_rfl

/-- The factor `rate^count / count!` is measurable in the rate. -/
public theorem factorialTerm_measurable : (count : Nat) →
    MeasurableMap borel borel (fun radius => factorialTerm radius count)
  | 0 => MeasurableMap.constant _ borel one
  | count + 1 => measurable_div
      (measurable_mul (MeasurableMap.identity borel) (factorialTerm_measurable count))
      (MeasurableMap.constant _ borel _)

/-- The negative binomial mass is the marginal likelihood of a Poisson count
under the Gamma law at `(shape, rate)`. -/
public theorem poisson_evidence {shape rate : Carrier} (shapePositive : lt zero shape)
    (ratePositive : lt zero rate) (count : Nat) :
    lintegral (law shape rate) (fun latent => ENNReal.finite (poissonMass latent count)) =
      ENNReal.finite (poissonEvidence shape rate count) :=
  lintegral_law_likelihood shapePositive ratePositive (factorialTerm_one_positive count).1
    (positive_add_nonnegative shapePositive (ofRat_nat_nonnegative count))
    (add_positive ratePositive one_positive)
    (ofReal_measurable.comp (measurable_mul (factorialTerm_measurable count)
      (MeasurableMap.comp exp_measurable neg_measurable)))
    (fun latent positive => by
      unfold poissonMass
      rw [factorialTerm_factor latent count, ← rpow_nat positive.1 count, one_mul, mul_assoc])

/-- The Lomax density is the marginal likelihood of a positive exponential
observation under the Gamma law at `(shape, rate)`. -/
public theorem exponential_evidence {shape rate : Carrier} (shapePositive : lt zero shape)
    (ratePositive : lt zero rate) {observation : Carrier}
    (observationPositive : lt zero observation) :
    lintegral (law shape rate) (fun latent => ENNReal.finite (density one latent observation)) =
      ENNReal.finite (exponentialEvidence shape rate observation) := by
  rw [exponentialEvidence_eq shapePositive]
  exact lintegral_law_likelihood shapePositive ratePositive one_nonnegative
    (add_positive shapePositive one_positive) (add_positive ratePositive observationPositive)
    (density_measurable.comp (Space.pair_measurable
      (Space.pair_measurable (MeasurableMap.constant borel borel one)
        (MeasurableMap.identity borel))
      (MeasurableMap.constant borel borel observation)))
    (fun _ _ => by
      rw [density_of_positive _ _ observationPositive, sub_self, rpow_zero, one_mul, one_mul,
        gamma_one, div_one, mul_comm _ observation])

/-! ### Gaussian precision -/

/-- The square root of a nonnegative real is its power at one half. -/
private theorem sqrt_toReal {value : Carrier} (nonnegative : le zero value) :
    (sqrt (NNReal.ofReal value)).toReal = rpow value (inverse (selection.ofRat 2)) := by
  classical
  by_cases positive : lt zero value
  · have ofRealPositive : NNReal.lt NNReal.zero (NNReal.ofReal value) := by
      change lt zero (NNReal.toReal (NNReal.ofReal value))
      rw [NNReal.toReal_ofReal nonnegative]
      exact positive
    rw [sqrt_of_positive _ ofRealPositive, NNReal.toReal_ofReal (exp_positive _).1,
      rpow_of_positive positive]
    change exp (div (logIntegral (NNReal.toReal (NNReal.ofReal value))) (add one one)) = _
    rw [NNReal.toReal_ofReal nonnegative, div_eq_mul_inverse, mul_comm, ← one_add_one]
  · have vanishing : value = zero := le_antisymm (not_lt_iff_le.mp positive) nonnegative
    rw [vanishing,
      zero_rpow (nonzero_of_positive (inverse_of_positive_positive ofRat_two_positive)),
      NNReal.ofReal_zero, sqrt_zero]
    rfl

/-- The Gaussian normalizer at variance `1/precision` is the unit normalizer over
`precision^(1/2)`. -/
private theorem normalizer_inverse {precision : Carrier} (positive : lt zero precision) :
    inverse (Gaussian.normalizer (inverse precision)).toReal =
      mul (inverse (Gaussian.normalizer one).toReal)
        (rpow precision (inverse (selection.ofRat 2))) := by
  have scale : le zero (mul (selection.ofRat 2) pi) :=
    (mul_positive ofRat_two_positive pi_positive).1
  have inverseNonnegative := (inverse_of_positive_positive positive).1
  have reciprocal : inverse precision = rpow precision (neg one) := by
    rw [rpow_neg positive, rpow_one positive.1]
  have halfPower : rpow (inverse precision) (inverse (selection.ofRat 2)) =
      inverse (rpow precision (inverse (selection.ofRat 2))) := by
    rw [reciprocal, ← rpow_mul positive.1, neg_mul, one_mul, rpow_neg positive]
  unfold Gaussian.normalizer
  rw [sqrt_toReal (mul_nonnegative scale inverseNonnegative),
    sqrt_toReal (mul_nonnegative scale one_nonnegative), mul_one,
    mul_rpow scale inverseNonnegative, inverse_mul_total, halfPower, inverse_inverse]

/-- The Gaussian likelihood of the precision has the Gamma form with power one
half and tilt half the squared displacement. -/
private theorem precision_form (mean observation : Carrier) {precision : Carrier}
    (positive : lt zero precision) :
    Gaussian.density mean (inverse precision) observation =
      NNReal.ofReal (mul (inverse (Gaussian.normalizer one).toReal)
        (mul (rpow precision (inverse (selection.ofRat 2)))
          (exp (neg (mul (div (mul (sub observation mean) (sub observation mean))
            (selection.ofRat 2)) precision))))) := by
  have exponent : div (mul (sub observation mean) (sub observation mean))
      (mul (selection.ofRat 2) (inverse precision)) =
      mul (div (mul (sub observation mean) (sub observation mean)) (selection.ofRat 2))
        precision := by
    simp only [div_eq_mul_inverse]
    rw [inverse_mul_total, inverse_inverse]
    ac_rfl
  unfold Gaussian.density
  congr 1
  rw [exponent, div_eq_mul_inverse (exp _), normalizer_inverse positive]
  ac_rfl

/-- The Gaussian-precision evidence, the Student-t density
`rate^shape Γ(shape+1/2) / (sqrt(2π) Γ(shape) (rate+(observation-mean)^2/2)^(shape+1/2))`. -/
@[expose] public def precisionEvidence (shape rate mean observation : Carrier) : NNReal :=
  evidence shape rate (inverse (Gaussian.normalizer one).toReal) (inverse (selection.ofRat 2))
    (div (mul (sub observation mean) (sub observation mean)) (selection.ofRat 2))

/-- Gaussian-precision conjugacy, pointwise in the precision. A Gamma prior
density at `(shape, rate)` times the Gaussian density of an observation at a
known mean and variance `1/precision` equals the Student-t evidence times the
Gamma density at `(shape + 1/2, rate + (observation - mean)^2/2)`. -/
public theorem precision_conjugate {shape rate : Carrier} (shapePositive : lt zero shape)
    (ratePositive : lt zero rate) (mean observation latent : Carrier) :
    NNReal.mul (density shape rate latent) (Gaussian.density mean (inverse latent) observation) =
      NNReal.mul (precisionEvidence shape rate mean observation)
        (density (add shape (inverse (selection.ofRat 2)))
          (add rate (div (mul (sub observation mean) (sub observation mean)) (selection.ofRat 2)))
          latent) :=
  density_conjugate (inverse_nonnegative (Gaussian.normalizer one).property)
    (add_positive shapePositive (inverse_of_positive_positive ofRat_two_positive))
    (positive_add_nonnegative ratePositive
      (div_nonnegative (mul_self_nonnegative _) ofRat_two_positive.1)) latent
    (fun positive => precision_form mean observation positive)

end
end Problib.Analysis.Gamma
