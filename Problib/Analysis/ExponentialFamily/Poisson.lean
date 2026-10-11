module

public import Problib.Analysis.ExponentialFamily
public import Problib.Analysis.Gamma.Conjugate
import Problib.Measure.Integral.Density.AlmostEverywhere
import Problib.Measure.Integral.Density.Algebra

/-! The Poisson family and its Gamma conjugate prior.

`poisson` observes a count `k` at a rate `λ`. Its base is `1/k!`, its statistic
is `k`, its natural parameter is `log λ` and its log partition is `λ`, so at a
positive rate the likelihood is the Poisson mass `λ^k e^(-λ)/k!`
(`likelihood_poisson`). The logarithm is meaningful only on the positive half
line, so the rate lives on the reference `volume` restricted to `(0, ∞)`
(`rateReference`).

At evidence `(α - 1, β)` the conjugate weight is `λ^(α-1) e^(-βλ)` on the
positive half line, the unnormalized Gamma density. The conjugate kernel there
is the Gamma law at `(α, β)` for positive `α` and `β` (`conjugate_poisson`).
A batch of counts with sum `S` updates the prior to the Gamma law at
`(α + S, β + N)` (`posterior_poisson_batch`), and one count `k` to
`(α + k, β + 1)` (`posterior_poisson`), the pointwise
`Gamma.poisson_conjugate` lifted to the conditional kernel.

The conjugate kernel is defined at every evidence, so the premises need hold
only after the update. At any evidence `(χ, ν)` with `χ > -1` and `ν > 0` it is
the Gamma law at `(χ + 1, ν)` (`conjugate_poisson_evidence`), and a batch
posterior needs those premises only on the updated evidence
(`posterior_poisson_evidence`). Both premises are necessary: at `ν = 0` or at
`χ = -1` the weight has no normalization (`poisson_zero_rate_not_normalizable`,
`poisson_zero_shape_not_normalizable`). The scale-invariant weight `1/λ` at
`(-1, 0)` fails both, yet one count `k ≥ 1` updates it to the Gamma law at
`(k, 1)` (`posterior_poisson_scaleInvariant`).
-/

set_option autoImplicit false

open scoped Problib.Real.AC

namespace Problib.Analysis.ExponentialFamily

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real.SignedSeries (factorialTerm factorialTerm_factor
  factorialTerm_one_positive)
open Logarithm

noncomputable section

/-- The reference on rates: volume on the positive half line. -/
@[expose] public def rateReference : Measure borel := volume.restrict (Ioi zero)

@[expose] public def rateReferenceSFinite : Measure.SFinite rateReference :=
  volumeSFinite.restrict (measurable_ioi zero)

/-- The Poisson family of counts at a rate. -/
@[expose] public def poisson : ExponentialFamily (Space.discrete Nat) borel 1 where
  base count := NNReal.ofReal (factorialTerm one count)
  statistic count _ := selection.ofRat (count : Rat)
  natural rate _ := logIntegral rate
  logPartition rate := rate
  base_measurable := ENNRealMeasurable.of_measurableMap (MeasurableMap.from_discrete _ _)
  statistic_measurable _ := MeasurableMap.from_discrete borel _
  natural_measurable _ := log_measurable
  logPartition_measurable := MeasurableMap.identity borel

/-- At a positive rate the family's likelihood is the Poisson mass. -/
public theorem likelihood_poisson {rate : Carrier} (positive : lt zero rate) (count : Nat) :
    poisson.likelihood rate count = ENNReal.finite (Gamma.poissonMass rate count) := by
  show ENNReal.mul (ENNReal.ofReal (factorialTerm one count))
      (ENNReal.ofReal (exp (sub (pairing 1 (fun _ => logIntegral rate)
        (fun _ => selection.ofRat (count : Rat))) rate))) =
    ENNReal.ofReal (mul (factorialTerm rate count) (exp (neg rate)))
  rw [pairing_one, sub_eq_add_neg, exp_add, mul_comm (logIntegral rate),
    ← rpow_of_positive positive,
    ← ofReal_mul (factorialTerm_one_positive count).1
      (mul_nonnegative (rpow_nonnegative _ _) (exp_positive _).1),
    rpow_nat positive.1, factorialTerm_factor rate count, mul_assoc]

/-- At positive rates the conjugate weight at evidence `(χ, ν)` is the Gamma
weight at shape `χ₀ + 1` and rate `ν`. -/
private theorem weight_ae_gamma (total : Fin 1 → Carrier) (count : Carrier) :
    rateReference.AEEq (poisson.weight (total, count)) (Gamma.weight (add (total 0) one) count) :=
  (volume.ae_restrict_mem (measurable_ioi zero)).mono (fun latent positive => by
    show ENNReal.ofReal (exp (sub (pairing 1 (fun _ => logIntegral latent) total)
        (mul count latent))) = Gamma.weight (add (total 0) one) count latent
    unfold Gamma.weight Exponential.weight
    rw [pairing_one, sub_eq_add_neg, exp_add, ofReal_mul (exp_positive _).1 (exp_positive _).1,
      rpow_of_positive positive, add_comm (total 0) one, add_sub_self,
      mul_comm (logIntegral latent)])

/-- The total mass of the conjugate weight at `(χ, ν)` is the integral of the
Gamma weight at shape `χ₀ + 1` and rate `ν`. -/
private theorem weight_mass (total : Fin 1 → Carrier) (count : Carrier) :
    rateReference.withDensity (poisson.weight (total, count)) Set.univ =
      lintegral (volume.restrict (Ioi zero)) (Gamma.weight (add (total 0) one) count) := by
  rw [Measure.withDensity_congr_ae (weight_ae_gamma total count),
    Measure.withDensity_apply _ _ (Space.univ _), Measure.restrict_univ]
  rfl

/-- The conjugate kernel of the Poisson family at evidence `(χ, ν)` is the Gamma
law at `(χ₀ + 1, ν)` wherever that shape and rate are positive. -/
public theorem conjugate_poisson_evidence {total : Fin 1 → Carrier} {count : Carrier}
    (shapePositive : lt zero (add (total 0) one)) (ratePositive : lt zero count)
    (fallback : Carrier) :
    poisson.conjugate rateReference rateReferenceSFinite fallback (total, count) =
      Gamma.law (add (total 0) one) count := by
  have scalePositive : lt zero (div (rpow count (add (total 0) one)) (gamma (add (total 0) one))) :=
    div_positive (rpow_positive ratePositive _) (gamma_positive shapePositive)
  have law : Gamma.law (add (total 0) one) count = Measure.smul
      (ENNReal.ofReal (div (rpow count (add (total 0) one)) (gamma (add (total 0) one))))
      (rateReference.withDensity (Gamma.weight (add (total 0) one) count)) := by
    rw [Measure.smul_withDensity _ _ (Gamma.weight_measurable _ count), rateReference,
      ← Measure.withDensity_indicator _ _ (measurable_ioi zero),
      Gamma.law_eq_withDensity shapePositive ratePositive]
    apply congrArg
    funext latent
    unfold ennrealIndicator ennrealPiecewise
    by_cases positive : lt zero latent
    · rw [ite_eq_left (show Ioi zero latent from positive), Gamma.density_product _ count positive]
    · rw [ite_eq_right (show ¬Ioi zero latent from positive),
        Gamma.density_of_nonpositive _ _ (not_lt_iff_le.mp positive)]
      rfl
  have inverseNonzero : ENNReal.ofReal (inverse (div (rpow count (add (total 0) one))
      (gamma (add (total 0) one)))) ≠ ENNReal.zero := by
    intro vanishing
    have unit := ofReal_mul_ofReal_inverse scalePositive
    rw [vanishing, ENNReal.mul_zero] at unit
    exact ENNReal.one_ne_zero unit.symm
  apply conjugate_eq_of_smul _ _ _ _ _ (Gamma.law_isProbability _ _)
    (show ENNReal.Finite (ENNReal.ofReal (inverse (div (rpow count (add (total 0) one))
      (gamma (add (total 0) one))))) from True.intro) inverseNonzero
  rw [Measure.withDensity_congr_ae (weight_ae_gamma total count), law, Measure.smul_smul,
    ENNReal.mul_comm, ofReal_mul_ofReal_inverse scalePositive, Measure.one_smul]

/-- The conjugate kernel of the Poisson family at evidence `(α - 1, β)` is the
Gamma law at `(α, β)`. -/
public theorem conjugate_poisson {shape rate : Carrier} (shapePositive : lt zero shape)
    (ratePositive : lt zero rate) (fallback : Carrier) :
    poisson.conjugate rateReference rateReferenceSFinite fallback (fun _ => sub shape one, rate) =
      Gamma.law shape rate := by
  have general := conjugate_poisson_evidence (total := fun _ => sub shape one)
    (show lt zero (add (sub shape one) one) by rw [sub_add_cancel]; exact shapePositive)
    ratePositive fallback
  rwa [sub_add_cancel] at general

/-- At rate zero the conjugate weight has infinite mass at every positive shape,
so no evidence with a zero count normalizes. -/
public theorem poisson_zero_rate_not_normalizable {total : Fin 1 → Carrier}
    (shapePositive : lt zero (add (total 0) one)) :
    ¬Measure.IsNormalizable (rateReference.withDensity (poisson.weight (total, zero))) := by
  apply Measure.infinite_not_normalizable
  rw [weight_mass]
  exact Gamma.weight_integral_zero_rate shapePositive

/-- At shape zero, the statistic `-1`, the conjugate weight has infinite mass at
every positive rate, so no evidence at that statistic normalizes. -/
public theorem poisson_zero_shape_not_normalizable {count : Carrier}
    (ratePositive : lt zero count) :
    ¬Measure.IsNormalizable
      (rateReference.withDensity (poisson.weight (fun _ => neg one, count))) := by
  apply Measure.infinite_not_normalizable
  have scaled := Gamma.weight_integral zero ratePositive
  rw [rpow_zero, ENNReal.ofReal_one, ENNReal.one_mul, gammaIntegral_zero_eq_top] at scaled
  rw [weight_mass]
  show lintegral (volume.restrict (Ioi zero)) (Gamma.weight (add (neg one) one) count) = _
  rw [add_comm, add_neg]
  exact scaled

private theorem base_ne_zero (count : Nat) : poisson.base count ≠ NNReal.zero := by
  intro vanishing
  have projected := NNReal.toReal_ofReal (factorialTerm_one_positive count).1
  change NNReal.toReal (poisson.base count) = _ at projected
  rw [vanishing] at projected
  exact (factorialTerm_one_positive count).2 (projected ▸ le_refl zero)

/-- Poisson–Gamma conjugacy for a batch. Under the prior at `(α - 1, β)`, the
conditional law of the rate given counts with sum `S` and number `N` is the
Gamma law at `(α + S, β + N)`. -/
public theorem posterior_poisson_batch {shape rate : Carrier} (shapePositive : lt zero shape)
    (ratePositive : lt zero rate) (fallback : Carrier) {count : Nat} (data : Fin count → Nat) :
    Kernel.densityConditional rateReference rateReferenceSFinite
        (poisson.joint (fun _ => sub shape one, rate) count)
        (poisson.joint_measurable _ count) fallback data =
      Gamma.law (add shape ((Evidence.laws.listSum ((List.ofFn data).map poisson.observation)).1 0))
        (add rate (Evidence.laws.listSum ((List.ofFn data).map poisson.observation)).2) := by
  rw [posterior _ _ _ _ _ data (fun index => base_ne_zero (data index))]
  have updated : poisson.update (fun _ => sub shape one, rate) (List.ofFn data) =
      (fun _ => sub (add shape ((Evidence.laws.listSum
        ((List.ofFn data).map poisson.observation)).1 0)) one,
        add rate (Evidence.laws.listSum ((List.ofFn data).map poisson.observation)).2) := by
    refine Prod.ext (funext fun index => ?_) rfl
    show add (sub shape one) ((Evidence.laws.listSum
      ((List.ofFn data).map poisson.observation)).1 index) =
      sub (add shape ((Evidence.laws.listSum ((List.ofFn data).map poisson.observation)).1 0)) one
    rw [Subsingleton.elim index 0, sub_eq_add_neg, sub_eq_add_neg]
    ac_rfl
  rw [updated]
  apply conjugate_poisson
  · have total := listSum_observation_statistic_nonnegative poisson
      (fun count _ => ofRat_nat_nonnegative count) (List.ofFn data) 0
    have raised := add_le_add (le_refl shape) total
    rw [add_zero] at raised
    exact lt_of_lt_of_le shapePositive raised
  · have raised := add_le_add (le_refl rate)
      (listSum_observation_count_nonnegative poisson (List.ofFn data))
    rw [add_zero] at raised
    exact lt_of_lt_of_le ratePositive raised

/-- Poisson–Gamma conjugacy through the general theorem. Under the prior at
`(α - 1, β)`, the conditional law of the rate given one count `k` is the Gamma
law at `(α + k, β + 1)`. -/
public theorem posterior_poisson {shape rate : Carrier} (shapePositive : lt zero shape)
    (ratePositive : lt zero rate) (fallback : Carrier) (data : Fin 1 → Nat) :
    Kernel.densityConditional rateReference rateReferenceSFinite
        (poisson.joint (fun _ => sub shape one, rate) 1)
        (poisson.joint_measurable _ 1) fallback data =
      Gamma.law (add shape (selection.ofRat (data 0 : Rat))) (add rate one) := by
  rw [posterior_poisson_batch shapePositive ratePositive fallback data, List.ofFn_succ,
    List.ofFn_zero]
  show Gamma.law (add shape (add (selection.ofRat (data 0 : Rat)) zero))
      (add rate (add one zero)) = _
  rw [add_zero, add_zero]

/-- Poisson conjugacy under premises on the updated evidence only. Under the
conjugate prior at any evidence `(χ, ν)`, proper or not, the conditional law of
the rate given `N` counts with statistic sum `S` is the Gamma law at
`(χ₀ + S + 1, ν + N)`, wherever that shape and rate are positive. -/
public theorem posterior_poisson_evidence (prior : Evidence 1) (fallback : Carrier)
    {count : Nat} (data : Fin count → Nat)
    (shapePositive : lt zero
      (add (add (prior.1 0) ((Evidence.laws.listSum
        ((List.ofFn data).map poisson.observation)).1 0)) one))
    (ratePositive : lt zero (add prior.2 (selection.ofRat (count : Rat)))) :
    Kernel.densityConditional rateReference rateReferenceSFinite (poisson.joint prior count)
        (poisson.joint_measurable prior count) fallback data =
      Gamma.law
        (add (add (prior.1 0) ((Evidence.laws.listSum
          ((List.ofFn data).map poisson.observation)).1 0)) one)
        (add prior.2 (selection.ofRat (count : Rat))) := by
  have counted : (Evidence.laws.listSum ((List.ofFn data).map poisson.observation)).2 =
      selection.ofRat (count : Rat) := by
    rw [listSum_observation_count, List.length_ofFn]
  rw [posterior _ _ _ _ _ data (fun index => base_ne_zero (data index))]
  show poisson.conjugate rateReference rateReferenceSFinite fallback
      (fun index => add (prior.1 index)
          ((Evidence.laws.listSum ((List.ofFn data).map poisson.observation)).1 index),
        add prior.2 (Evidence.laws.listSum ((List.ofFn data).map poisson.observation)).2) = _
  rw [counted]
  exact conjugate_poisson_evidence shapePositive ratePositive fallback

/-- The scale-invariant prior. The weight `1/λ` at evidence `(-1, 0)` has no
normalization (`poisson_zero_shape_not_normalizable`,
`poisson_zero_rate_not_normalizable`), but one count `k ≥ 1` makes the
posterior the Gamma law at `(k, 1)`. -/
public theorem posterior_poisson_scaleInvariant (fallback : Carrier) (data : Fin 1 → Nat)
    (positive : 0 < data 0) :
    Kernel.densityConditional rateReference rateReferenceSFinite
        (poisson.joint (fun _ => neg one, zero) 1) (poisson.joint_measurable _ 1) fallback data =
      Gamma.law (selection.ofRat (data 0 : Rat)) one := by
  have countPositive : lt zero (selection.ofRat (data 0 : Rat)) := by
    obtain ⟨previous, successor⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp positive)
    rw [successor]
    exact ofRat_succ_positive previous
  have single : (Evidence.laws.listSum ((List.ofFn data).map poisson.observation)).1 0 =
      selection.ofRat (data 0 : Rat) := by
    rw [List.ofFn_succ, List.ofFn_zero]
    exact add_zero _
  have shape : add (add (neg one) (selection.ofRat (data 0 : Rat))) one =
      selection.ofRat (data 0 : Rat) := by
    rw [add_comm (neg one), add_assoc, add_comm (neg one) one, add_neg, add_zero]
  have rate : add zero (selection.ofRat ((1 : Nat) : Rat)) = one := by
    rw [zero_add, show ((1 : Nat) : Rat) = 1 from rfl, ofRat_one]
  have general := posterior_poisson_evidence (fun _ => neg one, zero) fallback data
    (show lt zero
        (add (add (neg one) ((Evidence.laws.listSum
          ((List.ofFn data).map poisson.observation)).1 0)) one) by
      rw [single, shape]
      exact countPositive)
    (show lt zero (add zero (selection.ofRat ((1 : Nat) : Rat))) by
      rw [rate]
      exact one_positive)
  rw [general]
  show Gamma.law
      (add (add (neg one) ((Evidence.laws.listSum
        ((List.ofFn data).map poisson.observation)).1 0)) one)
      (add zero (selection.ofRat ((1 : Nat) : Rat))) = _
  rw [single, shape, rate]

end

end Problib.Analysis.ExponentialFamily
