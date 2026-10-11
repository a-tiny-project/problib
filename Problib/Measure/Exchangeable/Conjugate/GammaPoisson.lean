module

public import Problib.Measure.Exchangeable.Keyed
public import Problib.Analysis.Count.Poisson
public import Problib.Measure.StandardBorel.Real
public import Problib.Analysis.Gamma.Logarithm
import Problib.Real.Grind

set_option autoImplicit false

/-!
# The Gamma–Poisson urn

Counts are Poisson at an unknown rate, and the rate is Gamma at `(shape, rate)`.
The urn keeps the Gamma parameters as its statistic: a count `k` moves them to
`(shape + k, rate + 1)`, and the next count's predictive is the negative
binomial mass `Gamma.poissonEvidence`.

The local latent draws the rate from the Gamma law at the statistic and scores a
count by its Poisson mass (`local`). Its step is Problib's pointwise
`poisson_conjugate` under the two Gamma densities (`step`). The likelihood is the
Poisson law's mass at the count (`likelihood_eq_law`), and the predictive is the
Gamma mixture of that law (`predictive_eq_lintegral`, from `poisson_evidence`).
-/

namespace Problib.Measure.Exchangeable.GammaPoisson

open Problib.Real Problib.Measure.Real Problib.Real.Construction.Dedekind
open Problib.Analysis Problib.Analysis.Logarithm

public section

noncomputable section

/-- A count as a real. -/
@[expose] def count (k : Nat) : Carrier := selection.ofRat (k : Rat)

/-- The statistic after one count: `(shape + k, rate + 1)`. -/
@[expose] def incorporate (s : Carrier × Carrier) (k : Nat) : Carrier × Carrier :=
  (add s.1 (count k), add s.2 one)

/-- The predictive of a count: the negative binomial mass at `(shape, rate)`. -/
@[expose] def predictive (s : Carrier × Carrier) (k : Nat) : ENNReal :=
  ENNReal.finite (Gamma.poissonEvidence s.1 s.2 k)

theorem incorporate_measurable :
    MeasurableMap (Space.product (Space.product borel borel) (Space.discrete Nat))
      (Space.product borel borel) fun pair => incorporate pair.1 pair.2 := by
  have atCount : MeasurableMap (Space.product (Space.discrete Nat) (Space.product borel borel))
      (Space.product borel borel) fun pair => incorporate pair.2 pair.1 :=
    MeasurableMap.uncurry_of_countable_first id (fun _ _ equal => equal)
      (function := fun k s => incorporate s k) fun k =>
        Space.pair_measurable
          (measurable_add (Space.first_measurable borel borel)
            (MeasurableMap.constant _ borel (count k)))
          (measurable_add (Space.second_measurable borel borel)
            (MeasurableMap.constant _ borel one))
  intro set measurable
  exact MeasurableMap.comp atCount (Space.swap_measurable _ _) measurable

/-- At a fixed count the negative binomial mass is measurable in the Gamma
parameters. -/
theorem predictive_count_measurable (k : Nat) :
    ENNRealMeasurable (Space.product borel borel) fun s : Carrier × Carrier => predictive s k := by
  have shape : MeasurableMap (Space.product borel borel) borel fun s : Carrier × Carrier => s.1 :=
    Space.first_measurable borel borel
  have rate : MeasurableMap (Space.product borel borel) borel fun s : Carrier × Carrier => s.2 :=
    Space.second_measurable borel borel
  have shifted : MeasurableMap (Space.product borel borel) borel
      fun s : Carrier × Carrier => add s.1 (count k) :=
    measurable_add shape (MeasurableMap.constant _ borel (count k))
  have real : MeasurableMap (Space.product borel borel) borel fun s : Carrier × Carrier =>
      div (mul (Problib.Analysis.Real.SignedSeries.factorialTerm one k)
          (mul (rpow s.2 s.1) (gamma (add s.1 (count k)))))
        (mul (gamma s.1) (rpow (add s.2 one) (add s.1 (count k)))) :=
    measurable_div
      (measurable_mul (MeasurableMap.constant _ borel _)
        (measurable_mul (MeasurableMap.comp rpow_jointly_measurable (Space.pair_measurable rate shape))
          (MeasurableMap.comp gamma_measurable shifted)))
      (measurable_mul (MeasurableMap.comp gamma_measurable shape)
        (MeasurableMap.comp rpow_jointly_measurable
          (Space.pair_measurable (measurable_add rate (MeasurableMap.constant _ borel one)) shifted)))
  exact ofReal_measurable.comp real

theorem predictive_measurable :
    ENNRealMeasurable (Space.product (Space.product borel borel) (Space.discrete Nat))
      fun pair => predictive pair.1 pair.2 := by
  have atCount : MeasurableMap (Space.product (Space.discrete Nat) (Space.product borel borel))
      ennrealBorel fun pair => predictive pair.2 pair.1 :=
    MeasurableMap.uncurry_of_countable_first id (fun _ _ equal => equal)
      (function := fun k s => predictive s k) fun k => (predictive_count_measurable k).measurableMap
  exact ENNRealMeasurable.comp (ENNRealMeasurable.of_measurableMap atCount)
    (before := fun pair : (Carrier × Carrier) × Nat => (pair.2, pair.1))
    (Space.swap_measurable _ _)

end

end

end Problib.Measure.Exchangeable.GammaPoisson

namespace Problib.Measure.Exchangeable

open Problib.Real Problib.Measure.Real Problib.Real.Construction.Dedekind
open Problib.Analysis Problib.Analysis.Logarithm

public section

noncomputable section

/-- The Gamma–Poisson urn from the prior `(shape, rate)`. -/
@[expose] def gammaPoissonUrn (shape rate : Carrier) : Urn.{0, 0} (Space.discrete Nat) where
  Stat := Carrier × Carrier
  statSpace := Space.product borel borel
  init := (shape, rate)
  incorporate := GammaPoisson.incorporate
  predictive := GammaPoisson.predictive
  incorporate_measurable := GammaPoisson.incorporate_measurable
  predictive_measurable := GammaPoisson.predictive_measurable

namespace GammaPoisson

/-- Positive Gamma parameters. -/
@[expose] def Valid (s : Carrier × Carrier) : Prop := lt zero s.1 ∧ lt zero s.2

theorem valid_incorporate {s : Carrier × Carrier} (k : Nat) (valid : Valid s) :
    Valid (incorporate s k) := by
  have raised := add_le_add (le_refl s.1) (ofRat_nat_nonnegative k)
  rw [add_zero] at raised
  exact ⟨lt_of_lt_of_le valid.1 raised, add_positive valid.2 one_positive⟩

/-- The Poisson mass of a count at a rate. -/
@[expose] def likelihood (k : Nat) (rate : Carrier) : ENNReal :=
  ENNReal.finite (Gamma.poissonMass rate k)

theorem likelihood_measurable (k : Nat) : ENNRealMeasurable borel (likelihood k) := by
  have real : MeasurableMap borel borel fun rate =>
      mul (Problib.Analysis.Real.SignedSeries.factorialTerm rate k) (exp (neg rate)) :=
    measurable_mul (Gamma.factorialTerm_measurable k)
      (MeasurableMap.comp exp_measurable neg_measurable)
  exact ofReal_measurable.comp real

/-- The likelihood is the Poisson law's mass at the count. -/
theorem likelihood_eq_law (k : Nat) (rate : Carrier) :
    likelihood k rate = Count.Poisson.law rate (fun value => value = k) :=
  (Count.Poisson.law_singleton rate k).symm

/-- Scoring a count under the Gamma law at a valid statistic gives the negative
binomial mass times the Gamma law at the incorporated statistic. -/
theorem step {s : Carrier × Carrier} (k : Nat) (valid : Valid s) :
    (Gamma.law s.1 s.2).withDensity (likelihood k) =
      Measure.smul (predictive s k) (Gamma.law (incorporate s k).1 (incorporate s k).2) := by
  have posterior := valid_incorporate k valid
  rw [Gamma.law_eq_withDensity valid.1 valid.2, Gamma.law_eq_withDensity posterior.1 posterior.2,
    Measure.smul_withDensity _ _ (Gamma.density_measurable_slice _ _),
    Measure.withDensity_withDensity _ (Gamma.density_measurable_slice _ _) (likelihood_measurable k)]
  congr 1
  funext rate
  unfold likelihood predictive
  rw [ENNReal.finite_mul_finite, ENNReal.finite_mul_finite,
    Gamma.poisson_conjugate valid.1 valid.2 k rate]
  rfl

/-- At a valid statistic the predictive is the Poisson law's mass at the count,
integrated against the Gamma law. -/
theorem predictive_eq_lintegral {s : Carrier × Carrier} (valid : Valid s) (k : Nat) :
    predictive s k =
      lintegral (Gamma.law s.1 s.2) fun rate => Count.Poisson.law rate (fun value => value = k) := by
  rw [show (fun rate => Count.Poisson.law rate (fun value => value = k)) = likelihood k from
    funext fun rate => (likelihood_eq_law k rate).symm]
  exact (Gamma.poisson_evidence valid.1 valid.2 k).symm

/-! ### The evidence in log space -/

/-- The log negative binomial mass:
`a log b + log Γ(a + k) - log Γ(a) - log Γ(k + 1) - (a + k) log(b + 1)`. -/
@[expose] def logPredictive (s : Carrier × Carrier) (k : Nat) : Carrier :=
  sub (sub (add (mul s.1 (logIntegral s.2)) (sub (lgamma (add s.1 (count k))) (lgamma s.1)))
      (lgamma (count (k + 1))))
    (mul (add s.1 (count k)) (logIntegral (add s.2 one)))

theorem count_nonnegative (k : Nat) : le zero (count k) := ofRat_nat_nonnegative k

theorem add_count_positive {value : Carrier} (positive : lt zero value) (k : Nat) :
    lt zero (add value (count k)) := by
  have raised := add_le_add (le_refl value) (count_nonnegative k)
  rw [add_zero] at raised
  exact lt_of_lt_of_le positive raised

/-- At a valid statistic the predictive is the exponential of its log. -/
theorem predictive_eq_exp {s : Carrier × Carrier} (valid : Valid s) (k : Nat) :
    predictive s k = ENNReal.ofReal (exp (logPredictive s k)) := by
  have shifted := add_count_positive valid.1 k
  have raised := add_positive valid.2 one_positive
  have factorial := Problib.Analysis.Real.SignedSeries.factorialTerm_one_positive k
  unfold predictive Gamma.poissonEvidence Gamma.evidence logPredictive
  change ENNReal.ofReal _ = _
  congr 1
  rw [show lgamma (count (k + 1)) =
      neg (logIntegral (Problib.Analysis.Real.SignedSeries.factorialTerm one k)) from lgamma_nat k]
  simp only [sub_eq_add_neg, exp_add, exp_neg, neg_neg]
  rw [exp_log _ factorial, exp_lgamma valid.1, exp_lgamma shifted,
    ← rpow_of_positive valid.2, ← rpow_of_positive raised, div_eq_mul_inverse, inverse_mul_total]
  unfold count
  real_grind

/-- At a valid statistic the log of the predictive is `logPredictive`. -/
theorem log_predictive {s : Carrier × Carrier} (valid : Valid s) (k : Nat) :
    logIntegral (predictive s k).toReal = logPredictive s k := by
  rw [predictive_eq_exp valid, ENNReal.toReal_ofReal (exp_positive _).1, log_exp]

/-- The sum of `log Γ(y + 1) = log y!` over the counts. -/
@[expose] def logFactorials (ys : List Nat) : Carrier :=
  ys.foldr (fun y total => add (lgamma (count (y + 1))) total) zero

/-- The log of the chain in closed form, from the count `n` and the total `S`:
`a log b + log Γ(a + S) - log Γ(a) - Σ log yᵢ! - (a + S) log(b + n)`. -/
@[expose] def logChain (s : Carrier × Carrier) (ys : List Nat) : Carrier :=
  sub (sub (add (mul s.1 (logIntegral s.2)) (sub (lgamma (add s.1 (count ys.sum))) (lgamma s.1)))
      (logFactorials ys))
    (mul (add s.1 (count ys.sum)) (logIntegral (add s.2 (count ys.length))))

theorem count_add (k n : Nat) : count (k + n) = add (count k) (count n) := by
  unfold count
  rw [Rat.natCast_add, ofRat_add]

theorem count_zero : count 0 = zero := by
  unfold count
  rw [show ((0 : Nat) : Rat) = 0 from rfl, ofRat_zero]

theorem count_succ (n : Nat) : count (n + 1) = add (count n) one := by
  rw [count_add]
  unfold count
  rw [show ((1 : Nat) : Rat) = 1 from rfl, ofRat_one]

/-- One step of the log chain: the log predictive at the statistic, plus the log
chain from the incorporated statistic. -/
theorem logChain_cons (s : Carrier × Carrier) (y : Nat) (ys : List Nat) :
    logChain s (y :: ys) = add (logPredictive s y) (logChain (incorporate s y) ys) := by
  unfold logChain logPredictive incorporate
  have total : add s.1 (count (y :: ys).sum) = add (add s.1 (count y)) (count ys.sum) := by
    rw [List.sum_cons, count_add, add_assoc]
  have length : add s.2 (count (y :: ys).length) = add (add s.2 one) (count ys.length) := by
    rw [List.length_cons, count_succ, add_assoc, add_comm one, ← add_assoc, add_assoc s.2,
      add_comm (count ys.length), ← add_assoc]
  have factorials : logFactorials (y :: ys) = add (lgamma (count (y + 1))) (logFactorials ys) := rfl
  simp only
  rw [total, length, factorials]
  real_grind

/-- At a valid statistic the chain is the exponential of its log. -/
theorem chain_eq_exp (shape rate : Carrier) :
    ∀ {s : Carrier × Carrier}, Valid s → ∀ ys : List Nat,
      (gammaPoissonUrn shape rate).chain s ys = ENNReal.ofReal (exp (logChain s ys))
  | s, _, [] => by
      have empty : logChain s [] = zero := by
        unfold logChain logFactorials
        simp only [List.sum_nil, List.length_nil, List.foldr_nil]
        rw [count_zero, add_zero, add_zero]
        real_grind
      change ENNReal.one = _
      rw [empty, exp_zero, ENNReal.ofReal_one]
  | s, valid, y :: ys => by
      change ENNReal.mul (predictive s y) ((gammaPoissonUrn shape rate).chain (incorporate s y) ys) = _
      rw [logChain_cons, exp_add,
        Problib.Measure.Real.ofReal_mul (exp_positive _).1 (exp_positive _).1]
      rw [predictive_eq_exp valid y, chain_eq_exp shape rate (valid_incorporate y valid) ys]

/-- At a valid statistic the log of the chain is `logChain`. -/
theorem log_chain (shape rate : Carrier) {s : Carrier × Carrier} (valid : Valid s)
    (ys : List Nat) :
    logIntegral ((gammaPoissonUrn shape rate).chain s ys).toReal = logChain s ys := by
  rw [chain_eq_exp shape rate valid, ENNReal.toReal_ofReal (exp_positive _).1, log_exp]

end GammaPoisson

/-- The Gamma–Poisson local latent: the rate drawn from the Gamma law at the
statistic, and each count scored by its Poisson mass. -/
@[expose] def gammaPoissonLocal (shape rate : Carrier) (shapePositive : lt zero shape)
    (ratePositive : lt zero rate) : (gammaPoissonUrn shape rate).LocalLatent where
  Value := Carrier
  valueSpace := borel
  standard := StandardBorel.real
  Valid := GammaPoisson.Valid
  valid_init := ⟨shapePositive, ratePositive⟩
  valid_inc := fun k valid => GammaPoisson.valid_incorporate k valid
  prior := ⟨Gamma.kernel, fun s => Gamma.law_isProbability s.1 s.2⟩
  likelihood := GammaPoisson.likelihood
  likelihood_measurable := GammaPoisson.likelihood_measurable
  step := fun k valid => GammaPoisson.step k valid

end

end

end Problib.Measure.Exchangeable
