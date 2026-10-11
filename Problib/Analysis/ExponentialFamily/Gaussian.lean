module

public import Problib.Analysis.ExponentialFamily
public import Problib.Analysis.Gaussian.Conjugate
public import Problib.Measure.Real.Lebesgue
import Problib.Analysis.Real.Limit
import Problib.Measure.Integral.Density.Algebra

/-! The Gaussian family with known variance and its Gaussian conjugate prior.

`gaussianMean variance` observes a real value at an unknown mean `μ` with a
fixed variance `v`. Its base is the Gaussian density at mean zero, its statistic
is `x/v`, its natural parameter is `μ` and its log partition is `μ²/(2v)`, so
the likelihood is the Gaussian density at `(μ, v)` (`likelihood_gaussianMean`).
The identity is `-(x-μ)²/(2v) = -x²/(2v) + μ(x/v) - μ²/(2v)`.

At evidence `(χ, ν)` with a positive count the conjugate weight
`exp(μχ - νμ²/(2v))` completes the square around `(v/ν)χ`, so the conjugate
kernel is the Gaussian law at `((v/ν)χ, v/ν)` (`conjugate_gaussianMean`). The
prior law at `(m, s)` is the conjugate kernel at `(m/s, v/s)`
(`conjugate_gaussianMean_prior`). One observation `x` updates it to the law at
the precision-weighted mean and the harmonic variance of
`Gaussian.density_conjugate` (`posterior_gaussianMean`).

Against volume, which has infinite mass, the flat evidence `(0, 0)` has no
normalization (`conjugate_gaussianMean_flat`). One observation `x` repairs it:
the flat prior updates to the Gaussian law at `(x, v)`
(`posterior_gaussianMean_flat`).

The batch posterior at any prior evidence `(χ, ν)` needs only a positive
updated count `ν + N` (`posterior_gaussianMean_evidence`). The flat evidence
is the boundary `ν + N = 0` of that premise, and any `N ≥ 1` observations
normalize it (`posterior_gaussianMean_flat_batch`).
-/

set_option autoImplicit false

open scoped Problib.Real.AC

namespace Problib.Analysis.ExponentialFamily

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

/-- The Gaussian family of observations at an unknown mean and a known
variance. -/
@[expose] public def gaussianMean (variance : Carrier) : ExponentialFamily borel borel 1 where
  base value := Gaussian.density zero variance value
  statistic value _ := div value variance
  natural mean _ := mean
  logPartition mean := div (mul mean mean) (mul (selection.ofRat 2) variance)
  base_measurable := Gaussian.density_measurable_slice zero variance
  statistic_measurable _ :=
    measurable_div (MeasurableMap.identity borel) (MeasurableMap.constant _ borel variance)
  natural_measurable _ := MeasurableMap.identity borel
  logPartition_measurable :=
    measurable_div (measurable_mul (MeasurableMap.identity borel) (MeasurableMap.identity borel))
      (MeasurableMap.constant _ borel (mul (selection.ofRat 2) variance))

/-- Twice a product over twice a variance is the product over the variance. -/
private theorem double_cancel (left right variance : Carrier) :
    mul (mul left (add right right)) (inverse (mul (selection.ofRat 2) variance)) =
      mul (mul left right) (inverse variance) := by
  rw [show add right right = mul right (selection.ofRat 2) from Real.add_self right,
    inverse_mul_total]
  calc mul (mul left (mul right (selection.ofRat 2)))
          (mul (inverse (selection.ofRat 2)) (inverse variance))
      = mul (mul (mul left right) (inverse variance))
          (mul (selection.ofRat 2) (inverse (selection.ofRat 2))) := by ac_rfl
    _ = mul (mul left right) (inverse variance) := by
        rw [mul_inverse_cancel (nonzero_of_positive ofRat_two_positive), mul_one]

/-- The negated square of a difference, expanded, with a common scale. -/
private theorem neg_square_expand (value center scale : Carrier) :
    neg (mul (mul (sub value center) (sub value center)) scale) =
      add (add (neg (mul (mul value value) scale)) (mul (mul value (add center center)) scale))
        (neg (mul (mul center center) scale)) := by
  simp only [sub_eq_add_neg, mul_add, add_mul, neg_mul, mul_neg, neg_neg, neg_add]
  ac_rfl

private theorem add_add_neg_cancel (first second : Carrier) :
    add first (add second (neg first)) = second := by
  rw [add_comm second, ← add_assoc, add_neg, add_comm, add_zero]

/-- The likelihood of the family is the Gaussian density at the mean and the
known variance. -/
public theorem likelihood_gaussianMean (variance mean value : Carrier) :
    (gaussianMean variance).likelihood mean value =
      ENNReal.finite (Gaussian.density mean variance value) := by
  show ENNReal.mul (ENNReal.finite (Gaussian.density zero variance value))
      (ENNReal.ofReal (exp (sub (pairing 1 (fun _ => mean) (fun _ => div value variance))
        (div (mul mean mean) (mul (selection.ofRat 2) variance))))) = _
  rw [Gaussian.density_product, Gaussian.density_product, ENNReal.mul_assoc,
    ← ofReal_mul (exp_positive _).1 (exp_positive _).1, ← exp_add, pairing_one]
  congr 3
  simp only [div_eq_mul_inverse, sub_zero]
  rw [neg_square_expand, double_cancel, sub_eq_add_neg]
  ac_rfl

/-- The conjugate exponent completes the square around `spread · total`, where
`spread` is the variance over the count. -/
private theorem conjugate_exponent {mean total count variance spread : Carrier}
    (spreadInverse : inverse spread = mul count (inverse variance))
    (spreadNonzero : spread ≠ zero) :
    sub (mul mean total) (mul count (div (mul mean mean) (mul (selection.ofRat 2) variance))) =
      add (div (mul (mul spread total) (mul spread total)) (mul (selection.ofRat 2) spread))
        (neg (div (mul (sub mean (mul spread total)) (sub mean (mul spread total)))
          (mul (selection.ofRat 2) spread))) := by
  have centered : mul (mul mean (mul spread total)) (inverse spread) = mul mean total := by
    calc mul (mul mean (mul spread total)) (inverse spread)
        = mul (mul mean total) (mul spread (inverse spread)) := by ac_rfl
      _ = mul mean total := by rw [mul_inverse_cancel spreadNonzero, mul_one]
  simp only [div_eq_mul_inverse]
  rw [neg_square_expand, add_add_neg_cancel, double_cancel, centered, inverse_mul_total,
    inverse_mul_total, spreadInverse, sub_eq_add_neg]
  ac_rfl

/-- At a positive count the conjugate kernel of the family is the Gaussian law
at mean `(v/ν)χ` and variance `v/ν`. -/
public theorem conjugate_gaussianMean {variance count : Carrier}
    (variancePositive : lt zero variance) (countPositive : lt zero count)
    (total : Fin 1 → Carrier) (fallback : Carrier) :
    (gaussianMean variance).conjugate volume volumeSFinite fallback (total, count) =
      Gaussian.law (mul (div variance count) (total 0)) (div variance count) := by
  have spreadPositive : lt zero (div variance count) := div_positive variancePositive countPositive
  have spreadInverse : inverse (div variance count) = mul count (inverse variance) := by
    rw [div_eq_mul_inverse, inverse_mul_total, inverse_inverse, mul_comm]
  have root := Gaussian.normalizer_positive _ spreadPositive
  have rootNonzero : (Gaussian.normalizer (div variance count)).toReal ≠ zero :=
    (positive_iff_nonnegative_and_nonzero.mp root).2
  have reciprocalNonnegative :
      le zero (inverse (Gaussian.normalizer (div variance count)).toReal) :=
    inverse_nonnegative root.1
  have scalePositive : lt zero (mul (exp (div (mul (mul (div variance count) (total 0))
      (mul (div variance count) (total 0))) (mul (selection.ofRat 2) (div variance count))))
      (Gaussian.normalizer (div variance count)).toReal) :=
    mul_positive (exp_positive _) root
  apply conjugate_eq_of_smul _ _ _ _ _ (Gaussian.law_isProbability _ _)
    (show ENNReal.Finite (ENNReal.ofReal (mul (exp (div (mul (mul (div variance count) (total 0))
      (mul (div variance count) (total 0))) (mul (selection.ofRat 2) (div variance count))))
      (Gaussian.normalizer (div variance count)).toReal)) from True.intro)
    (fun vanishing => scalePositive.2 (ENNReal.ofReal_eq_zero_iff.mp vanishing))
  rw [Gaussian.law_eq_withDensity _ _ spreadPositive,
    Measure.smul_withDensity _ _ (Gaussian.density_measurable_slice _ _)]
  apply congrArg
  funext mean
  show ENNReal.ofReal (exp (sub (pairing 1 (fun _ => mean) total)
      (mul count (div (mul mean mean) (mul (selection.ofRat 2) variance))))) = _
  rw [Gaussian.density_product, ← ENNReal.mul_assoc,
    ← ofReal_mul scalePositive.1 reciprocalNonnegative,
    ← ofReal_mul (mul_nonnegative scalePositive.1 reciprocalNonnegative) (exp_positive _).1,
    mul_assoc (exp _), mul_inverse_cancel rootNonzero, mul_one, ← exp_add, pairing_one,
    conjugate_exponent spreadInverse (nonzero_of_positive spreadPositive)]

/-- The Gaussian prior at mean `m` and variance `s` is the conjugate kernel at
the evidence `(m/s, v/s)`. -/
public theorem conjugate_gaussianMean_prior {variance priorVariance : Carrier}
    (variancePositive : lt zero variance) (priorPositive : lt zero priorVariance)
    (priorMean fallback : Carrier) :
    (gaussianMean variance).conjugate volume volumeSFinite fallback
        (fun _ => div priorMean priorVariance, div variance priorVariance) =
      Gaussian.law priorMean priorVariance := by
  rw [conjugate_gaussianMean variancePositive (div_positive variancePositive priorPositive),
    div_div_cancel _ _ (nonzero_of_positive variancePositive),
    mul_div_cancel _ (nonzero_of_positive priorPositive)]

private theorem base_ne_zero {variance : Carrier} (variancePositive : lt zero variance)
    (value : Carrier) : (gaussianMean variance).base value ≠ NNReal.zero := by
  intro vanishing
  have positive := Gaussian.density_positive zero variance variancePositive value
  change lt zero (NNReal.toReal ((gaussianMean variance).base value)) at positive
  rw [vanishing] at positive
  exact lt_irrefl zero positive

/-- The count after one observation, `v/s + 1`, is `(s+v)/s`. -/
private theorem count_succ {variance priorVariance : Carrier}
    (priorNonzero : priorVariance ≠ zero) :
    add (div variance priorVariance) one =
      mul (add priorVariance variance) (inverse priorVariance) := by
  rw [add_mul, mul_inverse_cancel priorNonzero, div_eq_mul_inverse, add_comm]

/-- Gaussian conjugacy through the general theorem. Under the prior at mean `m`
and variance `s`, the conditional law of the mean given one observation `x` is
the Gaussian law at the precision-weighted mean and the harmonic variance. -/
public theorem posterior_gaussianMean {variance priorVariance : Carrier}
    (variancePositive : lt zero variance) (priorPositive : lt zero priorVariance)
    (priorMean fallback : Carrier) (data : Fin 1 → Carrier) :
    Kernel.densityConditional volume volumeSFinite
        ((gaussianMean variance).joint
          (fun _ => div priorMean priorVariance, div variance priorVariance) 1)
        ((gaussianMean variance).joint_measurable _ 1) fallback data =
      Gaussian.law (Gaussian.posteriorMean (data 0) priorMean priorVariance variance)
        (Gaussian.posteriorVariance priorVariance variance) := by
  have varianceNonzero := nonzero_of_positive variancePositive
  have priorNonzero := nonzero_of_positive priorPositive
  rw [posterior _ _ _ _ _ data (fun index => base_ne_zero variancePositive (data index)),
    List.ofFn_succ, List.ofFn_zero]
  show (gaussianMean variance).conjugate volume volumeSFinite fallback
      (fun _ => add (div priorMean priorVariance) (add (div (data 0) variance) zero),
        add (div variance priorVariance) (add one zero)) = _
  rw [add_zero, add_zero, conjugate_gaussianMean variancePositive
    (add_positive (div_positive variancePositive priorPositive) one_positive),
    count_succ priorNonzero]
  have spread : div variance (mul (add priorVariance variance) (inverse priorVariance)) =
      Gaussian.posteriorVariance priorVariance variance := by
    unfold Gaussian.posteriorVariance
    rw [div_eq_mul_inverse, div_eq_mul_inverse, inverse_mul_total, inverse_inverse]
    ac_rfl
  rw [spread]
  congr 1
  unfold Gaussian.posteriorVariance Gaussian.posteriorMean
  simp only [div_eq_mul_inverse]
  calc mul (mul (mul priorVariance variance) (inverse (add priorVariance variance)))
        (add (mul priorMean (inverse priorVariance)) (mul (data 0) (inverse variance)))
      = add (mul (mul (mul variance priorMean) (inverse (add priorVariance variance)))
            (mul priorVariance (inverse priorVariance)))
          (mul (mul (mul priorVariance (data 0)) (inverse (add priorVariance variance)))
            (mul variance (inverse variance))) := by
        rw [mul_add]
        ac_rfl
    _ = mul (add (mul priorVariance (data 0)) (mul variance priorMean))
          (inverse (add priorVariance variance)) := by
        rw [mul_inverse_cancel priorNonzero, mul_inverse_cancel varianceNonzero, mul_one, mul_one,
          add_mul, add_comm]

/-- Against volume, the conjugate kernel at the flat evidence is the fallback:
the flat prior has no normalization. -/
public theorem conjugate_gaussianMean_flat (variance fallback : Carrier) :
    (gaussianMean variance).conjugate volume volumeSFinite fallback Evidence.zero =
      Measure.dirac borel fallback :=
  conjugate_flat _ volume volumeSFinite fallback volume_univ

/-- One observation `x` normalizes the flat prior: the conditional law of the
mean is the Gaussian law at `(x, v)`. -/
public theorem posterior_gaussianMean_flat {variance : Carrier}
    (variancePositive : lt zero variance) (fallback : Carrier) (data : Fin 1 → Carrier) :
    Kernel.densityConditional volume volumeSFinite
        ((gaussianMean variance).joint Evidence.zero 1)
        ((gaussianMean variance).joint_measurable _ 1) fallback data =
      Gaussian.law (data 0) variance := by
  rw [posterior _ _ _ _ _ data (fun index => base_ne_zero variancePositive (data index)),
    List.ofFn_succ, List.ofFn_zero]
  show (gaussianMean variance).conjugate volume volumeSFinite fallback
      (fun _ => add zero (add (div (data 0) variance) zero), add zero (add one zero)) = _
  rw [add_zero, add_zero, zero_add, zero_add,
    conjugate_gaussianMean variancePositive one_positive, div_one,
    mul_div_cancel _ (nonzero_of_positive variancePositive)]

/-- Gaussian conjugacy under a premise on the updated evidence only. Under the
conjugate prior at any evidence `(χ, ν)`, proper or not, the conditional law of
the mean given `N` observations with sum `S` is the Gaussian law at
`(v/ν')(χ + S/v)` and `v/ν'`, where `ν' = ν + N` is positive. -/
public theorem posterior_gaussianMean_evidence {variance : Carrier}
    (variancePositive : lt zero variance) (prior : Evidence 1) (fallback : Carrier)
    {count : Nat} (data : Fin count → Carrier)
    (countPositive : lt zero (add prior.2 (selection.ofRat (count : Rat)))) :
    Kernel.densityConditional volume volumeSFinite ((gaussianMean variance).joint prior count)
        ((gaussianMean variance).joint_measurable prior count) fallback data =
      Gaussian.law
        (mul (div variance (add prior.2 (selection.ofRat (count : Rat))))
          (add (prior.1 0) ((Evidence.laws.listSum
            ((List.ofFn data).map (gaussianMean variance).observation)).1 0)))
        (div variance (add prior.2 (selection.ofRat (count : Rat)))) := by
  have counted : (Evidence.laws.listSum
      ((List.ofFn data).map (gaussianMean variance).observation)).2 =
        selection.ofRat (count : Rat) := by
    rw [listSum_observation_count, List.length_ofFn]
  rw [posterior _ _ _ _ _ data (fun index => base_ne_zero variancePositive (data index))]
  show (gaussianMean variance).conjugate volume volumeSFinite fallback
      (fun index => add (prior.1 index) ((Evidence.laws.listSum
          ((List.ofFn data).map (gaussianMean variance).observation)).1 index),
        add prior.2 (Evidence.laws.listSum
          ((List.ofFn data).map (gaussianMean variance).observation)).2) = _
  rw [counted]
  exact conjugate_gaussianMean variancePositive countPositive _ fallback

/-- The flat prior with a batch: `N ≥ 1` observations with sum `S` normalize it,
and the conditional law of the mean is the Gaussian law at `S/N` and `v/N`,
written as `(v/N)(S/v)`. -/
public theorem posterior_gaussianMean_flat_batch {variance : Carrier}
    (variancePositive : lt zero variance) (fallback : Carrier) {count : Nat}
    (data : Fin (count + 1) → Carrier) :
    Kernel.densityConditional volume volumeSFinite
        ((gaussianMean variance).joint Evidence.zero (count + 1))
        ((gaussianMean variance).joint_measurable _ (count + 1)) fallback data =
      Gaussian.law
        (mul (div variance (selection.ofRat ((count + 1 : Nat) : Rat)))
          ((Evidence.laws.listSum
            ((List.ofFn data).map (gaussianMean variance).observation)).1 0))
        (div variance (selection.ofRat ((count + 1 : Nat) : Rat))) := by
  have general := posterior_gaussianMean_evidence variancePositive Evidence.zero fallback data
    (show lt zero (add zero (selection.ofRat ((count + 1 : Nat) : Rat))) by
      rw [zero_add]
      exact ofRat_succ_positive count)
  rw [general]
  show Gaussian.law (mul (div variance (add zero (selection.ofRat ((count + 1 : Nat) : Rat))))
      (add zero ((Evidence.laws.listSum
        ((List.ofFn data).map (gaussianMean variance).observation)).1 0)))
      (div variance (add zero (selection.ofRat ((count + 1 : Nat) : Rat)))) = _
  rw [zero_add, zero_add]

end

end Problib.Analysis.ExponentialFamily
