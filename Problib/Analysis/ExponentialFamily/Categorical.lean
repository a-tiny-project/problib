module

public import Problib.Analysis.ExponentialFamily
public import Problib.Analysis.Dirichlet.Conjugate
import Problib.Measure.Integral.Density.AlmostEverywhere

/-! The categorical family and its Dirichlet conjugate prior.

`categorical dimension` observes one of `dimension + 1` categories at a point
`θ` of the open simplex. Its statistic is the one-hot vector of the observed
category and its natural parameter is `(log θᵢ)ᵢ`, so the likelihood of `k` is
`exp(log θₖ) = θₖ` at points with positive coordinates. The base is one and the
log partition is zero, because the simplex constraint already normalizes the
likelihood.

At evidence `(α - 1, ν)` the conjugate weight is `∏ θᵢ^(αᵢ-1)` wherever every
coordinate is positive, which is almost every simplex point
(`simplex_ae_positive`). The conjugate kernel there is the Dirichlet law at `α`
for every count `ν` (`conjugate_categorical`), because the zero log partition
makes the count irrelevant. One observation of `k` updates the prior to the
Dirichlet law with `αₖ` raised by one (`posterior_categorical`), the result of
`Dirichlet.posterior` rederived through the general theorem.

At any evidence `(χ, ν)` with every `χᵢ > -1` the conjugate kernel is the
Dirichlet law at `χ + 1` (`conjugate_categorical_evidence`), and a batch
posterior needs that premise only on the updated evidence
(`posterior_categorical_evidence`). At its boundary, one `χᵢ = -1`, the weight
has no normalization (`categorical_zero_concentration_not_normalizable`). The
zero-concentration weight `∏ θᵢ⁻¹` at `(-1, ν)` fails it at every coordinate,
yet a batch that observes every category updates it to the Dirichlet law at the
category counts (`posterior_categorical_zeroConcentration`).
-/

set_option autoImplicit false

namespace Problib.Analysis.ExponentialFamily

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind
open Logarithm

noncomputable section

/-- The categorical family on `dimension + 1` categories, parameterized by the
open simplex. -/
@[expose] public def categorical (dimension : Nat) :
    ExponentialFamily (Space.discrete (Fin (dimension + 1)))
      (Space.pi (fun _ : Fin (dimension + 1) => borel)) (dimension + 1) where
  base _ := NNReal.one
  statistic observed index := if index = observed then one else zero
  natural point index := logIntegral (point index)
  logPartition _ := zero
  base_measurable := ENNRealMeasurable.of_measurableMap (MeasurableMap.from_discrete _ _)
  statistic_measurable _ := MeasurableMap.from_discrete borel _
  natural_measurable index :=
    MeasurableMap.comp log_measurable
      (Space.coordinate_measurable (fun _ : Fin (dimension + 1) => borel) index)
  logPartition_measurable := MeasurableMap.constant _ borel zero

/-- At positive coordinates, the exponential of the pairing of the logarithms
with `α - 1` is the Dirichlet weight at `α`. -/
private theorem exp_pairing_eq_weight : (count : Nat) →
    (concentration point : Fin count → Carrier) →
    (∀ index, lt zero (point index)) →
    ENNReal.ofReal (exp (additiveLaws.finSum count
        (fun index => mul (logIntegral (point index)) (sub (concentration index) one)))) =
      Dirichlet.weight count concentration point
  | 0, _, _, _ => by
      show ENNReal.ofReal (exp zero) = ENNReal.one
      rw [exp_zero, ENNReal.ofReal_one]
  | count + 1, concentration, point, positive => by
      show ENNReal.ofReal (exp (add (mul (logIntegral (point 0)) (sub (concentration 0) one))
          (additiveLaws.finSum count (fun index =>
            mul (logIntegral (finTail count point index))
              (sub (finTail count concentration index) one))))) =
        ENNReal.mul (shapePower (concentration 0) (point 0))
          (Dirichlet.weight count (finTail count concentration) (finTail count point))
      rw [exp_add, ofReal_mul (exp_positive _).1 (exp_positive _).1,
        exp_pairing_eq_weight count (finTail count concentration) (finTail count point)
          (fun index => positive index.succ),
        shapePower_of_positive _ (positive 0), rpow_of_positive (positive 0), mul_comm]

/-- At evidence `(α - 1, ν)` the categorical conjugate weight is the Dirichlet
weight at `α` almost everywhere on the simplex, for every `α` and `ν`. -/
private theorem weight_ae_dirichlet {dimension : Nat}
    (concentration : Fin (dimension + 1) → Carrier) (count : Carrier) :
    (simplex dimension).AEEq
      ((categorical dimension).weight (fun index => sub (concentration index) one, count))
      (Dirichlet.weight (dimension + 1) concentration) :=
  (simplex_ae_positive dimension).mono (fun point pointPositive => by
    show ENNReal.ofReal (exp (sub (additiveLaws.finSum (dimension + 1) (fun index =>
        mul (logIntegral (point index)) (sub (concentration index) one))) (mul count zero))) = _
    rw [mul_zero, sub_zero]
    exact exp_pairing_eq_weight (dimension + 1) concentration point pointPositive)

/-- The conjugate kernel of the categorical family at evidence `(α - 1, ν)` is
the Dirichlet law at `α`, whatever the count `ν`. -/
public theorem conjugate_categorical {dimension : Nat}
    {concentration : Fin (dimension + 1) → Carrier}
    (positive : ∀ index, lt zero (concentration index)) (count : Carrier)
    (fallback : Fin (dimension + 1) → Carrier) :
    (categorical dimension).conjugate (simplex dimension) (simplexSFinite dimension) fallback
        (fun index => sub (concentration index) one, count) =
      Dirichlet.law concentration := by
  have weighted := Measure.withDensity_congr_ae (weight_ae_dirichlet concentration count)
  rw [conjugate_eq_normalize _ _ _ _ _ (weighted ▸ Dirichlet.weight_normalizable positive),
    Dirichlet.law_eq_normalize positive]
  exact Measure.normalize_congr weighted _ _

/-- The concentration `χ + 1` of categorical evidence `χ`. -/
private theorem sub_concentration {dimension : Nat} (total : Fin (dimension + 1) → Carrier) :
    (fun index => sub (add (total index) one) one) = total :=
  funext fun index => by rw [add_comm (total index) one, add_sub_self]

/-- The conjugate kernel of the categorical family at any evidence `(χ, ν)`
with every `χᵢ > -1` is the Dirichlet law at `χ + 1`. -/
public theorem conjugate_categorical_evidence {dimension : Nat}
    {total : Fin (dimension + 1) → Carrier}
    (positive : ∀ index, lt zero (add (total index) one)) (count : Carrier)
    (fallback : Fin (dimension + 1) → Carrier) :
    (categorical dimension).conjugate (simplex dimension) (simplexSFinite dimension) fallback
        (total, count) =
      Dirichlet.law (fun index => add (total index) one) := by
  have general := conjugate_categorical positive count fallback
  rwa [sub_concentration] at general

/-- Evidence at the boundary of the premise of `conjugate_categorical_evidence`
has no normalization: one `χᵢ = -1`, with every other `χⱼ ≥ -1` and a positive
total concentration. -/
public theorem categorical_zero_concentration_not_normalizable {dimension : Nat}
    {total : Fin (dimension + 1) → Carrier}
    (nonnegative : ∀ index, le zero (add (total index) one))
    (totalPositive :
      lt zero (additiveLaws.finSum (dimension + 1) (fun index => add (total index) one)))
    (index : Fin (dimension + 1)) (vanishing : add (total index) one = zero) (count : Carrier) :
    ¬Measure.IsNormalizable
      ((simplex dimension).withDensity ((categorical dimension).weight (total, count))) := by
  have weighted := Measure.withDensity_congr_ae
    (weight_ae_dirichlet (fun index => add (total index) one) count)
  rw [sub_concentration] at weighted
  rw [weighted]
  exact Dirichlet.weight_not_normalizable nonnegative totalPositive index vanishing

/-- Categorical–Dirichlet conjugacy through the general theorem. Under the
prior at `(α - 1, ν)`, the conditional law of `θ` given one observation `k` is
the Dirichlet law with `αₖ` raised by one. -/
public theorem posterior_categorical {dimension : Nat}
    {concentration : Fin (dimension + 1) → Carrier}
    (positive : ∀ index, lt zero (concentration index)) (count : Carrier)
    (fallback : Fin (dimension + 1) → Carrier) (data : Fin 1 → Fin (dimension + 1)) :
    Kernel.densityConditional (simplex dimension) (simplexSFinite dimension)
        ((categorical dimension).joint (fun index => sub (concentration index) one, count) 1)
        ((categorical dimension).joint_measurable _ 1) fallback data =
      Dirichlet.law (Dirichlet.increment concentration (data 0)) := by
  rw [posterior _ _ _ _ _ data (fun _ => show NNReal.one ≠ NNReal.zero from NNReal.one_ne_zero)]
  have updated : (categorical dimension).update (fun index => sub (concentration index) one, count)
      (List.ofFn data) =
      (fun index => sub (Dirichlet.increment concentration (data 0) index) one,
        add count (add one zero)) := by
    rw [List.ofFn_succ, List.ofFn_zero]
    refine Prod.ext (funext fun index => ?_) rfl
    show add (sub (concentration index) one)
        (add (if index = data 0 then one else zero) zero) =
      sub (Dirichlet.increment concentration (data 0) index) one
    by_cases same : index = data 0
    · rw [ite_eq_left same, same, Dirichlet.increment_self, add_zero, sub_add_cancel, add_comm,
        add_sub_self]
    · rw [ite_eq_right same, Dirichlet.increment_of_ne _ same, add_zero, add_zero]
  rw [updated]
  exact conjugate_categorical (Dirichlet.increment_positive positive (data 0)) _ fallback

/-- Categorical–Dirichlet conjugacy under premises on the updated evidence
only. Under the conjugate prior at any evidence `(χ, ν)`, proper or not, the
conditional law of `θ` given a batch with category counts `S` is the Dirichlet
law at `χ + S + 1`, wherever every coordinate is positive. -/
public theorem posterior_categorical_evidence {dimension : Nat}
    (prior : Evidence (dimension + 1)) (fallback : Fin (dimension + 1) → Carrier)
    {count : Nat} (data : Fin count → Fin (dimension + 1))
    (positive : ∀ index, lt zero (add (add (prior.1 index) ((Evidence.laws.listSum
      ((List.ofFn data).map (categorical dimension).observation)).1 index)) one)) :
    Kernel.densityConditional (simplex dimension) (simplexSFinite dimension)
        ((categorical dimension).joint prior count)
        ((categorical dimension).joint_measurable prior count) fallback data =
      Dirichlet.law (fun index => add (add (prior.1 index) ((Evidence.laws.listSum
        ((List.ofFn data).map (categorical dimension).observation)).1 index)) one) := by
  rw [posterior _ _ _ _ _ data (fun _ => show NNReal.one ≠ NNReal.zero from NNReal.one_ne_zero)]
  exact conjugate_categorical_evidence positive _ fallback

/-- The zero-concentration prior. The weight `∏ θᵢ⁻¹` at evidence `(-1, ν)`
has no normalization (`categorical_zero_concentration_not_normalizable`), but a
batch that observes every category makes the posterior the Dirichlet law at the
category counts. -/
public theorem posterior_categorical_zeroConcentration {dimension : Nat} (count : Carrier)
    (fallback : Fin (dimension + 1) → Carrier) {observations : Nat}
    (data : Fin observations → Fin (dimension + 1))
    (observed : ∀ index, lt zero ((Evidence.laws.listSum
      ((List.ofFn data).map (categorical dimension).observation)).1 index)) :
    Kernel.densityConditional (simplex dimension) (simplexSFinite dimension)
        ((categorical dimension).joint (fun _ => neg one, count) observations)
        ((categorical dimension).joint_measurable _ observations) fallback data =
      Dirichlet.law
        (Evidence.laws.listSum ((List.ofFn data).map (categorical dimension).observation)).1 := by
  have shape : (fun index => add (add (neg one) ((Evidence.laws.listSum
      ((List.ofFn data).map (categorical dimension).observation)).1 index)) one) =
      (Evidence.laws.listSum ((List.ofFn data).map (categorical dimension).observation)).1 :=
    funext fun index => by
      rw [add_comm (neg one), add_assoc, add_comm (neg one) one, add_neg, add_zero]
  have general := posterior_categorical_evidence (fun _ => neg one, count) fallback data
    (fun index => by
      show lt zero (add (add (neg one) ((Evidence.laws.listSum
        ((List.ofFn data).map (categorical dimension).observation)).1 index)) one)
      rw [congrFun shape index]
      exact observed index)
  rw [general]
  exact congrArg Dirichlet.law shape

end

end Problib.Analysis.ExponentialFamily
