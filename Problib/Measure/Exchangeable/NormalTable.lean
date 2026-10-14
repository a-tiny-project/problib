module

public import Problib.Measure.Exchangeable.Summary
public import Problib.Measure.Exchangeable.Normal
public import Problib.Analysis.Gaussian.Network.Scalar
public import Problib.Measure.StandardBorel.Real
import Problib.Real.Grind

set_option autoImplicit false

/-!
# The Normal table

The Normal urn's mean is a latent value. After `n` observations with sum `t`
it is Normal at `postMean n t` with variance `postVar n`, and an observation
`y` is Normal around it with variance `likVar`. Scoring `y` under that law is
the urn's predictive at `y` times the law after `n + 1` observations with sum
`t + y` (`posterior_step`, and `normalLocal_step` at a history).

The step is the scalar score collapse (`Gaussian.scalar_score_collapse`) at the
mean's posterior. The posterior parameters it gives are the posterior mean and
variance after one more observation, by field arithmetic alone. The step makes
the mean a local latent value of the Normal urn (`normalLocal`), which the keyed
urn lifts to one mean per table (`normalTable`). The urn's predictive and
incorporation read only the count and the sum (`normalSummary`), so the Normal
urn also runs on that summary (`normalSummaryUrn`), with the same local latent
value (`normalSummaryLocal`).
-/

namespace Problib.Measure.Exchangeable

open Problib.Real Problib.Measure.Real Problib.Real.Construction.Dedekind Problib.Analysis

public section

noncomputable section

namespace Normal

/-- Positive prior and likelihood variances. -/
structure Positive (priorVar likVar : Carrier) : Prop where
  prior : lt zero priorVar
  likelihood : lt zero likVar

/-- The posterior precision after `n` observations is positive. -/
theorem precision_positive {priorVar likVar : Carrier} (positive : Positive priorVar likVar)
    (n : Nat) : lt zero (add (inverse priorVar) (div (selection.ofRat n) likVar)) := by
  have first := inverse_of_positive_positive positive.prior
  have second := div_nonnegative (ofRat_nat_nonnegative n) positive.likelihood.1
  real_grind

/-- The posterior variance after `n` observations is positive. -/
theorem postVar_positive {priorVar likVar : Carrier} (positive : Positive priorVar likVar)
    (n : Nat) : lt zero (postVar priorVar likVar n) :=
  inverse_of_positive_positive (precision_positive positive n)

/-! ### The posterior of the mean -/

/-- The posterior mean is measurable in the summary `(n, t)`. -/
theorem summaryMean_measurable (priorMean priorVar likVar : Carrier) :
    MeasurableMap (Space.product (Space.discrete Nat) borel) borel
      fun summary : Nat × Carrier => postMean priorMean priorVar likVar summary.1 summary.2 := by
  unfold postMean
  exact measurable_mul (left := fun summary : Nat × Carrier => postVar priorVar likVar summary.1)
    (right := fun summary => add (div priorMean priorVar) (div summary.2 likVar))
    (MeasurableMap.comp (MeasurableMap.from_discrete borel (postVar priorVar likVar))
      (Space.first_measurable _ _))
    (measurable_add (left := fun _ => div priorMean priorVar)
      (right := fun summary : Nat × Carrier => div summary.2 likVar)
      (MeasurableMap.constant _ borel _)
      (measurable_div (left := fun summary : Nat × Carrier => summary.2) (right := fun _ => likVar)
        (Space.second_measurable _ _) (MeasurableMap.constant _ borel likVar)))

/-- The mean's posterior law at each summary. -/
@[expose] def summaryPrior (priorMean priorVar likVar : Carrier) :
    LawFamily (Space.product (Space.discrete Nat) borel) borel where
  kernel := Gaussian.kernel.precomp
    (fun summary : Nat × Carrier =>
      (postMean priorMean priorVar likVar summary.1 summary.2, postVar priorVar likVar summary.1))
    (Space.pair_measurable (summaryMean_measurable priorMean priorVar likVar)
      (MeasurableMap.comp (MeasurableMap.from_discrete borel (postVar priorVar likVar))
        (Space.first_measurable _ _)))
  markov := fun _ => Gaussian.law_isProbability _ _

/-- One more observation adds one to the count in the precision. -/
theorem precision_succ (priorVar likVar : Carrier) (n : Nat) :
    add (inverse priorVar) (div (selection.ofRat ((n + 1 : Nat) : Rat)) likVar) =
      add (add (inverse priorVar) (div (selection.ofRat (n : Rat)) likVar)) (inverse likVar) := by
  rw [Rat.natCast_add, Rat.natCast_ofNat, ofRat_add, ofRat_one]
  real_grind

/-- **The Normal step.** Scoring `y` under the mean's posterior after `n`
observations with sum `t` gives the predictive at `y` times the posterior after
`n + 1` observations with sum `t + y`. -/
theorem posterior_step (priorMean priorVar likVar : Carrier) (positive : Positive priorVar likVar)
    (n : Nat) (t y : Carrier) :
    (Gaussian.law (postMean priorMean priorVar likVar n t) (postVar priorVar likVar n)).withDensity
        (fun value => ENNReal.finite (Gaussian.density value likVar y)) =
      Measure.smul (ENNReal.finite (Gaussian.density (postMean priorMean priorVar likVar n t)
          (add (postVar priorVar likVar n) likVar) y))
        (Gaussian.law (postMean priorMean priorVar likVar (n + 1) (add t y))
          (postVar priorVar likVar (n + 1))) := by
  rw [Gaussian.scalar_score_collapse _ _ _ y (postVar_positive positive n) positive.likelihood]
  have precisionNonzero := nonzero_of_positive (precision_positive positive n)
  have likNonzero := nonzero_of_positive positive.likelihood
  have likInverse := inverse_of_positive_positive positive.likelihood
  have precisionPositive := precision_positive positive n
  have variancePositive := postVar_positive positive n
  have priorNonzero := nonzero_of_positive positive.prior
  have sumNonzero : add (inverse (add (inverse priorVar) (div (selection.ofRat (n : Rat)) likVar)))
      likVar ≠ zero :=
    nonzero_of_positive (add_positive variancePositive positive.likelihood)
  have nextNonzero : add (add (inverse priorVar) (div (selection.ofRat (n : Rat)) likVar))
      (inverse likVar) ≠ zero := by
    apply nonzero_of_positive
    real_grind
  have varianceEq : div (mul (postVar priorVar likVar n) likVar) (add (postVar priorVar likVar n) likVar) =
      postVar priorVar likVar (n + 1) := by
    unfold postVar
    rw [precision_succ]
    real_grind
  have meanEq : div (add (mul (postMean priorMean priorVar likVar n t) likVar)
        (mul (postVar priorVar likVar n) y)) (add (postVar priorVar likVar n) likVar) =
      postMean priorMean priorVar likVar (n + 1) (add t y) := by
    unfold postMean postVar
    rw [precision_succ]
    real_grind
  unfold Gaussian.scalarMean Gaussian.scalarVariance
  rw [meanEq, varianceEq]

end Normal

open Normal

/-- The Normal urn's predictive and incorporation read only the count and the
sum. -/
@[expose] def normalSummary (priorMean priorVar likVar : Carrier) :
    (normalUrn priorMean priorVar likVar).Summary where
  Value := Nat × Carrier
  space := Space.product (Space.discrete Nat) borel
  summary := Normal.summary
  summary_measurable := Space.comap_map Normal.summary _
  predictive := fun summary y => ENNReal.finite (Gaussian.density
    (postMean priorMean priorVar likVar summary.1 summary.2)
    (add (postVar priorVar likVar summary.1) likVar) y)
  predictive_eq := fun _ _ => rfl
  predictive_measurable := ENNRealMeasurable.comp
    (map := fun p : (Carrier × Carrier) × Carrier => ENNReal.finite (Gaussian.density p.1.1 p.1.2 p.2))
    (before := fun pair : (Nat × Carrier) × Carrier =>
      ((postMean priorMean priorVar likVar pair.1.1 pair.1.2,
        add (postVar priorVar likVar pair.1.1) likVar), pair.2))
    Gaussian.density_measurable
    (Space.pair_measurable
      (Space.pair_measurable
        (MeasurableMap.comp (summaryMean_measurable priorMean priorVar likVar)
          (Space.first_measurable _ _))
        (MeasurableMap.comp
          (MeasurableMap.from_discrete borel fun n => add (postVar priorVar likVar n) likVar)
          (MeasurableMap.comp (Space.first_measurable _ _) (Space.first_measurable _ _))))
      (Space.second_measurable _ _))
  incorporate := fun summary y => (summary.1 + 1, add summary.2 y)
  incorporate_eq := fun (s : List Carrier) y => by
    change ((s ++ [y]).length, total (s ++ [y])) = (s.length + 1, add (total s) y)
    rw [List.length_append, total_snoc]
    rfl
  incorporate_measurable := Space.pair_measurable
    (MeasurableMap.comp (MeasurableMap.from_discrete (Space.discrete Nat) fun n => n + 1)
      (MeasurableMap.comp (Space.first_measurable _ _) (Space.first_measurable _ _)))
    (measurable_add (left := fun pair : (Nat × Carrier) × Carrier => pair.1.2)
      (right := fun pair => pair.2)
      (MeasurableMap.comp (Space.second_measurable _ _) (Space.first_measurable _ _))
      (Space.second_measurable _ _))

/-- The Normal urn on its count and sum. -/
@[expose] def normalSummaryUrn (priorMean priorVar likVar : Carrier) : Urn.{0, 0} borel :=
  Urn.ofSummary (normalSummary priorMean priorVar likVar)

/-- **The local Normal step.** Scoring `y` under the mean's posterior after a
history is the predictive at `y` times the posterior after the history and `y`. -/
theorem normalLocal_step (priorMean priorVar likVar : Carrier) (positive : Positive priorVar likVar)
    (s : List Carrier) (y : Carrier) :
    (Gaussian.law (postMean priorMean priorVar likVar s.length (total s))
        (postVar priorVar likVar s.length)).withDensity
        (fun value => ENNReal.finite (Gaussian.density value likVar y)) =
      Measure.smul (ENNReal.finite (Gaussian.density
          (postMean priorMean priorVar likVar s.length (total s))
          (add (postVar priorVar likVar s.length) likVar) y))
        (Gaussian.law (postMean priorMean priorVar likVar (s ++ [y]).length (total (s ++ [y])))
          (postVar priorVar likVar (s ++ [y]).length)) := by
  rw [List.length_append, total_snoc]
  exact posterior_step priorMean priorVar likVar positive s.length (total s) y

/-- **The Normal table.** The mean is a local latent value of the Normal urn:
its prior at a history is the posterior at the history's count and sum, and an
observation is Normal around it. -/
@[expose] def normalLocal (priorMean priorVar likVar : Carrier)
    (positive : Positive priorVar likVar) : (normalUrn priorMean priorVar likVar).LocalLatent where
  Value := Carrier
  valueSpace := borel
  standard := StandardBorel.real
  Valid := fun _ => True
  valid_init := trivial
  valid_inc := fun _ _ => trivial
  prior := {
    kernel := (summaryPrior priorMean priorVar likVar).kernel.precomp Normal.summary
      (Space.comap_map Normal.summary _)
    markov := fun _ => (summaryPrior priorMean priorVar likVar).markov _ }
  likelihood := fun y value => ENNReal.finite (Gaussian.density value likVar y)
  likelihood_measurable := fun y => ENNRealMeasurable.comp
    (map := fun p : (Carrier × Carrier) × Carrier => ENNReal.finite (Gaussian.density p.1.1 p.1.2 p.2))
    (before := fun value : Carrier => ((value, likVar), y))
    Gaussian.density_measurable
    (Space.pair_measurable
      (Space.pair_measurable (MeasurableMap.identity borel) (MeasurableMap.constant borel borel likVar))
      (MeasurableMap.constant borel borel y))
  step := fun {s} y _ => normalLocal_step priorMean priorVar likVar positive s y

/-- The Normal table on the summary urn: the same mean, read at the count and
sum. -/
@[expose] def normalSummaryLocal (priorMean priorVar likVar : Carrier)
    (positive : Positive priorVar likVar) :
    (normalSummaryUrn priorMean priorVar likVar).LocalLatent :=
  (normalLocal priorMean priorVar likVar positive).ofSummary (normalSummary priorMean priorVar likVar)
    (summaryPrior priorMean priorVar likVar) fun _ => rfl

/-- One Normal mean per table key, drawn independently. -/
@[expose] def normalTable (priorMean priorVar likVar : Carrier) (positive : Positive priorVar likVar)
    {κ : Type} (encode : κ → Nat) (injective : Function.Injective encode) :
    ((normalUrn priorMean priorVar likVar).keyed encode injective).Latent :=
  (normalLocal priorMean priorVar likVar positive).ofKeyed encode injective

end

end

end Problib.Measure.Exchangeable
