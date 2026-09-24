import Problib.Probability.Finite.Example
import Problib.Inference.Derivative.FirstOrder.Necessity
import Problib.Inference.Derivative.Source.Certificate
import Problib.Inference.Derivative.Source.Normalization

set_option autoImplicit false

namespace Problib.Inference.Derivative.Source.Necessity

open Problib.Linear.Rational
open Problib.Probability
open Problib.Probability.FiniteExample

/-- Primal-only pure composition cannot give every related computation the
same expected tangent. The two admissible pure jets force zero to equal one.
This isolates the inconsistent observation premise removed from source lowering. -/
theorem primal_only_observation_is_impossible
    {Effect : Type → Type} {Outcome : Type}
    (model : Model Rat Effect) (pureOutcome : Outcome)
    (relation : ComputationRelation Rat Rat Effect
      (FinitePMF (Outcome × (Rat × Vector 1))))
    (composition : CompositionCertificate model relation)
    (fixedTangent : Vector 1)
    (observe : ∀ {source : Effect Rat}
        {target : (Target.Jet Rat Rat → FinitePMF (Outcome × (Rat × Vector 1))) →
          FinitePMF (Outcome × (Rat × Vector 1))},
      relation .scalar source target →
        expectedVector (target (scalarContinuation pureOutcome))
          (fun sample => sample.2.2) = fixedTangent) : False := by
  have zeroRelated := composition.pure
    (result := .scalar) (source := (0 : Rat))
    (target := ((0 : Rat), (0 : Rat))) rfl
  have oneRelated := composition.pure
    (result := .scalar) (source := (0 : Rat))
    (target := ((0 : Rat), (1 : Rat))) rfl
  have impossible : (0 : Rat) = 1 := by
    simpa [expectedVector, scalarContinuation] using
      congrFun ((observe zeroRelated).trans (observe oneRelated).symm) 0
  exact (by decide : (0 : Rat) ≠ 1) impossible

def sourceModel : Model Nat (fun Value => Value) where
  pure value := value
  bind value next := next value
  normalReparameterized mean _scale := mean
  normalReinforce mean _scale := mean

/-- A type-correct target model with an intentionally invalid REINFORCE rule. -/
def badTargetModel : Target.Model Nat Nat Nat where
  normalReparameterized mean _scale continuation := continuation mean
  normalReinforce _mean _scale _continuation := 1

def reinforceTerm : Term Nat [] .scalar :=
  .normalReinforce (.scalar 0) (.scalar 1)

def observableEquality :
    ComputationRelation Nat Nat (fun Value => Value) Nat
  | .scalar, source, target => target (fun jet => jet.1) = source
  | .unit, _, _ => True
  | .product _ _, _, _ => True

/-- Intrinsic typing alone cannot establish a primitive's semantic
certificate: the same well-typed CPS rule admits a target interpretation that
changes the observable result. -/
theorem primitive_typing_does_not_imply_certificate :
    ((reinforceTerm.adev 0).denote badTargetModel .nil fun jet => jet.1) ≠
      reinforceTerm.denote sourceModel .nil := by
  decide

/-- The bad interpretation cannot satisfy even the scalar observable-equality
primitive certificate. -/
theorem bad_reinforce_has_no_observable_certificate :
    ¬ ReinforceNormalCertificate sourceModel badTargetModel observableEquality := by
  intro certificate
  have impossible := certificate.sound
    (sourceMean := 0) (sourceScale := 1)
    (targetMean := (0, 0)) (targetScale := (1, 0)) rfl rfl
  simp [observableEquality, sourceModel, badTargetModel] at impossible

abbrev coordinate : Fin 1 :=
  ⟨0, by decide⟩

def zeroDirection : Vector 1 :=
  fun _ => 0

def unitDirection : Vector 1 :=
  fun _ => 1

def zeroJacobian : Matrix 1 1 :=
  fun _ _ => 0

/-- An expected-correct directional execution whose exposed sample law is
chosen after inspecting the tangent. -/
def directionDependentExecution : DirectionalExecution Bool 1 :=
  fun direction =>
    (if direction coordinate = 0 then
      FinitePMF.dirac false
    else
      FinitePMF.dirac true).map fun outcome =>
        (outcome, (0, fun _ => 0))

theorem directionDependentExecution_expected :
    ExpectedCorrectness directionDependentExecution 0 zeroJacobian := by
  constructor
  · intro direction
    rw [directionDependentExecution, FinitePMF.expectation_map]
    simp only [FinitePMF.expectation_zero]
  · intro direction
    apply Problib.Linear.Rational.Vector.ext
    intro row
    change (directionDependentExecution direction).expectation
        (fun sample => sample.2.2 row) =
      Matrix.apply zeroJacobian direction row
    rw [directionDependentExecution, FinitePMF.expectation_map]
    simp [zeroJacobian, Matrix.apply]
    rw [finSum_zero]

/-- Expected directional correctness does not derive one pre-tangent outcome
law. The exposed outcome marginals at zero and unit directions disagree. -/
theorem expected_correctness_does_not_imply_tangent_independent_staging :
    ExpectedCorrectness directionDependentExecution 0 zeroJacobian ∧
      ¬Nonempty (TangentIndependentStaging directionDependentExecution) := by
  refine ⟨directionDependentExecution_expected, ?_⟩
  intro staged
  obtain ⟨staging⟩ := staged
  have equivalent := staging.outcome_marginal_independent_of_direction
    zeroDirection unitDirection
  have zeroMarginal :
      (directionDependentExecution zeroDirection).map Prod.fst ≈ₚ
        FinitePMF.dirac false := by
    change ((FinitePMF.dirac false).map fun outcome =>
        (outcome, (0, fun _ => 0))).map Prod.fst ≈ₚ FinitePMF.dirac false
    exact FinitePMF.Equivalent.trans
      (FinitePMF.map_comp
        (fun outcome : Bool => (outcome, (0, fun _ : Fin 1 => 0)))
        Prod.fst (FinitePMF.dirac false))
      (FinitePMF.map_id (FinitePMF.dirac false))
  have unitMarginal :
      (directionDependentExecution unitDirection).map Prod.fst ≈ₚ
        FinitePMF.dirac true := by
    change ((FinitePMF.dirac true).map fun outcome =>
        (outcome, (0, fun _ => 0))).map Prod.fst ≈ₚ FinitePMF.dirac true
    exact FinitePMF.Equivalent.trans
      (FinitePMF.map_comp
        (fun outcome : Bool => (outcome, (0, fun _ : Fin 1 => 0)))
        Prod.fst (FinitePMF.dirac true))
      (FinitePMF.map_id (FinitePMF.dirac true))
  have falseTrue := FinitePMF.Equivalent.trans
    (FinitePMF.Equivalent.symm zeroMarginal)
    (FinitePMF.Equivalent.trans equivalent unitMarginal)
  have massEqual := falseTrue.mass_eq false
  change (FinitePMF.dirac false).prob false =
    (FinitePMF.dirac true).prob false at massEqual
  rw [FinitePMF.prob_dirac, FinitePMF.prob_dirac] at massEqual
  exact (by decide : (1 : NNRat) ≠ 0) massEqual

/-- The existing fair-coin nonlinear residual, now retaining its sample as the
explicit staged outcome. -/
def nonlinearExecution : DirectionalExecution Bool 1 :=
  fun direction => fairCoin.map fun outcome =>
    (outcome, (0, FirstOrder.Necessity.nonlinearResidual outcome direction))

def nonlinearStaging : TangentIndependentStaging nonlinearExecution where
  law := fairCoin
  primal := fun _ => 0
  tangent := FirstOrder.Necessity.nonlinearResidual
  execution_eq := by
    intro direction
    exact FinitePMF.Equivalent.refl _

theorem nonlinearExecution_expected :
    ExpectedCorrectness nonlinearExecution 0 FirstOrder.Necessity.identity := by
  constructor
  · intro direction
    rw [nonlinearExecution, FinitePMF.expectation_map]
    exact FinitePMF.expectation_zero _
  · intro direction
    apply Problib.Linear.Rational.Vector.ext
    intro row
    change (nonlinearExecution direction).expectation
        (fun sample => sample.2.2 row) =
      Matrix.apply FirstOrder.Necessity.identity direction row
    rw [nonlinearExecution, FinitePMF.expectation_map]
    exact congrFun
      (FirstOrder.Necessity.nonlinear_residual_directionally_unbiased direction) row

/-- Even expected correctness under one exposed outcome law does not produce a
samplewise-linear residual. -/
theorem expected_staging_does_not_imply_samplewise_linear_residual :
    ExpectedCorrectness nonlinearExecution 0 FirstOrder.Necessity.identity ∧
      ¬Nonempty (SamplewiseLinearResidual nonlinearStaging) := by
  refine ⟨nonlinearExecution_expected, ?_⟩
  intro represented
  obtain ⟨linear⟩ := represented
  apply FirstOrder.Necessity.nonlinear_residual_not_representable
  refine ⟨linear.residual, ?_⟩
  intro outcome direction
  simpa [nonlinearStaging] using linear.apply_eq outcome direction

/-- A direction-dependent effect law cannot be produced by the
effect-preserving partial evaluator. Every completed result derives one
pre-tangent staging law. -/
theorem tangent_dependent_effect_rejected_by_partial_evaluation :
    ¬Nonempty
      (Normalization.Finite.PartialEvaluation directionDependentExecution) := by
  intro admitted
  obtain ⟨evaluation⟩ := admitted
  exact expected_correctness_does_not_imply_tangent_independent_staging.2
    ⟨evaluation.staging⟩

/-- A nonlinear directional residual is rejected at the local primitive
boundary because no typed sample-free linear program represents it
samplewise. -/
theorem nonlinear_residual_rejected_by_partial_evaluation :
    ¬Normalization.Finite.ResidualAdmissible
      FirstOrder.Necessity.nonlinearResidual :=
  FirstOrder.Necessity.nonlinear_residual_not_representable

end Problib.Inference.Derivative.Source.Necessity
