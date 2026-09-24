import Problib.Probability.Finite
import Problib.Inference.Derivative.FirstOrder.ADEV
import Problib.Inference.Derivative.Source.Family

set_option autoImplicit false

namespace Problib.Inference.Derivative.Source

open Problib.Linear.Rational
open Problib.Probability

universe u v

/-- Intrinsic typing makes type preservation an inhabitance theorem: the ADEV
target has exactly the translated context and the original result index. -/
theorem Term.adev_type_preserving {Scalar : Type u} {Tangent : Type v}
    (zero : Tangent) {context : List Ty} {result : Ty}
    (term : Term Scalar context result) :
    Nonempty (Target.CPS Scalar Tangent (context.map Ty.derivative) result) :=
  ⟨term.adev zero⟩

/-- A directional CPS execution retains its generated outcome beside the
primal and tangent observations. The outcome is not reconstructed from those
observations, so a staging proof must preserve their joint law. -/
abbrev DirectionalExecution (Outcome : Type u) (columns : Nat) :=
  Vector columns → FinitePMF (Outcome × (Rat × Vector 1))

/-- The terminal continuation records that a pure return generated no new
outcome beyond the target model's designated pure outcome. -/
def scalarContinuation {Outcome : Type u} (pureOutcome : Outcome)
    (jet : Target.Jet Rat Rat) : FinitePMF (Outcome × (Rat × Vector 1)) :=
  FinitePMF.dirac (pureOutcome, (jet.1, fun _ => jet.2))

/-- A family of finite target interpretations, one for each input direction.

Every interpretation returns its generated outcome explicitly. This interface
does not assert that the outcome law is direction independent. That stronger
fact is the separate `TangentIndependentStaging` boundary below. -/
structure DirectionalTarget (Outcome : Type u) (columns : Nat)
    (context : List Ty) where
  pureOutcome : Outcome
  model : Vector columns →
    Target.Model Rat Rat (FinitePMF (Outcome × (Rat × Vector 1)))
  environment : Vector columns →
    Target.Environment Rat Rat (context.map Ty.derivative)

/-- A parameterized source interpretation and its scalar observation.
Retaining the environment family distinguishes equal primals with different derivatives. -/
structure SourceMeaning (Effect : Type → Type v) (context : List Ty) where
  Parameter : Type
  point : Parameter
  model : Model Rat Effect
  environment : Parameter → Environment Rat context
  primal : Effect Rat → Rat

/-- The selected observation of the exact source term at every parameter. -/
def SourceMeaning.observationFamily {Effect : Type → Type v} {context : List Ty}
    (source : SourceMeaning Effect context) (term : Term Rat context .scalar) :
    source.Parameter → Rat :=
  fun parameter => source.primal (term.denote source.model (source.environment parameter))

/-- Run the typed CPS target for one direction. The returned law exposes the
generated outcome and preserves `let_` order through `Target.CPS.denote`. -/
def Term.directionalExecution {Outcome : Type u} {columns : Nat}
    {context : List Ty} (term : Term Rat context .scalar)
    (target : DirectionalTarget Outcome columns context) :
    DirectionalExecution Outcome columns :=
  fun direction =>
    (term.adev 0).denote (target.model direction)
      (target.environment direction) (scalarContinuation target.pureOutcome)

/-- The source `let_` remains ordered CPS nesting in every directional target
execution. No exchange or commutativity law is used. -/
@[simp] theorem Term.directionalExecution_let {Outcome : Type u}
    {columns : Nat} {context : List Ty} {bound : Ty}
    (first : Term Rat context bound) (body : Term Rat (bound :: context) .scalar)
    (target : DirectionalTarget Outcome columns context) :
    (Term.let_ first body).directionalExecution target = fun direction =>
      (first.adev 0).denote (target.model direction)
        (target.environment direction) fun value =>
          (body.adev 0).denote (target.model direction)
            (.cons value (target.environment direction))
            (scalarContinuation target.pureOutcome) :=
  rfl

/-- The observable finite correctness judgment before staging.

It states primal preservation and expected JVP correctness for every supplied
direction. It does not state that those executions share randomness or have a
samplewise-linear residual. -/
structure ExpectedCorrectness {Outcome : Type u} {columns : Nat}
    (execution : DirectionalExecution Outcome columns)
    (primalTarget : Rat) (jacobian : Matrix 1 columns) : Prop where
  primal : ∀ direction,
    (execution direction).expectation (fun sample => sample.2.1) = primalTarget
  jvp : ∀ direction,
    expectedVector (execution direction) (fun sample => sample.2.2) =
      Matrix.apply jacobian direction

/-- Source-indexed observation of a family-level CPS relation.
Each observed jet is related to its own source family. Uniqueness identifies
it with the selected term's reference jet, not a Jacobian shared by all terms.
The scalar and primitive relations retain their analytic obligations explicitly. -/
structure ExpectedCertificate {Effect : Type → Type v} {Outcome : Type u}
    {columns : Nat} {context : List Ty}
    (term : Term Rat context .scalar)
    (source : SourceMeaning Effect context)
    (target : DirectionalTarget Outcome columns context)
    (jacobian : Matrix 1 columns)
    (scalarRelation : Vector columns → Family.ScalarRelation source.Parameter Rat Rat)
    (relation : (direction : Vector columns) →
      Family.ComputationRelation source.Parameter Rat Rat Effect
        (FinitePMF (Outcome × (Rat × Vector 1)))) : Prop where
  unique : ∀ direction family left right,
    scalarRelation direction family left → scalarRelation direction family right → left = right
  environments : ∀ direction,
    Family.EnvironmentRelated (scalarRelation direction)
      source.environment (target.environment direction)
  semantics : ∀ direction,
    Family.Certificate 0 source.model (target.model direction)
      (scalarRelation direction) (relation direction)
  reference : ∀ direction,
    scalarRelation direction (source.observationFamily term)
      (source.observationFamily term source.point, Matrix.apply jacobian direction 0)
  observe : ∀ direction {sourceComputation : source.Parameter → Effect Rat}
      {targetComputation :
        (Target.Jet Rat Rat → FinitePMF (Outcome × (Rat × Vector 1))) →
          FinitePMF (Outcome × (Rat × Vector 1))},
    relation direction .scalar sourceComputation targetComputation →
      scalarRelation direction (fun parameter => source.primal (sourceComputation parameter))
        ((targetComputation (scalarContinuation target.pureOutcome)).expectation
            (fun sample => sample.2.1),
          expectedVector (targetComputation (scalarContinuation target.pureOutcome))
            (fun sample => sample.2.2) 0)

/-- The CPS ADEV transform preserves the selected source family's primal and
expected JVP. Family composition, primitive semantics, observation, and the
source-only reference jet supply the explicit semantic obligations. -/
theorem Term.directionalExecution_expected {Effect : Type → Type v}
    {Outcome : Type u} {columns : Nat} {context : List Ty}
    (term : Term Rat context .scalar) (source : SourceMeaning Effect context)
    (target : DirectionalTarget Outcome columns context)
    (jacobian : Matrix 1 columns)
    (scalarRelation : Vector columns → Family.ScalarRelation source.Parameter Rat Rat)
    (relation : (direction : Vector columns) →
      Family.ComputationRelation source.Parameter Rat Rat Effect
        (FinitePMF (Outcome × (Rat × Vector 1))))
    (certificate : ExpectedCertificate term source target jacobian scalarRelation relation) :
    ExpectedCorrectness (term.directionalExecution target)
      (source.observationFamily term source.point) jacobian := by
  have jet_eq (direction : Vector columns) :
      ((term.directionalExecution target direction).expectation (fun sample => sample.2.1),
        expectedVector (term.directionalExecution target direction) (fun sample => sample.2.2) 0) =
      (source.observationFamily term source.point, Matrix.apply jacobian direction 0) := by
    exact certificate.unique direction (source.observationFamily term) _ _
      (certificate.observe direction
        (Family.fundamental 0 source.model (target.model direction)
          (scalarRelation direction) (relation direction)
          (certificate.semantics direction) term (certificate.environments direction)))
      (certificate.reference direction)
  constructor
  · intro direction
    exact congrArg Prod.fst (jet_eq direction)
  · intro direction
    apply Problib.Linear.Rational.Vector.ext
    intro row
    have row_eq : row = 0 := Subsingleton.elim _ _
    subst row
    exact congrArg Prod.snd (jet_eq direction)

/-- A joint staging certificate.

One law on the exact exposed outcome carrier is chosen before any tangent.
Every directional CPS execution is semantically equivalent to its pushforward
by the joint outcome, primal, and tangent observation. -/
structure TangentIndependentStaging {Outcome : Type u} {columns : Nat}
    (execution : DirectionalExecution Outcome columns) where
  law : FinitePMF Outcome
  primal : Outcome → Rat
  tangent : Outcome → Vector columns → Vector 1
  execution_eq : ∀ direction,
    execution direction ≈ₚ law.map fun outcome =>
      (outcome, (primal outcome, tangent outcome direction))

/-- A separate samplewise-linearity certificate. It connects every staged
outcome and every tangent to one typed residual program, not merely their
expectations. -/
structure SamplewiseLinearResidual {Outcome : Type u} {columns : Nat}
    {execution : DirectionalExecution Outcome columns}
    (staging : TangentIndependentStaging execution) where
  residual : FirstOrder.Linear.Program Outcome 1 columns
  apply_eq : ∀ outcome direction,
    residual.apply outcome direction = staging.tangent outcome direction

/-- The staged first-order program derived from the joint staging and linear
residual certificates. -/
def TangentIndependentStaging.toProgram {Outcome : Type u} {columns : Nat}
    {execution : DirectionalExecution Outcome columns}
    (staging : TangentIndependentStaging execution)
    (linear : SamplewiseLinearResidual staging) :
    FirstOrder.ADEV.Program Outcome Rat 1 columns where
  law := staging.law
  primal := staging.primal
  residual := linear.residual

/-- Projecting the generated outcome from any directional execution recovers
the same pre-tangent law. -/
theorem TangentIndependentStaging.outcome_marginal {Outcome : Type u}
    {columns : Nat} {execution : DirectionalExecution Outcome columns}
    (staging : TangentIndependentStaging execution) (direction : Vector columns) :
    (execution direction).map Prod.fst ≈ₚ staging.law := by
  exact FinitePMF.Equivalent.trans
    ((staging.execution_eq direction).map Prod.fst)
    (FinitePMF.Equivalent.trans
    (FinitePMF.map_comp
      (fun outcome =>
        (outcome, (staging.primal outcome, staging.tangent outcome direction)))
      Prod.fst staging.law)
    (FinitePMF.map_id staging.law))

/-- The exposed generated-outcome marginal is independent of the tangent. -/
theorem TangentIndependentStaging.outcome_marginal_independent_of_direction
    {Outcome : Type u} {columns : Nat}
    {execution : DirectionalExecution Outcome columns}
    (staging : TangentIndependentStaging execution)
    (left right : Vector columns) :
    (execution left).map Prod.fst ≈ₚ (execution right).map Prod.fst :=
  FinitePMF.Equivalent.trans (staging.outcome_marginal left)
    (FinitePMF.Equivalent.symm (staging.outcome_marginal right))

/-- The joint CPS execution is the pushforward of the same pre-tangent law by
the staged primal and typed residual application. This is the coupled boundary
consumed by unzip. -/
theorem TangentIndependentStaging.toProgram_joint_execution {Outcome : Type u}
    {columns : Nat} {execution : DirectionalExecution Outcome columns}
    (staging : TangentIndependentStaging execution)
    (linear : SamplewiseLinearResidual staging) (direction : Vector columns) :
    execution direction ≈ₚ staging.law.map fun outcome =>
      (outcome, (staging.primal outcome, linear.residual.apply outcome direction)) := by
  apply FinitePMF.Equivalent.trans (staging.execution_eq direction)
  have observed :
      (fun outcome =>
        (outcome, (staging.primal outcome, staging.tangent outcome direction))) =
      (fun outcome =>
        (outcome, (staging.primal outcome, linear.residual.apply outcome direction))) := by
    funext outcome
    rw [linear.apply_eq outcome direction]
  rw [observed]
  exact FinitePMF.Equivalent.refl _

/-- The CPS-observed primal/JVP pair is the observation of the derived staged
program under the same coupled outcome law. -/
theorem TangentIndependentStaging.toProgram_execution {Outcome : Type u}
    {columns : Nat} {execution : DirectionalExecution Outcome columns}
    (staging : TangentIndependentStaging execution)
    (linear : SamplewiseLinearResidual staging) (direction : Vector columns) :
    (execution direction).map Prod.snd ≈ₚ
      (staging.toProgram linear).execute direction := by
  apply FinitePMF.Equivalent.trans
    ((staging.toProgram_joint_execution linear direction).map Prod.snd)
  exact FinitePMF.Equivalent.trans
    (FinitePMF.map_comp
      (fun outcome =>
        (outcome, (staging.primal outcome, linear.residual.apply outcome direction)))
      Prod.snd staging.law)
    (FinitePMF.Equivalent.refl _)

/-- Expected primal preservation descends from CPS execution to the one-law
staged program. It consumes staging but not residual linearity. -/
theorem ExpectedCorrectness.staged_primal_unbiased {Outcome : Type u}
    {columns : Nat} {execution : DirectionalExecution Outcome columns}
    {primalTarget : Rat} {jacobian : Matrix 1 columns}
    (expected : ExpectedCorrectness execution primalTarget jacobian)
    (staging : TangentIndependentStaging execution) :
    staging.law.expectation staging.primal = primalTarget := by
  let direction := Problib.Linear.Rational.Vector.zero columns
  let observePrimal : Outcome × (Rat × Vector 1) → Rat :=
    fun sample => sample.2.1
  calc
    staging.law.expectation staging.primal =
        (staging.law.map fun outcome =>
          (outcome, (staging.primal outcome, staging.tangent outcome direction))).expectation
            observePrimal := by
      rw [FinitePMF.expectation_map]
    _ = (execution direction).expectation observePrimal :=
      ((staging.execution_eq direction).expectation_eq observePrimal).symm
    _ = primalTarget := expected.primal direction

/-- Expected directional correctness and the samplewise residual equation
derive the staged program's all-direction JVP theorem. -/
theorem ExpectedCorrectness.staged_jvp_unbiased {Outcome : Type u}
    {columns : Nat} {execution : DirectionalExecution Outcome columns}
    {primalTarget : Rat} {jacobian : Matrix 1 columns}
    (expected : ExpectedCorrectness execution primalTarget jacobian)
    (staging : TangentIndependentStaging execution)
    (linear : SamplewiseLinearResidual staging) :
    (staging.toProgram linear).JVPUnbiased jacobian := by
  intro direction
  change expectedVector staging.law
      (fun outcome => linear.residual.apply outcome direction) =
    Matrix.apply jacobian direction
  apply Problib.Linear.Rational.Vector.ext
  intro row
  calc
    staging.law.expectation (fun outcome =>
        (staging.toProgram linear).residual.apply outcome direction row) =
        staging.law.expectation (fun outcome =>
          staging.tangent outcome direction row) := by
      apply FinitePMF.expectation_congr
      intro outcome
      exact congrFun (linear.apply_eq outcome direction) row
    _ = (staging.law.map fun outcome =>
          (outcome, (staging.primal outcome, staging.tangent outcome direction))).expectation
            (fun sample => sample.2.2 row) := by
      rw [FinitePMF.expectation_map]
    _ = (execution direction).expectation (fun sample => sample.2.2 row) :=
      ((staging.execution_eq direction).expectation_eq
        (fun sample => sample.2.2 row)).symm
    _ = Matrix.apply jacobian direction row :=
      congrFun (expected.jvp direction) row

/-- The complete pre-partial-evaluation bridge. Primal and JVP correctness are
derived jointly after expected correctness, common-law staging, and
samplewise-linearity have been established at their separate boundaries. -/
theorem ExpectedCorrectness.firstOrder_sound {Outcome : Type u}
    {columns : Nat} {execution : DirectionalExecution Outcome columns}
    {primalTarget : Rat} {jacobian : Matrix 1 columns}
    (expected : ExpectedCorrectness execution primalTarget jacobian)
    (staging : TangentIndependentStaging execution)
    (linear : SamplewiseLinearResidual staging) :
    staging.law.expectation staging.primal = primalTarget ∧
      (staging.toProgram linear).JVPUnbiased jacobian :=
  ⟨expected.staged_primal_unbiased staging,
    expected.staged_jvp_unbiased staging linear⟩

end Problib.Inference.Derivative.Source
