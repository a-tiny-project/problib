import Problib.Inference.Derivative.Source.Lowering
import Problib.Inference.Derivative.Source.Normalization.Structural

set_option autoImplicit false

namespace Problib.Inference.Derivative.Source.Normalization.Finite

open Problib.Linear.Rational
open Problib.Probability

abbrev SymbolicTangent (Outcome : Type) (columns : Nat) :=
  FirstOrder.Linear.Program Outcome 1 columns

/-- Effect-preserving normalization produces the existing staged ADEV program.
The finite nonlinear law is fixed before tangent choice and the residual is
intrinsically typed sample-free linear syntax. -/
abbrev NormalForm (Outcome : Type) (columns : Nat) :=
  FirstOrder.ADEV.Program Outcome Rat 1 columns

/-- Reconstruct the joint outcome, primal, and JVP execution from a normalized
form. Tangent application occurs only after sampling the nonlinear law. -/
def NormalForm.jointExecution {Outcome : Type} {columns : Nat}
    (normal : NormalForm Outcome columns) (direction : Vector columns) :
    FinitePMF (Outcome × (Rat × Vector 1)) :=
  normal.law.map fun outcome =>
    (outcome, (normal.primal outcome, normal.residual.apply outcome direction))

/-- The symbolic terminal continuation for a pure CPS return. -/
def NormalForm.terminal {Outcome : Type} {columns : Nat}
    (pureOutcome : Outcome)
    (jet : Target.Jet Rat (SymbolicTangent Outcome columns)) :
    NormalForm Outcome columns where
  law := FinitePMF.dirac pureOutcome
  primal := fun _ => jet.1
  residual := jet.2

/-- Symbolic target semantics used by partial evaluation. Primitive handlers
operate on typed residuals and must keep all effects inside the resulting
nonlinear law. -/
structure Normalizer (Outcome : Type) (columns : Nat) where
  pureOutcome : Outcome
  model : Target.Model Rat (SymbolicTangent Outcome columns)
    (NormalForm Outcome columns)

def zeroResidual (Outcome : Type) (columns : Nat) :
    SymbolicTangent Outcome columns :=
  .zero 1 columns

/-- Total structural interpretation of the published CPS ADEV target into the
finite staged normal form. -/
def Term.normalize {Outcome : Type} {columns : Nat} {context : List Ty}
    (term : Term Rat context .scalar) (normalizer : Normalizer Outcome columns)
    (environment : Target.Environment Rat
      (SymbolicTangent Outcome columns)
      (context.map Ty.derivative)) : NormalForm Outcome columns :=
  (term.adev (zeroResidual Outcome columns)).denote normalizer.model environment
    (NormalForm.terminal normalizer.pureOutcome)

/-- Ordered source composition remains literal CPS nesting during
normalization. The theorem contains no exchange rule. -/
@[simp] theorem Term.normalize_let {Outcome : Type} {columns : Nat}
    {context : List Ty} {bound : Ty}
    (first : Term Rat context bound) (body : Term Rat (bound :: context) .scalar)
    (normalizer : Normalizer Outcome columns)
    (environment : Target.Environment Rat
      (SymbolicTangent Outcome columns)
      (context.map Ty.derivative)) :
    Term.normalize (Term.let_ first body) normalizer environment =
      (first.adev (zeroResidual Outcome columns)).denote normalizer.model
        environment fun value =>
          (body.adev (zeroResidual Outcome columns)).denote normalizer.model
            (.cons value environment)
            (NormalForm.terminal normalizer.pureOutcome) :=
  rfl

/-- Lean's total definition produces a normal form for every intrinsically
typed scalar term in the admitted fragment. -/
theorem Term.normalize_total {Outcome : Type} {columns : Nat}
    {context : List Ty} (term : Term Rat context .scalar)
    (normalizer : Normalizer Outcome columns)
    (environment : Target.Environment Rat
      (SymbolicTangent Outcome columns)
      (context.map Ty.derivative)) :
    ∃ normal : NormalForm Outcome columns,
      Term.normalize term normalizer environment = normal :=
  ⟨Term.normalize term normalizer environment, rfl⟩

/-- Normalization produces a staged program with the exact scalar-output and
input-dimension indices. -/
theorem Term.normalize_type_preserving {Outcome : Type} {columns : Nat}
    {context : List Ty} (term : Term Rat context .scalar)
    (normalizer : Normalizer Outcome columns)
    (environment : Target.Environment Rat
      (SymbolicTangent Outcome columns)
    (context.map Ty.derivative)) :
    Nonempty (FirstOrder.ADEV.Program Outcome Rat 1 columns) :=
  ⟨Term.normalize term normalizer environment⟩

/-- Semantic reconstruction at one direction. The relation is extensional in
finite probability mass and does not compare raw weight-list representations. -/
def NormalForm.Reconstructs {Outcome : Type} {columns : Nat}
    (direction : Vector columns) (normal : NormalForm Outcome columns)
    (execution : FinitePMF (Outcome × (Rat × Vector 1))) : Prop :=
  execution ≈ₚ normal.jointExecution direction

/-- Local obligations that connect one symbolic normalizer to a family of
concrete directional target models.

The tangent relation may depend on the direction. Primitive certificates must
preserve related continuations. The terminal clause only relates pure returns.
No global staging or residual certificate is a field. -/
structure ReconstructionCertificate {Outcome : Type} {columns : Nat}
    {context : List Ty} (term : Term Rat context .scalar)
    (normalizer : Normalizer Outcome columns)
    (target : DirectionalTarget Outcome columns context)
    (symbolicEnvironment : Target.Environment Rat
      (SymbolicTangent Outcome columns)
      (context.map Ty.derivative))
    (tangentRelated : (direction : Vector columns) →
      Structural.TangentRelation
        (SymbolicTangent Outcome columns) Rat) : Prop where
  zeros : ∀ direction,
    tangentRelated direction (zeroResidual Outcome columns) 0
  environments : ∀ direction,
    Structural.EnvironmentRelated (tangentRelated direction)
      symbolicEnvironment (target.environment direction)
  admitted : ∀ direction,
    Structural.Admission normalizer.model (target.model direction)
      (tangentRelated direction) (NormalForm.Reconstructs direction) term
  terminal : ∀ direction symbolicJet concreteJet,
    Structural.ValueRelated (tangentRelated direction) Ty.scalar.derivative
      symbolicJet concreteJet →
    NormalForm.Reconstructs direction
      (NormalForm.terminal normalizer.pureOutcome symbolicJet)
      (scalarContinuation target.pureOutcome concreteJet)

/-- Effect-preserving reconstruction of the concrete directional execution.

The structural theorem fixes the symbolic normal form before a direction is
chosen. Each concrete execution is then the joint pushforward of that same law
by the normalized primal and residual application. -/
theorem Term.normalize_reconstructs {Outcome : Type} {columns : Nat}
    {context : List Ty} (term : Term Rat context .scalar)
    (normalizer : Normalizer Outcome columns)
    (target : DirectionalTarget Outcome columns context)
    (symbolicEnvironment : Target.Environment Rat
      (SymbolicTangent Outcome columns)
      (context.map Ty.derivative))
    (tangentRelated : (direction : Vector columns) →
      Structural.TangentRelation
        (SymbolicTangent Outcome columns) Rat)
    (certificate : ReconstructionCertificate term normalizer target
      symbolicEnvironment tangentRelated) :
    ∀ direction,
      NormalForm.Reconstructs direction
        (Term.normalize term normalizer symbolicEnvironment)
        (term.directionalExecution target direction) := by
  intro direction
  have related := Structural.fundamental
    (zeroResidual Outcome columns) 0 normalizer.model (target.model direction)
    (tangentRelated direction) (NormalForm.Reconstructs direction)
    (certificate.zeros direction) term (certificate.admitted direction)
    (certificate.environments direction)
  exact related
    (NormalForm.terminal normalizer.pureOutcome)
    (scalarContinuation target.pureOutcome)
    (certificate.terminal direction)

/-- A completed partial evaluation. The compiler stores its normal form and a
joint reconstruction theorem. The staging and linear-residual interfaces below
are derived views. -/
structure PartialEvaluation {Outcome : Type} {columns : Nat}
    (execution : DirectionalExecution Outcome columns) where
  normal : NormalForm Outcome columns
  reconstructs : ∀ direction,
    NormalForm.Reconstructs direction normal (execution direction)

/-- Local admission criterion for a symbolic primitive tangent. The witness is
sample-free typed syntax and the equation is samplewise, not in expectation. -/
def ResidualAdmissible {Outcome : Type} {columns : Nat}
    (tangent : Outcome → Vector columns → Vector 1) : Prop :=
  ∃ residual : FirstOrder.Linear.Program Outcome 1 columns,
    ∀ outcome direction,
      residual.apply outcome direction = tangent outcome direction

/-- Run the total normalizer and discharge reconstruction through local
primitive certificates. -/
def Term.partialEvaluate {Outcome : Type} {columns : Nat}
    {context : List Ty} (term : Term Rat context .scalar)
    (normalizer : Normalizer Outcome columns)
    (target : DirectionalTarget Outcome columns context)
    (symbolicEnvironment : Target.Environment Rat
      (SymbolicTangent Outcome columns)
      (context.map Ty.derivative))
    (tangentRelated : (direction : Vector columns) →
      Structural.TangentRelation
        (SymbolicTangent Outcome columns) Rat)
    (certificate : ReconstructionCertificate term normalizer target
      symbolicEnvironment tangentRelated) :
    PartialEvaluation (term.directionalExecution target) where
  normal := Term.normalize term normalizer symbolicEnvironment
  reconstructs := Term.normalize_reconstructs term normalizer target
    symbolicEnvironment tangentRelated certificate

/-- One tangent-independent law is derived from the completed normalization. -/
def PartialEvaluation.staging {Outcome : Type} {columns : Nat}
    {execution : DirectionalExecution Outcome columns}
    (evaluation : PartialEvaluation execution) :
    TangentIndependentStaging execution where
  law := evaluation.normal.law
  primal := evaluation.normal.primal
  tangent := fun outcome direction =>
    evaluation.normal.residual.apply outcome direction
  execution_eq := evaluation.reconstructs

/-- The samplewise-linear certificate is derived from the normal form's typed,
sample-free residual syntax. -/
def PartialEvaluation.linear {Outcome : Type} {columns : Nat}
    {execution : DirectionalExecution Outcome columns}
    (evaluation : PartialEvaluation execution) :
    SamplewiseLinearResidual evaluation.staging where
  residual := evaluation.normal.residual
  apply_eq := by
    intro outcome direction
    rfl

/-- The stored reconstruction theorem is exactly the execution law of the
derived staged program. -/
theorem PartialEvaluation.execution_law_preserved {Outcome : Type}
    {columns : Nat} {execution : DirectionalExecution Outcome columns}
    (evaluation : PartialEvaluation execution) (direction : Vector columns) :
    execution direction ≈ₚ evaluation.normal.jointExecution direction :=
  evaluation.reconstructs direction

/-- Projecting the joint reconstruction gives the exact execution law of the
normalized staged program. -/
theorem PartialEvaluation.program_execution_preserved {Outcome : Type}
    {columns : Nat} {execution : DirectionalExecution Outcome columns}
    (evaluation : PartialEvaluation execution) (direction : Vector columns) :
    (execution direction).map Prod.snd ≈ₚ evaluation.normal.execute direction := by
  simpa [PartialEvaluation.staging, PartialEvaluation.linear,
    TangentIndependentStaging.toProgram] using
    evaluation.staging.toProgram_execution evaluation.linear direction

/-- Expected primal correctness is used only after common-law reconstruction.
It is not an assumption of structural normalization. -/
theorem PartialEvaluation.primal_preserved {Outcome : Type}
    {columns : Nat} {execution : DirectionalExecution Outcome columns}
    {primalTarget : Rat} {jacobian : Matrix 1 columns}
    (evaluation : PartialEvaluation execution)
    (expected : ExpectedCorrectness execution primalTarget jacobian) :
    evaluation.normal.law.expectation evaluation.normal.primal = primalTarget :=
  expected.staged_primal_unbiased evaluation.staging

/-- Expected JVP correctness is transported to the normalized typed residual.
All expectation assumptions remain in the supplied `ExpectedCorrectness`. -/
theorem PartialEvaluation.jvp_preserved {Outcome : Type}
    {columns : Nat} {execution : DirectionalExecution Outcome columns}
    {primalTarget : Rat} {jacobian : Matrix 1 columns}
    (evaluation : PartialEvaluation execution)
    (expected : ExpectedCorrectness execution primalTarget jacobian) :
    evaluation.normal.JVPUnbiased jacobian := by
  simpa [PartialEvaluation.staging, PartialEvaluation.linear,
    TangentIndependentStaging.toProgram] using
    expected.staged_jvp_unbiased evaluation.staging evaluation.linear

/-- The final preservation boundary combines independently proved expected
correctness with the normalizer-derived staging and residual certificates. -/
theorem PartialEvaluation.meaning_preserved {Outcome : Type}
    {columns : Nat} {execution : DirectionalExecution Outcome columns}
    {primalTarget : Rat} {jacobian : Matrix 1 columns}
    (evaluation : PartialEvaluation execution)
    (expected : ExpectedCorrectness execution primalTarget jacobian) :
    evaluation.normal.law.expectation evaluation.normal.primal = primalTarget ∧
      evaluation.normal.JVPUnbiased jacobian :=
  ⟨evaluation.primal_preserved expected, evaluation.jvp_preserved expected⟩

end Problib.Inference.Derivative.Source.Normalization.Finite
