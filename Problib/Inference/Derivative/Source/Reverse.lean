import Problib.Inference.Derivative.FirstOrder.Pipeline
import Problib.Inference.Derivative.Source.Normalization.Finite

set_option autoImplicit false

namespace Problib.Inference.Derivative.Source.Reverse

open Problib.Linear.Rational
open Problib.Probability

universe u

/-- Source expected correctness and term-local reconstruction derive the
meaning of the normalized staged program. No completed partial evaluation or
first-order correctness judgment is a premise. -/
theorem normalize_preserves_meaning_finite
    {Effect : Type → Type u} {Outcome : Type} {columns : Nat}
    {context : List Ty} (term : Term Rat context .scalar)
    (source : SourceMeaning Effect context)
    (target : DirectionalTarget Outcome columns context)
    (jacobian : Matrix 1 columns)
    (scalarRelation : Vector columns → Family.ScalarRelation source.Parameter Rat Rat)
    (relation : (direction : Vector columns) →
      Family.ComputationRelation source.Parameter Rat Rat Effect
        (FinitePMF (Outcome × (Rat × Vector 1))))
    (expectedCertificate : ExpectedCertificate term source target jacobian scalarRelation relation)
    (normalizer : Normalization.Finite.Normalizer Outcome columns)
    (symbolicEnvironment : Target.Environment Rat
      (Normalization.Finite.SymbolicTangent Outcome columns)
      (context.map Ty.derivative))
    (tangentRelated : (direction : Vector columns) →
      Normalization.Structural.TangentRelation
        (Normalization.Finite.SymbolicTangent Outcome columns) Rat)
    (reconstruction : Normalization.Finite.ReconstructionCertificate
      term normalizer target symbolicEnvironment tangentRelated) :
    (Normalization.Finite.Term.normalize term normalizer
        symbolicEnvironment).law.expectation
          (Normalization.Finite.Term.normalize term normalizer
            symbolicEnvironment).primal =
        source.observationFamily term source.point ∧
      (Normalization.Finite.Term.normalize term normalizer
        symbolicEnvironment).JVPUnbiased jacobian := by
  exact
    (Normalization.Finite.Term.partialEvaluate term normalizer target
      symbolicEnvironment tangentRelated reconstruction).meaning_preserved
        (term.directionalExecution_expected source target jacobian scalarRelation relation
          expectedCertificate)

/-- The common-law random linearization compiled from source syntax.

Its nonlinear law and samplewise linear matrix are obtained from normalization.
Coefficientwise unbiasedness is derived from source expected correctness. -/
def commonLawRandomLinearization
    {Effect : Type → Type u} {Outcome : Type} {columns : Nat}
    {context : List Ty} (term : Term Rat context .scalar)
    (source : SourceMeaning Effect context)
    (target : DirectionalTarget Outcome columns context)
    (jacobian : Matrix 1 columns)
    (scalarRelation : Vector columns → Family.ScalarRelation source.Parameter Rat Rat)
    (relation : (direction : Vector columns) →
      Family.ComputationRelation source.Parameter Rat Rat Effect
        (FinitePMF (Outcome × (Rat × Vector 1))))
    (expectedCertificate : ExpectedCertificate term source target jacobian scalarRelation relation)
    (normalizer : Normalization.Finite.Normalizer Outcome columns)
    (symbolicEnvironment : Target.Environment Rat
      (Normalization.Finite.SymbolicTangent Outcome columns)
      (context.map Ty.derivative))
    (tangentRelated : (direction : Vector columns) →
      Normalization.Structural.TangentRelation
        (Normalization.Finite.SymbolicTangent Outcome columns) Rat)
    (reconstruction : Normalization.Finite.ReconstructionCertificate
      term normalizer target symbolicEnvironment tangentRelated) :
    Problib.Inference.Derivative.RandomLinearization (Rat × Outcome) 1 columns jacobian :=
  FirstOrder.Pipeline.randomLinearization
    (Normalization.Finite.Term.normalize term normalizer symbolicEnvironment)
    jacobian
    (normalize_preserves_meaning_finite term source target jacobian scalarRelation relation
      expectedCertificate normalizer symbolicEnvironment tangentRelated
      reconstruction).2

/-- The derived random linearization uses exactly the nonlinear law exposed by
deterministic unzip. -/
@[simp] theorem commonLawRandomLinearization_law
    {Effect : Type → Type u} {Outcome : Type} {columns : Nat}
    {context : List Ty} (term : Term Rat context .scalar)
    (source : SourceMeaning Effect context)
    (target : DirectionalTarget Outcome columns context)
    (jacobian : Matrix 1 columns)
    (scalarRelation : Vector columns → Family.ScalarRelation source.Parameter Rat Rat)
    (relation : (direction : Vector columns) →
      Family.ComputationRelation source.Parameter Rat Rat Effect
        (FinitePMF (Outcome × (Rat × Vector 1))))
    (expectedCertificate : ExpectedCertificate term source target jacobian scalarRelation relation)
    (normalizer : Normalization.Finite.Normalizer Outcome columns)
    (symbolicEnvironment : Target.Environment Rat
      (Normalization.Finite.SymbolicTangent Outcome columns)
      (context.map Ty.derivative))
    (tangentRelated : (direction : Vector columns) →
      Normalization.Structural.TangentRelation
        (Normalization.Finite.SymbolicTangent Outcome columns) Rat)
    (reconstruction : Normalization.Finite.ReconstructionCertificate
      term normalizer target symbolicEnvironment tangentRelated) :
    (commonLawRandomLinearization term source target jacobian scalarRelation relation
        expectedCertificate normalizer symbolicEnvironment tangentRelated
      reconstruction).law =
      (FirstOrder.Unzip.transform
        (Normalization.Finite.Term.normalize term normalizer
          symbolicEnvironment)).law :=
  rfl

/-- Unzip is a verified view of the source CPS execution. The proof composes
normalization's semantic reconstruction with deterministic unzip correctness. -/
theorem unzip_execution_finite
    {Outcome : Type} {columns : Nat} {context : List Ty}
    (term : Term Rat context .scalar)
    (normalizer : Normalization.Finite.Normalizer Outcome columns)
    (target : DirectionalTarget Outcome columns context)
    (symbolicEnvironment : Target.Environment Rat
      (Normalization.Finite.SymbolicTangent Outcome columns)
      (context.map Ty.derivative))
    (tangentRelated : (direction : Vector columns) →
      Normalization.Structural.TangentRelation
        (Normalization.Finite.SymbolicTangent Outcome columns) Rat)
    (reconstruction : Normalization.Finite.ReconstructionCertificate
      term normalizer target symbolicEnvironment tangentRelated)
    (direction : Vector columns) :
    (FirstOrder.Unzip.transform
        (Normalization.Finite.Term.normalize term normalizer
          symbolicEnvironment)).execute direction ≈ₚ
      (term.directionalExecution target direction).map Prod.snd := by
  apply FinitePMF.Equivalent.trans
    (FirstOrder.Unzip.transform_correct
      (Normalization.Finite.Term.normalize term normalizer symbolicEnvironment)
      direction)
  exact FinitePMF.Equivalent.symm
    ((Normalization.Finite.Term.partialEvaluate term normalizer target
      symbolicEnvironment tangentRelated reconstruction).program_execution_preserved
        direction)

/-- Structural transposition is samplewise adjoint for every normalized source
residual. This theorem is deterministic. It uses neither expectation nor a
primitive correctness certificate. -/
theorem samplewise_transpose
    {Outcome : Type} {columns : Nat} {context : List Ty}
    (term : Term Rat context .scalar)
    (normalizer : Normalization.Finite.Normalizer Outcome columns)
    (symbolicEnvironment : Target.Environment Rat
      (Normalization.Finite.SymbolicTangent Outcome columns)
      (context.map Ty.derivative))
    (outcome : Outcome) (direction : Vector columns) (cotangent : Vector 1) :
    Vector.dot
        ((Normalization.Finite.Term.normalize term normalizer
          symbolicEnvironment).residual.apply outcome direction)
        cotangent =
      Vector.dot direction
        ((FirstOrder.Transpose.transform
          (FirstOrder.Unzip.transform
            (Normalization.Finite.Term.normalize term normalizer
              symbolicEnvironment))).residual.apply
              outcome cotangent) :=
  FirstOrder.Transpose.pointwise_adjoint
    (FirstOrder.Unzip.transform
      (Normalization.Finite.Term.normalize term normalizer symbolicEnvironment))
    outcome direction cotangent

/-- Finite expectation transports the derived all-direction source JVP theorem
through structural transpose for every deterministic cotangent. -/
theorem vjp_unbiased_finite
    {Effect : Type → Type u} {Outcome : Type} {columns : Nat}
    {context : List Ty} (term : Term Rat context .scalar)
    (source : SourceMeaning Effect context)
    (target : DirectionalTarget Outcome columns context)
    (jacobian : Matrix 1 columns)
    (scalarRelation : Vector columns → Family.ScalarRelation source.Parameter Rat Rat)
    (relation : (direction : Vector columns) →
      Family.ComputationRelation source.Parameter Rat Rat Effect
        (FinitePMF (Outcome × (Rat × Vector 1))))
    (expectedCertificate : ExpectedCertificate term source target jacobian scalarRelation relation)
    (normalizer : Normalization.Finite.Normalizer Outcome columns)
    (symbolicEnvironment : Target.Environment Rat
      (Normalization.Finite.SymbolicTangent Outcome columns)
      (context.map Ty.derivative))
    (tangentRelated : (direction : Vector columns) →
      Normalization.Structural.TangentRelation
        (Normalization.Finite.SymbolicTangent Outcome columns) Rat)
    (reconstruction : Normalization.Finite.ReconstructionCertificate
      term normalizer target symbolicEnvironment tangentRelated)
    (cotangent : Vector 1) :
    expectedVector
        (FirstOrder.Transpose.transform
          (FirstOrder.Unzip.transform
            (Normalization.Finite.Term.normalize term normalizer
              symbolicEnvironment))).law
        (fun sample =>
          (FirstOrder.Transpose.transform
            (FirstOrder.Unzip.transform
              (Normalization.Finite.Term.normalize term normalizer
                symbolicEnvironment))).residual.apply
                sample.2 cotangent) =
      Matrix.transposeApply jacobian cotangent :=
  FirstOrder.Pipeline.transpose_unbiased_finite
    (Normalization.Finite.Term.normalize term normalizer symbolicEnvironment)
    (normalize_preserves_meaning_finite term source target jacobian scalarRelation relation
      expectedCertificate normalizer symbolicEnvironment tangentRelated
      reconstruction).2 cotangent

/-- The scalar-output specialization compiles a source term directly to an
unbiased finite gradient estimator. -/
theorem gradient_unbiased_finite
    {Effect : Type → Type u} {Outcome : Type} {columns : Nat}
    {context : List Ty} (term : Term Rat context .scalar)
    (source : SourceMeaning Effect context)
    (target : DirectionalTarget Outcome columns context)
    (jacobian : Matrix 1 columns)
    (scalarRelation : Vector columns → Family.ScalarRelation source.Parameter Rat Rat)
    (relation : (direction : Vector columns) →
      Family.ComputationRelation source.Parameter Rat Rat Effect
        (FinitePMF (Outcome × (Rat × Vector 1))))
    (expectedCertificate : ExpectedCertificate term source target jacobian scalarRelation relation)
    (normalizer : Normalization.Finite.Normalizer Outcome columns)
    (symbolicEnvironment : Target.Environment Rat
      (Normalization.Finite.SymbolicTangent Outcome columns)
      (context.map Ty.derivative))
    (tangentRelated : (direction : Vector columns) →
      Normalization.Structural.TangentRelation
        (Normalization.Finite.SymbolicTangent Outcome columns) Rat)
    (reconstruction : Normalization.Finite.ReconstructionCertificate
      term normalizer target symbolicEnvironment tangentRelated) :
    expectedVector
        (FirstOrder.Transpose.transform
          (FirstOrder.Unzip.transform
            (Normalization.Finite.Term.normalize term normalizer
              symbolicEnvironment))).law
        (fun sample =>
          (FirstOrder.Transpose.transform
            (FirstOrder.Unzip.transform
              (Normalization.Finite.Term.normalize term normalizer
                symbolicEnvironment))).residual.apply
                sample.2 scalarSeed) =
      gradient jacobian :=
  FirstOrder.Pipeline.scalar_gradient_unbiased_finite
    (Normalization.Finite.Term.normalize term normalizer symbolicEnvironment)
    (normalize_preserves_meaning_finite term source target jacobian scalarRelation relation
      expectedCertificate normalizer symbolicEnvironment tangentRelated
      reconstruction).2

/-- The complete finite source-to-reverse pipeline.

The theorem exposes one derived common law, source execution reconstruction,
samplewise deterministic adjointness, and unbiased deterministic-cotangent VJP.
Its only analytic inputs are the local source expected-correctness and
normalization reconstruction certificates. -/
theorem compiled_source_reverse_adev_finite
    {Effect : Type → Type u} {Outcome : Type} {columns : Nat}
    {context : List Ty} (term : Term Rat context .scalar)
    (source : SourceMeaning Effect context)
    (target : DirectionalTarget Outcome columns context)
    (jacobian : Matrix 1 columns)
    (scalarRelation : Vector columns → Family.ScalarRelation source.Parameter Rat Rat)
    (relation : (direction : Vector columns) →
      Family.ComputationRelation source.Parameter Rat Rat Effect
        (FinitePMF (Outcome × (Rat × Vector 1))))
    (expectedCertificate : ExpectedCertificate term source target jacobian scalarRelation relation)
    (normalizer : Normalization.Finite.Normalizer Outcome columns)
    (symbolicEnvironment : Target.Environment Rat
      (Normalization.Finite.SymbolicTangent Outcome columns)
      (context.map Ty.derivative))
    (tangentRelated : (direction : Vector columns) →
      Normalization.Structural.TangentRelation
        (Normalization.Finite.SymbolicTangent Outcome columns) Rat)
    (reconstruction : Normalization.Finite.ReconstructionCertificate
      term normalizer target symbolicEnvironment tangentRelated)
    (direction : Vector columns) (cotangent : Vector 1) :
    let normal := Normalization.Finite.Term.normalize term normalizer
      symbolicEnvironment
    let linearization := commonLawRandomLinearization term source target jacobian
      scalarRelation relation expectedCertificate normalizer symbolicEnvironment tangentRelated
      reconstruction
    linearization.law =
        (FirstOrder.Transpose.transform
          (FirstOrder.Unzip.transform normal)).law ∧
      CoefficientwiseUnbiased linearization.law linearization.estimate
        jacobian ∧
      (FirstOrder.Unzip.transform normal).execute direction ≈ₚ
        (term.directionalExecution target direction).map Prod.snd ∧
      (∀ outcome,
        Vector.dot (normal.residual.apply outcome direction) cotangent =
          Vector.dot direction
            ((FirstOrder.Transpose.transform
              (FirstOrder.Unzip.transform normal)).residual.apply
                outcome cotangent)) ∧
      expectedVector
          (FirstOrder.Transpose.transform
            (FirstOrder.Unzip.transform normal)).law
          (fun sample =>
            (FirstOrder.Transpose.transform
              (FirstOrder.Unzip.transform normal)).residual.apply
                sample.2 cotangent) =
        Matrix.transposeApply jacobian cotangent := by
  dsimp only
  refine ⟨rfl,
    (commonLawRandomLinearization term source target jacobian scalarRelation relation
      expectedCertificate normalizer symbolicEnvironment tangentRelated
      reconstruction).coefficientwiseUnbiased,
    unzip_execution_finite term normalizer target symbolicEnvironment
      tangentRelated reconstruction direction, ?_,
    vjp_unbiased_finite term source target jacobian scalarRelation relation expectedCertificate
      normalizer symbolicEnvironment tangentRelated reconstruction cotangent⟩
  intro outcome
  exact samplewise_transpose term normalizer symbolicEnvironment outcome direction
    cotangent

end Problib.Inference.Derivative.Source.Reverse
