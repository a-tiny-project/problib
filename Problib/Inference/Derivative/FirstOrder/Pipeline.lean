import Problib.Inference.Derivative.FirstOrder.Transpose
import Problib.Inference.Derivative.RandomLinearization

set_option autoImplicit false

namespace Problib.Inference.Derivative.FirstOrder.Pipeline

open Problib.Linear.Rational
open Problib.Probability

universe u v

theorem unzip_jvp_unbiased {Outcome : Type u} {Value : Type v}
    {rows columns : Nat} (program : ADEV.Program Outcome Value rows columns)
    {target : Matrix rows columns} (correct : program.JVPUnbiased target) :
    JVPUnbiased (Unzip.transform program).law
      (fun sample => program.residual.denote sample.2) target := by
  intro tangent
  apply Problib.Linear.Rational.Vector.ext
  intro row
  change (program.law.map
      (fun outcome => (program.primal outcome, outcome))).expectation
        (fun sample => Matrix.apply
          (program.residual.denote sample.2) tangent row) =
      Matrix.apply target tangent row
  rw [FinitePMF.expectation_map]
  exact congrFun (correct tangent) row

def randomLinearization {Outcome : Type u} {Value : Type v}
    {rows columns : Nat} (program : ADEV.Program Outcome Value rows columns)
    (target : Matrix rows columns) (correct : program.JVPUnbiased target) :
    Problib.Inference.Derivative.RandomLinearization (Value × Outcome) rows columns target where
  law := (Unzip.transform program).law
  estimate := fun sample => program.residual.denote sample.2
  coefficientwiseUnbiased :=
    jvp_implies_coefficientwise (unzip_jvp_unbiased program correct)

theorem transpose_unbiased_finite {Outcome : Type u} {Value : Type v}
    {rows columns : Nat} (program : ADEV.Program Outcome Value rows columns)
    {target : Matrix rows columns} (correct : program.JVPUnbiased target)
    (cotangent : Vector rows) :
    expectedVector (Transpose.transform (Unzip.transform program)).law
        (fun sample =>
          (Transpose.transform (Unzip.transform program)).residual.apply
            sample.2 cotangent) =
      Matrix.transposeApply target cotangent := by
  simpa [randomLinearization, Unzip.transform, Transpose.transform, Linear.Program.apply,
    Linear.Program.denote_transpose, Matrix.transposeApply] using
    (randomLinearization program target correct).transpose_unbiased_finite cotangent

theorem scalar_gradient_unbiased_finite {Outcome : Type u} {Value : Type v}
    {columns : Nat} (program : ADEV.Program Outcome Value 1 columns)
    {target : Matrix 1 columns} (correct : program.JVPUnbiased target) :
    expectedVector (Transpose.transform (Unzip.transform program)).law
        (fun sample =>
          (Transpose.transform (Unzip.transform program)).residual.apply
            sample.2 scalarSeed) =
      gradient target := by
  simpa [gradient] using
    transpose_unbiased_finite program correct scalarSeed

end Problib.Inference.Derivative.FirstOrder.Pipeline
