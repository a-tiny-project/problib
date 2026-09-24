import Problib.Inference.Derivative.FirstOrder.Unzip

set_option autoImplicit false

namespace Problib.Inference.Derivative.FirstOrder.Transpose

open Problib.Linear.Rational

universe u v

def transform {Outcome : Type u} {Value : Type v} {rows columns : Nat}
    (program : Unzip.Program Outcome Value rows columns) :
    Unzip.Program Outcome Value columns rows where
  law := program.law
  residual := program.residual.transpose

@[simp] theorem transform_law {Outcome : Type u} {Value : Type v}
    {rows columns : Nat} (program : Unzip.Program Outcome Value rows columns) :
    (transform program).law = program.law :=
  rfl

@[simp] theorem transform_involution {Outcome : Type u} {Value : Type v}
    {rows columns : Nat} (program : Unzip.Program Outcome Value rows columns) :
    transform (transform program) = program := by
  cases program
  simp [transform]

theorem pointwise_adjoint {Outcome : Type u} {Value : Type v}
    {rows columns : Nat} (program : Unzip.Program Outcome Value rows columns)
    (outcome : Outcome) (tangent : Vector columns) (cotangent : Vector rows) :
    Vector.dot (program.residual.apply outcome tangent) cotangent =
      Vector.dot tangent
        ((transform program).residual.apply outcome cotangent) :=
  program.residual.transpose_adjoint outcome tangent cotangent

end Problib.Inference.Derivative.FirstOrder.Transpose
