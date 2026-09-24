import Problib.Probability.Finite
import Problib.Inference.Derivative.FirstOrder.Linear

set_option autoImplicit false

namespace Problib.Inference.Derivative.FirstOrder.ADEV

open Problib.Linear.Rational
open Problib.Probability

universe u v

/-- The finite staged output expected after ADEV and effect-preserving partial
evaluation. Sampling and nonlinear coefficients are fixed before a tangent is
supplied. This is a semantic boundary, not a compiler for the published CPS
calculus. -/
structure Program (Outcome : Type u) (Value : Type v) (rows columns : Nat) where
  law : FinitePMF Outcome
  primal : Outcome → Value
  residual : Linear.Program Outcome rows columns

def Program.samplingLaw {Outcome : Type u} {Value : Type v} {rows columns : Nat}
    (program : Program Outcome Value rows columns) (_tangent : Vector columns) :
    FinitePMF Outcome :=
  program.law

@[simp] theorem Program.samplingLaw_independent_of_tangent
    {Outcome : Type u} {Value : Type v} {rows columns : Nat}
    (program : Program Outcome Value rows columns) (left right : Vector columns) :
    program.samplingLaw left = program.samplingLaw right :=
  rfl

def Program.execute {Outcome : Type u} {Value : Type v} {rows columns : Nat}
    (program : Program Outcome Value rows columns) (tangent : Vector columns) :
    FinitePMF (Value × Vector rows) :=
  program.law.map fun outcome =>
    (program.primal outcome, program.residual.apply outcome tangent)

def Program.JVPUnbiased {Outcome : Type u} {Value : Type v} {rows columns : Nat}
    (program : Program Outcome Value rows columns) (target : Matrix rows columns) : Prop :=
  Problib.Linear.Rational.JVPUnbiased program.law
    (fun outcome => program.residual.denote outcome) target

theorem Program.residual_add {Outcome : Type u} {Value : Type v} {rows columns : Nat}
    (program : Program Outcome Value rows columns) (outcome : Outcome)
    (left right : Vector columns) :
    program.residual.apply outcome
        (Problib.Linear.Rational.Vector.add left right) =
      Problib.Linear.Rational.Vector.add
        (program.residual.apply outcome left)
        (program.residual.apply outcome right) :=
  program.residual.apply_add outcome left right

theorem Program.residual_scale {Outcome : Type u} {Value : Type v} {rows columns : Nat}
    (program : Program Outcome Value rows columns) (outcome : Outcome)
    (constant : Rat) (tangent : Vector columns) :
    program.residual.apply outcome
        (Problib.Linear.Rational.Vector.scale constant tangent) =
      Problib.Linear.Rational.Vector.scale constant
        (program.residual.apply outcome tangent) :=
  program.residual.apply_scale outcome constant tangent

end Problib.Inference.Derivative.FirstOrder.ADEV
