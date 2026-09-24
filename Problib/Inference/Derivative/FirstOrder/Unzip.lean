import Problib.Inference.Derivative.FirstOrder.ADEV

set_option autoImplicit false

namespace Problib.Inference.Derivative.FirstOrder.Unzip

open Problib.Linear.Rational
open Problib.Probability

universe u v

/-- A sampled nonlinear value and tape, paired with a sample-free residual. -/
structure Program (Outcome : Type u) (Value : Type v) (rows columns : Nat) where
  law : FinitePMF (Value × Outcome)
  residual : Linear.Program Outcome rows columns

def Program.execute {Outcome : Type u} {Value : Type v} {rows columns : Nat}
    (program : Program Outcome Value rows columns) (tangent : Vector columns) :
    FinitePMF (Value × Vector rows) :=
  program.law.map fun sample =>
    (sample.1, program.residual.apply sample.2 tangent)

def transform {Outcome : Type u} {Value : Type v} {rows columns : Nat}
    (program : ADEV.Program Outcome Value rows columns) :
    Program Outcome Value rows columns where
  law := program.law.map fun outcome => (program.primal outcome, outcome)
  residual := program.residual

@[simp] theorem transform_law {Outcome : Type u} {Value : Type v}
    {rows columns : Nat} (program : ADEV.Program Outcome Value rows columns) :
    (transform program).law =
      program.law.map (fun outcome => (program.primal outcome, outcome)) :=
  rfl

theorem transform_correct {Outcome : Type u} {Value : Type v}
    {rows columns : Nat} (program : ADEV.Program Outcome Value rows columns)
    (tangent : Vector columns) :
    (transform program).execute tangent ≈ₚ program.execute tangent :=
  FinitePMF.map_comp
    (fun outcome => (program.primal outcome, outcome))
    (fun sample => (sample.1, program.residual.apply sample.2 tangent))
    program.law

theorem transform_tape_marginal {Outcome : Type u} {Value : Type v}
    {rows columns : Nat} (program : ADEV.Program Outcome Value rows columns) :
    (transform program).law.marginal₂ ≈ₚ program.law := by
  exact FinitePMF.Equivalent.trans
    (FinitePMF.map_comp
      (fun outcome => (program.primal outcome, outcome)) Prod.snd program.law)
    (FinitePMF.map_id program.law)

@[simp] theorem transform_residual {Outcome : Type u} {Value : Type v}
    {rows columns : Nat} (program : ADEV.Program Outcome Value rows columns) :
    (transform program).residual = program.residual :=
  rfl

end Problib.Inference.Derivative.FirstOrder.Unzip
