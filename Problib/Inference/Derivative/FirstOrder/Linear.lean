import Problib.Linear.Rational

set_option autoImplicit false

namespace Problib.Inference.Derivative.FirstOrder.Linear

open Problib.Linear.Rational

universe u

/-- A finite, sample-free linear residual. Coefficients may inspect the
nonlinear environment, but the linear input is available only to `apply`. -/
inductive Program (Environment : Type u) : Nat → Nat → Type u
  | zero (rows columns : Nat) : Program Environment rows columns
  | coordinate {rows columns : Nat}
      (coefficient : Environment → Rat)
      (row : Fin rows) (column : Fin columns) : Program Environment rows columns
  | add {rows columns : Nat}
      (left right : Program Environment rows columns) : Program Environment rows columns
  | compose {rows middle columns : Nat}
      (outer : Program Environment rows middle)
      (inner : Program Environment middle columns) : Program Environment rows columns

def Program.denote {Environment : Type u} {rows columns : Nat}
    (program : Program Environment rows columns) (environment : Environment) :
    Matrix rows columns :=
  match program with
  | .zero _ _ => Matrix.zero rows columns
  | .coordinate coefficient targetRow targetColumn =>
      fun row column =>
        if row = targetRow then
          if column = targetColumn then coefficient environment else 0
        else
          0
  | .add left right =>
      fun row column =>
        left.denote environment row column + right.denote environment row column
  | .compose outer inner =>
      fun row column => finSum fun middle =>
        outer.denote environment row middle * inner.denote environment middle column

def Program.apply {Environment : Type u} {rows columns : Nat}
    (program : Program Environment rows columns) (environment : Environment)
    (input : Vector columns) : Vector rows :=
  Matrix.apply (program.denote environment) input

def Program.transpose {Environment : Type u} {rows columns : Nat}
    (program : Program Environment rows columns) : Program Environment columns rows :=
  match program with
  | .zero rows columns => .zero columns rows
  | .coordinate coefficient row column => .coordinate coefficient column row
  | .add left right => .add left.transpose right.transpose
  | .compose outer inner => .compose inner.transpose outer.transpose

theorem Program.denote_transpose {Environment : Type u} {rows columns : Nat}
    (program : Program Environment rows columns) (environment : Environment) :
    program.transpose.denote environment = Matrix.transpose (program.denote environment) := by
  induction program with
  | zero rows columns =>
      rfl
  | coordinate coefficient targetRow targetColumn =>
      apply Matrix.ext
      intro column row
      by_cases columnEqual : column = targetColumn
      · subst column
        by_cases rowEqual : row = targetRow <;> simp [Program.transpose, Program.denote, rowEqual]
      · by_cases rowEqual : row = targetRow <;>
          simp [Program.transpose, Program.denote, columnEqual, rowEqual]
  | add left right leftInduction rightInduction =>
      apply Matrix.ext
      intro column row
      change
        left.transpose.denote environment column row +
            right.transpose.denote environment column row =
          left.denote environment row column + right.denote environment row column
      rw [leftInduction, rightInduction]
  | compose outer inner outerInduction innerInduction =>
      apply Matrix.ext
      intro column row
      change
        finSum (fun middle =>
            inner.transpose.denote environment column middle *
              outer.transpose.denote environment middle row) =
          finSum (fun middle =>
            outer.denote environment row middle * inner.denote environment middle column)
      rw [outerInduction, innerInduction]
      apply finSum_congr
      intro middle
      exact Rat.mul_comm _ _

@[simp] theorem Program.transpose_involution
    {Environment : Type u} {rows columns : Nat}
    (program : Program Environment rows columns) :
    program.transpose.transpose = program := by
  induction program with
  | zero rows columns => rfl
  | coordinate coefficient row column => rfl
  | add left right leftInduction rightInduction =>
      simp only [Program.transpose, leftInduction, rightInduction]
  | compose outer inner outerInduction innerInduction =>
      simp only [Program.transpose, outerInduction, innerInduction]

theorem Program.apply_add {Environment : Type u} {rows columns : Nat}
    (program : Program Environment rows columns) (environment : Environment)
    (left right : Vector columns) :
    program.apply environment
        (Problib.Linear.Rational.Vector.add left right) =
      Problib.Linear.Rational.Vector.add
        (program.apply environment left) (program.apply environment right) :=
  Matrix.apply_add (program.denote environment) left right

theorem Program.apply_scale {Environment : Type u} {rows columns : Nat}
    (program : Program Environment rows columns) (environment : Environment)
    (constant : Rat) (input : Vector columns) :
    program.apply environment
        (Problib.Linear.Rational.Vector.scale constant input) =
      Problib.Linear.Rational.Vector.scale constant
        (program.apply environment input) :=
  Matrix.apply_scale (program.denote environment) constant input

theorem Program.transpose_adjoint {Environment : Type u} {rows columns : Nat}
    (program : Program Environment rows columns) (environment : Environment)
    (input : Vector columns) (cotangent : Vector rows) :
    Vector.dot (program.apply environment input) cotangent =
      Vector.dot input (program.transpose.apply environment cotangent) := by
  rw [Program.apply, Program.apply, Program.denote_transpose]
  exact Matrix.transpose_adjoint (program.denote environment) input cotangent

end Problib.Inference.Derivative.FirstOrder.Linear
