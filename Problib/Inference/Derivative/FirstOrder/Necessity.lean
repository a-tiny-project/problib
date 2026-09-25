import Problib.Probability.Finite.Example
import Problib.Inference.Derivative.FirstOrder.Pipeline

set_option autoImplicit false

namespace Problib.Inference.Derivative.FirstOrder.Necessity

open Problib.Linear.Rational
open Problib.Probability
open Problib.Probability.FiniteExample

universe u

/-- Expectation-level directional correctness without a matrix or linearity
premise. This is intentionally weaker than `ADEV.Program.JVPUnbiased`. -/
def DirectionallyUnbiased {Outcome : Type u} {rows columns : Nat}
    (law : FinitePMF Outcome)
    (estimate : Outcome → Vector columns → Vector rows)
    (target : Matrix rows columns) : Prop :=
  ∀ tangent, expectedVector law (fun outcome => estimate outcome tangent) =
    Matrix.apply target tangent

abbrev coordinate : Fin 1 :=
  ⟨0, by decide⟩

abbrev identity : Matrix 1 1 :=
  fun _ _ => 1

def nonlinearResidual : Bool → Vector 1 → Vector 1
  | false => fun tangent _ => tangent coordinate + tangent coordinate * tangent coordinate
  | true => fun tangent _ => tangent coordinate - tangent coordinate * tangent coordinate

private theorem fair_average_quadratic_cancel (value : Rat) :
    (half : Rat) * (value + value * value) +
        (half : Rat) * (value - value * value) = value := by
  rw [← Rat.mul_add]
  have cancel :
      (value + value * value) + (value - value * value) = value + value := by
    simp [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_left_comm,
      Rat.add_neg_cancel, Rat.add_zero]
  rw [cancel]
  have twoTimes : value + value = (2 : Rat) * value := by
    calc
      value + value = (1 : Rat) * value + (1 : Rat) * value := by
        simp only [Rat.one_mul]
      _ = ((1 : Rat) + 1) * value := (Rat.add_mul 1 1 value).symm
      _ = (2 : Rat) * value :=
        congrArg (fun coefficient : Rat => coefficient * value)
          (Rat.natCast_add 1 1).symm
  rw [twoTimes, ← Rat.mul_assoc, half_rat_mul_two, Rat.one_mul]

theorem nonlinear_residual_directionally_unbiased :
    DirectionallyUnbiased fairCoin nonlinearResidual identity := by
  intro tangent
  apply Problib.Linear.Rational.Vector.ext
  intro row
  change fairCoin.expectation
      (fun outcome => nonlinearResidual outcome tangent row) =
    finSum (fun column : Fin 1 => identity row column * tangent column)
  rw [fairCoin_expectation, finSum_one_dimension]
  change
    (half : Rat) * (tangent coordinate + tangent coordinate * tangent coordinate) +
        (half : Rat) * (tangent coordinate - tangent coordinate * tangent coordinate) =
      1 * tangent coordinate
  rw [Rat.one_mul]
  exact fair_average_quadratic_cancel (tangent coordinate)

def unitTangent : Vector 1 :=
  fun _ => 1

theorem nonlinear_residual_is_not_samplewise_additive :
    ∀ outcome,
      nonlinearResidual outcome
          (Problib.Linear.Rational.Vector.add unitTangent unitTangent) ≠
        Problib.Linear.Rational.Vector.add
          (nonlinearResidual outcome unitTangent)
          (nonlinearResidual outcome unitTangent) := by
  intro outcome equal
  have atCoordinate := congrFun equal coordinate
  cases outcome
  · simp only [nonlinearResidual, unitTangent,
      Problib.Linear.Rational.Vector.add] at atCoordinate
    have oneAddOne : (1 : Rat) + 1 = 2 := (Rat.natCast_add 1 1).symm
    simp only [Rat.one_mul] at atCoordinate
    rw [oneAddOne] at atCoordinate
    have productEqual : (2 : Rat) * 2 = 2 :=
      Rat.add_left_cancel 2 atCoordinate
    have fourEqualTwo : (4 : Rat) = 2 :=
      (Rat.natCast_mul 2 2).trans productEqual
    exact (by decide : (4 : Rat) ≠ 2) fourEqualTwo
  · simp only [nonlinearResidual, unitTangent,
      Problib.Linear.Rational.Vector.add] at atCoordinate
    have oneAddOne : (1 : Rat) + 1 = 2 := (Rat.natCast_add 1 1).symm
    simp only [Rat.one_mul] at atCoordinate
    rw [oneAddOne, Rat.sub_self, Rat.zero_add] at atCoordinate
    have twoMulTwo : (2 : Rat) * 2 = 4 := (Rat.natCast_mul 2 2).symm
    rw [twoMulTwo] at atCoordinate
    have shifted := congrArg (fun value : Rat => value + 4) atCoordinate
    rw [Rat.sub_add_cancel, Rat.zero_add] at shifted
    exact (by decide : (2 : Rat) ≠ 4) shifted

theorem nonlinear_residual_not_representable :
    ¬∃ residual : Linear.Program Bool 1 1,
      ∀ outcome tangent, residual.apply outcome tangent =
        nonlinearResidual outcome tangent := by
  intro represented
  obtain ⟨residual, representation⟩ := represented
  have additive := residual.apply_add false unitTangent unitTangent
  rw [representation false
      (Problib.Linear.Rational.Vector.add unitTangent unitTangent),
    representation false unitTangent] at additive
  exact nonlinear_residual_is_not_samplewise_additive false additive

theorem fixed_law_all_direction_unbiasedness_is_insufficient :
    DirectionallyUnbiased fairCoin nonlinearResidual identity ∧
      (∀ outcome,
        nonlinearResidual outcome
            (Problib.Linear.Rational.Vector.add unitTangent unitTangent) ≠
          Problib.Linear.Rational.Vector.add
            (nonlinearResidual outcome unitTangent)
            (nonlinearResidual outcome unitTangent)) ∧
      (¬∃ residual : Linear.Program Bool 1 1,
        ∀ outcome tangent, residual.apply outcome tangent =
          nonlinearResidual outcome tangent) :=
  ⟨nonlinear_residual_directionally_unbiased,
    nonlinear_residual_is_not_samplewise_additive,
    nonlinear_residual_not_representable⟩

end Problib.Inference.Derivative.FirstOrder.Necessity
