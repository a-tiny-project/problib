import Foundations.Linear.Rational.Matrix
import Foundations.Probability.Finite.Expectation

namespace Foundations.Linear.Rational

open Foundations.Probability

universe u v

theorem expectation_listSum {Ω : Type u} {Index : Type v}
    (law : FinitePMF Ω) (indices : List Index) (observable : Index → Ω → Rat) :
    law.expectation (fun outcome => listSum indices fun index => observable index outcome) =
      listSum indices fun index => law.expectation (observable index) := by
  induction indices with
  | nil =>
      change law.expectation (fun _ => 0) = 0
      exact FinitePMF.expectation_zero law
  | cons head tail ih =>
      change law.expectation (fun outcome =>
          listSum tail fun index => observable index outcome) =
        listSum tail fun index => law.expectation (observable index) at ih
      change law.expectation (fun outcome =>
          observable head outcome + listSum tail fun index => observable index outcome) =
        law.expectation (observable head) +
          listSum tail fun index => law.expectation (observable index)
      rw [FinitePMF.expectation_add, ih]

theorem expectation_finSum {Ω : Type u} {n : Nat}
    (law : FinitePMF Ω) (observable : Fin n → Ω → Rat) :
    law.expectation (fun outcome => finSum fun index => observable index outcome) =
      finSum fun index => law.expectation (observable index) :=
  expectation_listSum law (List.finRange n) observable

@[reducible] def expectedVector {Ω : Type u} {dimension : Nat}
    (law : FinitePMF Ω) (estimate : Ω → Vector dimension) : Vector dimension :=
  fun index => law.expectation fun outcome => estimate outcome index

theorem expectedVector_equivalent {Ω : Type u} {dimension : Nat}
    {left right : FinitePMF Ω} (equivalent : left ≈ₚ right)
    (estimate : Ω → Vector dimension) :
    expectedVector left estimate = expectedVector right estimate := by
  apply Foundations.Linear.Rational.Vector.ext
  intro index
  exact equivalent.expectation_eq fun outcome => estimate outcome index

@[reducible] def expectedMatrix {Ω : Type u} {rows columns : Nat}
    (law : FinitePMF Ω) (estimate : Ω → Matrix rows columns) : Matrix rows columns :=
  fun row column => law.expectation fun outcome => estimate outcome row column

theorem expected_apply {Ω : Type u} {rows columns : Nat}
    (law : FinitePMF Ω) (estimate : Ω → Matrix rows columns)
    (tangent : Vector columns) :
    expectedVector law (fun outcome => Matrix.apply (estimate outcome) tangent) =
      Matrix.apply (expectedMatrix law estimate) tangent := by
  apply Vector.ext
  intro row
  calc
    law.expectation (fun outcome =>
        finSum fun column => estimate outcome row column * tangent column) =
        finSum (fun column =>
          law.expectation fun outcome => estimate outcome row column * tangent column) :=
      expectation_finSum law fun column outcome => estimate outcome row column * tangent column
    _ = finSum (fun column =>
        law.expectation (fun outcome => estimate outcome row column) * tangent column) := by
          apply finSum_congr
          intro column
          calc
            law.expectation (fun outcome => estimate outcome row column * tangent column) =
                law.expectation (fun outcome => tangent column * estimate outcome row column) := by
                  apply FinitePMF.expectation_congr
                  intro outcome
                  exact Rat.mul_comm _ _
            _ = tangent column *
                law.expectation (fun outcome => estimate outcome row column) :=
              FinitePMF.expectation_scale law (tangent column)
                (fun outcome => estimate outcome row column)
            _ = law.expectation (fun outcome => estimate outcome row column) * tangent column :=
              Rat.mul_comm _ _
    _ = _ := rfl

theorem expected_transposeApply {Ω : Type u} {rows columns : Nat}
    (law : FinitePMF Ω) (estimate : Ω → Matrix rows columns)
    (cotangent : Vector rows) :
    expectedVector law (fun outcome => Matrix.transposeApply (estimate outcome) cotangent) =
      Matrix.transposeApply (expectedMatrix law estimate) cotangent := by
  exact expected_apply law (fun outcome => Matrix.transpose (estimate outcome)) cotangent

def CoefficientwiseUnbiased {Ω : Type u} {rows columns : Nat}
    (law : FinitePMF Ω) (estimate : Ω → Matrix rows columns)
    (target : Matrix rows columns) : Prop :=
  expectedMatrix law estimate = target

def JVPUnbiased {Ω : Type u} {rows columns : Nat}
    (law : FinitePMF Ω) (estimate : Ω → Matrix rows columns)
    (target : Matrix rows columns) : Prop :=
  ∀ tangent, expectedVector law (fun outcome => Matrix.apply (estimate outcome) tangent) =
    Matrix.apply target tangent

def VJPUnbiased {Ω : Type u} {rows columns : Nat}
    (law : FinitePMF Ω) (estimate : Ω → Matrix rows columns)
    (target : Matrix rows columns) : Prop :=
  ∀ cotangent,
    expectedVector law (fun outcome => Matrix.transposeApply (estimate outcome) cotangent) =
      Matrix.transposeApply target cotangent

def RandomCotangentVJPUnbiased {Ω : Type u} {rows columns : Nat}
    (law : FinitePMF Ω) (estimate : Ω → Matrix rows columns)
    (target : Matrix rows columns) (cotangent : Ω → Vector rows) : Prop :=
  expectedVector law (fun outcome =>
      Matrix.transposeApply (estimate outcome) (cotangent outcome)) =
    Matrix.transposeApply target (expectedVector law cotangent)

def CoefficientCotangentMomentsFactorize {Ω : Type u} {rows columns : Nat}
    (law : FinitePMF Ω) (estimate : Ω → Matrix rows columns)
    (cotangent : Ω → Vector rows) : Prop :=
  ∀ row column,
    law.expectation (fun outcome => estimate outcome row column * cotangent outcome row) =
      law.expectation (fun outcome => estimate outcome row column) *
        law.expectation (fun outcome => cotangent outcome row)

theorem coefficientwise_implies_jvp {Ω : Type u} {rows columns : Nat}
    {law : FinitePMF Ω} {estimate : Ω → Matrix rows columns}
    {target : Matrix rows columns}
    (unbiased : CoefficientwiseUnbiased law estimate target) :
    JVPUnbiased law estimate target := by
  intro tangent
  rw [expected_apply, unbiased]

theorem jvp_implies_coefficientwise {Ω : Type u} {rows columns : Nat}
    {law : FinitePMF Ω} {estimate : Ω → Matrix rows columns}
    {target : Matrix rows columns}
    (unbiased : JVPUnbiased law estimate target) :
    CoefficientwiseUnbiased law estimate target := by
  apply Matrix.ext
  intro row column
  have coordinate := congrFun (unbiased (Vector.basis column)) row
  calc
    expectedMatrix law estimate row column =
        law.expectation (fun outcome =>
          Matrix.apply (estimate outcome) (Vector.basis column) row) := by
            apply FinitePMF.expectation_congr
            intro outcome
            exact (Matrix.apply_basis (estimate outcome) column row).symm
    _ = Matrix.apply target (Vector.basis column) row := coordinate
    _ = target row column := Matrix.apply_basis target column row

theorem coefficientwise_implies_vjp {Ω : Type u} {rows columns : Nat}
    {law : FinitePMF Ω} {estimate : Ω → Matrix rows columns}
    {target : Matrix rows columns}
    (unbiased : CoefficientwiseUnbiased law estimate target) :
    VJPUnbiased law estimate target := by
  intro cotangent
  rw [expected_transposeApply, unbiased]

theorem jvp_implies_vjp {Ω : Type u} {rows columns : Nat}
    {law : FinitePMF Ω} {estimate : Ω → Matrix rows columns}
    {target : Matrix rows columns}
    (unbiased : JVPUnbiased law estimate target) :
    VJPUnbiased law estimate target :=
  coefficientwise_implies_vjp (jvp_implies_coefficientwise unbiased)

theorem coefficientwise_implies_random_cotangent_vjp
    {Ω : Type u} {rows columns : Nat}
    {law : FinitePMF Ω} {estimate : Ω → Matrix rows columns}
    {target : Matrix rows columns} {cotangent : Ω → Vector rows}
    (unbiased : CoefficientwiseUnbiased law estimate target)
    (moments : CoefficientCotangentMomentsFactorize law estimate cotangent) :
    RandomCotangentVJPUnbiased law estimate target cotangent := by
  apply Vector.ext
  intro column
  calc
    expectedVector law (fun outcome =>
        Matrix.transposeApply (estimate outcome) (cotangent outcome)) column =
        law.expectation (fun outcome =>
          finSum fun row => estimate outcome row column * cotangent outcome row) := rfl
    _ = finSum (fun row =>
        law.expectation (fun outcome =>
          estimate outcome row column * cotangent outcome row)) :=
      expectation_finSum law fun row outcome =>
        estimate outcome row column * cotangent outcome row
    _ = finSum (fun row =>
        law.expectation (fun outcome => estimate outcome row column) *
          law.expectation (fun outcome => cotangent outcome row)) := by
      apply finSum_congr
      intro row
      exact moments row column
    _ = finSum (fun row =>
        target row column * law.expectation (fun outcome => cotangent outcome row)) := by
      apply finSum_congr
      intro row
      have coefficient := congrFun (congrFun unbiased row) column
      exact congrArg
        (fun value => value * law.expectation (fun outcome => cotangent outcome row))
        coefficient
    _ = Matrix.transposeApply target (expectedVector law cotangent) column := rfl

theorem jvp_implies_random_cotangent_vjp
    {Ω : Type u} {rows columns : Nat}
    {law : FinitePMF Ω} {estimate : Ω → Matrix rows columns}
    {target : Matrix rows columns} {cotangent : Ω → Vector rows}
    (unbiased : JVPUnbiased law estimate target)
    (moments : CoefficientCotangentMomentsFactorize law estimate cotangent) :
    RandomCotangentVJPUnbiased law estimate target cotangent :=
  coefficientwise_implies_random_cotangent_vjp
    (jvp_implies_coefficientwise unbiased) moments

@[reducible] def scalarSeed : Vector 1 :=
  fun _ => 1

@[reducible] def gradient {columns : Nat} (jacobian : Matrix 1 columns) : Vector columns :=
  Matrix.transposeApply jacobian scalarSeed

theorem coefficientwise_implies_gradient {Ω : Type u} {columns : Nat}
    {law : FinitePMF Ω} {estimate : Ω → Matrix 1 columns}
    {target : Matrix 1 columns}
    (unbiased : CoefficientwiseUnbiased law estimate target) :
    expectedVector law (fun outcome => gradient (estimate outcome)) = gradient target :=
  coefficientwise_implies_vjp unbiased scalarSeed

theorem jvp_implies_gradient {Ω : Type u} {columns : Nat}
    {law : FinitePMF Ω} {estimate : Ω → Matrix 1 columns}
    {target : Matrix 1 columns}
    (unbiased : JVPUnbiased law estimate target) :
    expectedVector law (fun outcome => gradient (estimate outcome)) = gradient target :=
  jvp_implies_vjp unbiased scalarSeed

end Foundations.Linear.Rational
