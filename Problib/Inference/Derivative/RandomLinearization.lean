import Problib.Linear.Rational

set_option autoImplicit false

namespace Problib.Inference.Derivative

open Problib.Linear.Rational
open Problib.Probability

universe u

structure RandomLinearization (Outcome : Type u) (rows columns : Nat)
    (target : Matrix rows columns) where
  law : FinitePMF Outcome
  estimate : Outcome → Matrix rows columns
  coefficientwiseUnbiased : CoefficientwiseUnbiased law estimate target

def RandomLinearization.tangentEstimator
    {Outcome : Type u} {rows columns : Nat} {target : Matrix rows columns}
    (linearization : RandomLinearization Outcome rows columns target)
    (tangent : Vector columns) : Outcome → Vector rows :=
  fun outcome => Matrix.apply (linearization.estimate outcome) tangent

theorem RandomLinearization.tangentEstimator_add
    {Outcome : Type u} {rows columns : Nat} {target : Matrix rows columns}
    (linearization : RandomLinearization Outcome rows columns target)
    (left right : Vector columns) (outcome : Outcome) :
    linearization.tangentEstimator
        (Problib.Linear.Rational.Vector.add left right) outcome =
      Problib.Linear.Rational.Vector.add
        (linearization.tangentEstimator left outcome)
        (linearization.tangentEstimator right outcome) :=
  Matrix.apply_add (linearization.estimate outcome) left right

theorem RandomLinearization.tangentEstimator_scale
    {Outcome : Type u} {rows columns : Nat} {target : Matrix rows columns}
    (linearization : RandomLinearization Outcome rows columns target)
    (constant : Rat) (tangent : Vector columns) (outcome : Outcome) :
    linearization.tangentEstimator
        (Problib.Linear.Rational.Vector.scale constant tangent) outcome =
      Problib.Linear.Rational.Vector.scale constant
        (linearization.tangentEstimator tangent outcome) :=
  Matrix.apply_scale (linearization.estimate outcome) constant tangent

theorem RandomLinearization.tangent_unbiased_finite
    {Outcome : Type u} {rows columns : Nat} {target : Matrix rows columns}
    (linearization : RandomLinearization Outcome rows columns target) :
    JVPUnbiased linearization.law linearization.estimate target :=
  coefficientwise_implies_jvp linearization.coefficientwiseUnbiased

theorem RandomLinearization.transpose_unbiased_finite
    {Outcome : Type u} {rows columns : Nat} {target : Matrix rows columns}
    (linearization : RandomLinearization Outcome rows columns target) :
    VJPUnbiased linearization.law linearization.estimate target :=
  jvp_implies_vjp linearization.tangent_unbiased_finite

theorem RandomLinearization.scalar_gradient_unbiased_finite
    {Outcome : Type u} {columns : Nat} {target : Matrix 1 columns}
    (linearization : RandomLinearization Outcome 1 columns target) :
    expectedVector linearization.law
        (fun outcome => gradient (linearization.estimate outcome)) =
      gradient target :=
  jvp_implies_gradient linearization.tangent_unbiased_finite

end Problib.Inference.Derivative
