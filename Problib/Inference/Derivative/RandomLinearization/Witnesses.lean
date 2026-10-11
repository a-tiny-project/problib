import Problib.Inference.Derivative.RandomLinearization
import Problib.Inference.Derivative.Continuous.Interchange
import Problib.Inference.Derivative.Source.Affine

set_option autoImplicit false

/-! Witnesses for random real linear maps.

The real images of the finite linearization theorems are instances of the
general mean theorems under the interpreted law, and the affine source family's
expected correctness reads as a continuous estimate. A cotangent drawn from the
same sample as the coefficients does not pass through the expectation: with the
fair coin's sign as both coefficient and cotangent, each factor has mean zero,
yet the transposed application has mean one. -/

namespace Problib.Inference.Derivative.RandomLinearMap

open Problib.Linear.Rational (Matrix)
open Problib.Real.Construction.Dedekind
open Problib.Measure
open Continuous.Coupling (seed)
open Continuous.Correlated (sign sign_mean product_mean)

universe u

/-- The real image of `tangent_unbiased_finite`: `E[L v] = J v` for a real
tangent. -/
example {Outcome : Type u} {rows columns : Nat} {target : Matrix rows columns}
    (linearization : RandomLinearization Outcome rows columns target)
    (tangent : Fin columns → selection.Carrier) (row : Fin rows) :
    HasRealIntegral (linearization.law.measure.toMeasure (Space.discrete Outcome))
      (fun outcome => realApply
        (fun row column => selection.ofRat (linearization.estimate outcome row column)) tangent row)
      (realApply (fun row column => selection.ofRat (target row column)) tangent row) :=
  linearization.toRandomLinearMap.apply_mean linearization.law_isProbability tangent row

/-- The real image of `transpose_unbiased_finite`: `E[Lᵀ c] = Jᵀ c` for a real
cotangent. -/
example {Outcome : Type u} {rows columns : Nat} {target : Matrix rows columns}
    (linearization : RandomLinearization Outcome rows columns target)
    (cotangent : Fin rows → selection.Carrier) (column : Fin columns) :
    HasRealIntegral (linearization.law.measure.toMeasure (Space.discrete Outcome))
      (fun outcome => realApply (realTranspose
        fun row column => selection.ofRat (linearization.estimate outcome row column)) cotangent column)
      (realApply (realTranspose fun row column => selection.ofRat (target row column))
        cotangent column) :=
  linearization.toRandomLinearMap.transposeApply_mean linearization.law_isProbability cotangent column

/-- The real image of the scalar gradient: the scalar seed's transposed
application is unbiased for the gradient. -/
example {Outcome : Type u} {columns : Nat} {target : Matrix 1 columns}
    (linearization : RandomLinearization Outcome 1 columns target) (column : Fin columns) :
    HasRealIntegral (linearization.law.measure.toMeasure (Space.discrete Outcome))
      (fun outcome => realApply (realTranspose
        fun row column => selection.ofRat (linearization.estimate outcome row column))
        (fun _ => one) column)
      (realApply (realTranspose fun row column => selection.ofRat (target row column))
        (fun _ => one) column) :=
  linearization.toRandomLinearMap.transposeApply_mean linearization.law_isProbability
    (fun _ => one) column

/-- The affine source family's expected correctness, read under each
direction's interpreted law, estimates the real images of its primal and
directional derivative. -/
example (point slope offset : Rat) (direction : Problib.Linear.Rational.Vector 1) :
    Continuous.Estimates
      ((Source.Affine.term.directionalExecution
        (Source.Affine.target point slope offset) direction).measure.toMeasure
          (Space.discrete _))
      (fun sample => selection.ofRat sample.2.1)
      (fun sample => selection.ofRat (sample.2.2 0))
      (selection.ofRat (slope * point + offset))
      (selection.ofRat (Matrix.apply (Source.Affine.jacobian slope) direction 0)) :=
  (Source.Affine.expected point slope offset).estimates direction

/-- The fair coin's sign as a `1 × 1` random map, whose expected map is zero. -/
noncomputable def signMap : RandomLinearMap seed 1 1 where
  coefficient outcome _ _ := sign outcome
  expected _ _ := zero
  integrable _ _ := sign_mean

/-- A cotangent drawn from the coefficient's own sample does not pass through
the expectation. With the sign as cotangent, `E[Lᵀ c]` is one, while the
expected map's transpose applied to `E[c] = 0` is zero. -/
theorem sampled_cotangent_biased :
    HasRealIntegral seed (fun outcome =>
        realApply (realTranspose (signMap.coefficient outcome)) (fun _ => sign outcome) 0) one ∧
      ¬HasRealIntegral seed (fun outcome =>
          realApply (realTranspose (signMap.coefficient outcome)) (fun _ => sign outcome) 0)
        (realApply (realTranspose signMap.expected) (fun _ => zero) 0) := by
  have sampled : HasRealIntegral seed (fun outcome =>
      realApply (realTranspose (signMap.coefficient outcome)) (fun _ => sign outcome) 0) one :=
    product_mean.congr fun outcome => by
      show mul (sign outcome) (sign outcome) = add (mul (sign outcome) (sign outcome)) zero
      rw [add_zero]
  refine ⟨sampled, fun wrong => ?_⟩
  have equal := sampled.unique wrong
  have vanishes : realApply (realTranspose signMap.expected) (fun _ => zero) 0 = zero := by
    show add (mul zero zero) zero = zero
    rw [mul_zero, add_zero]
  rw [vanishes] at equal
  exact one_ne_zero equal

end Problib.Inference.Derivative.RandomLinearMap
