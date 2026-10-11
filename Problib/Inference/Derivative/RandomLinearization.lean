import Problib.Linear.Rational
import Problib.Inference.Derivative.Continuous.Integral
import Problib.Probability.Finite.Interpretation
import Problib.Real.Grind

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

end Problib.Inference.Derivative

/-! Random real linear maps.

A random linear map's coefficients are certified signed integrands under a
measure, and their means are the coefficients of its expected map `J`. Under a
probability, deterministic tangents and cotangents pass through the
expectation: `E[L v] = J v`, `E[Lᵀ c] = Jᵀ c`, and `E[⟨c, L v⟩] = ⟨Jᵀ c, v⟩`.
A finite rational linearization is one such map under its interpreted law. A
cotangent that depends on the sample does not pass through without a premise on
its mixed moments with the coefficients. -/

namespace Problib.Inference.Derivative

open Problib.Linear.Rational (Matrix)
open Problib.Real.Construction.Dedekind
open Problib.Measure Problib.Measure.Real
open Problib.Probability

universe w

/-- The real dot product, summed in index order. -/
noncomputable def realDot {dimension : Nat} (left right : Fin dimension → selection.Carrier) :
    selection.Carrier :=
  additiveLaws.listSum ((List.finRange dimension).map fun index => mul (left index) (right index))

/-- A real matrix applied to a vector. -/
noncomputable def realApply {rows columns : Nat}
    (matrix : Fin rows → Fin columns → selection.Carrier)
    (vector : Fin columns → selection.Carrier) : Fin rows → selection.Carrier :=
  fun row => realDot (matrix row) vector

/-- The transpose of a real matrix. -/
def realTranspose {rows columns : Nat} (matrix : Fin rows → Fin columns → selection.Carrier) :
    Fin columns → Fin rows → selection.Carrier :=
  fun column row => matrix row column

/-- A common left factor distributes over a listed sum. -/
private theorem mul_listSum {ι : Type} (factor : selection.Carrier) (values : ι → selection.Carrier) :
    (indices : List ι) →
      mul factor (additiveLaws.listSum (indices.map values)) =
        additiveLaws.listSum (indices.map fun index => mul factor (values index))
  | [] => mul_zero factor
  | index :: rest => by
      show mul factor (add (values index) (additiveLaws.listSum (rest.map values))) =
        add (mul factor (values index))
          (additiveLaws.listSum (rest.map fun index => mul factor (values index)))
      rw [mul_add, mul_listSum factor values rest]

/-- Pairing a cotangent with an applied matrix pairs the transposed application
with the tangent. -/
theorem realDot_apply {rows columns : Nat} (matrix : Fin rows → Fin columns → selection.Carrier)
    (cotangent : Fin rows → selection.Carrier) (tangent : Fin columns → selection.Carrier) :
    realDot cotangent (realApply matrix tangent) =
      realDot (realApply (realTranspose matrix) cotangent) tangent := by
  simp only [realDot, realApply, realTranspose]
  rw [List.map_congr_left fun row _ =>
      mul_listSum (cotangent row) (fun column => mul (matrix row column) (tangent column))
        (List.finRange columns),
    Problib.Algebra.AdditiveCommutativeMonoidLaws.listSum_comm]
  apply congrArg additiveLaws.listSum
  apply List.map_congr_left
  intro column _
  rw [mul_comm _ (tangent column), mul_listSum]
  apply congrArg additiveLaws.listSum
  apply List.map_congr_left
  intro row _
  real_grind

/-- A random real linear map under a measure. Every coefficient is a certified
signed integrand, so it is measurable and absolutely integrable, and its mean is
the matching coefficient of the expected map. -/
structure RandomLinearMap {Outcome : Type w} {space : Space Outcome} (measure : Measure space)
    (rows columns : Nat) where
  coefficient : Outcome → Fin rows → Fin columns → selection.Carrier
  expected : Fin rows → Fin columns → selection.Carrier
  integrable : ∀ row column,
    HasRealIntegral measure (fun outcome => coefficient outcome row column) (expected row column)

namespace RandomLinearMap

variable {Outcome : Type w} {space : Space Outcome} {measure : Measure space} {rows columns : Nat}

/-- The transposed map, whose expected map is the transpose. -/
def transpose (map : RandomLinearMap measure rows columns) : RandomLinearMap measure columns rows where
  coefficient outcome := realTranspose (map.coefficient outcome)
  expected := realTranspose map.expected
  integrable column row := map.integrable row column

/-- A certified integral scales by a constant on the right. -/
private theorem mul_right {integrand : Outcome → selection.Carrier} {value : selection.Carrier}
    (integral : HasRealIntegral measure integrand value) (scalar : selection.Carrier) :
    HasRealIntegral measure (fun outcome => mul (integrand outcome) scalar) (mul value scalar) := by
  have scaled := integral.smul scalar
  rw [mul_comm scalar value] at scaled
  exact scaled.congr fun outcome => mul_comm scalar (integrand outcome)

/-- A deterministic tangent passes through the expectation: `E[L v] = J v`. -/
theorem apply_mean (map : RandomLinearMap measure rows columns)
    (probability : Measure.IsProbability measure) (tangent : Fin columns → selection.Carrier)
    (row : Fin rows) :
    HasRealIntegral measure (fun outcome => realApply (map.coefficient outcome) tangent row)
      (realApply map.expected tangent row) :=
  HasRealIntegral.listSum probability
    (fun column => mul_right (map.integrable row column) (tangent column)) (List.finRange columns)

/-- A deterministic cotangent passes through the expectation: `E[Lᵀ c] = Jᵀ c`. -/
theorem transposeApply_mean (map : RandomLinearMap measure rows columns)
    (probability : Measure.IsProbability measure) (cotangent : Fin rows → selection.Carrier)
    (column : Fin columns) :
    HasRealIntegral measure
      (fun outcome => realApply (realTranspose (map.coefficient outcome)) cotangent column)
      (realApply (realTranspose map.expected) cotangent column) :=
  map.transpose.apply_mean probability cotangent column

/-- The sampled pairing of a deterministic cotangent with a deterministic
tangent has the expected map's transposed pairing as its mean:
`E[⟨c, L v⟩] = ⟨Jᵀ c, v⟩`. -/
theorem dot_mean (map : RandomLinearMap measure rows columns)
    (probability : Measure.IsProbability measure) (cotangent : Fin rows → selection.Carrier)
    (tangent : Fin columns → selection.Carrier) :
    HasRealIntegral measure
      (fun outcome => realDot cotangent (realApply (map.coefficient outcome) tangent))
      (realDot (realApply (realTranspose map.expected) cotangent) tangent) := by
  rw [← realDot_apply]
  exact HasRealIntegral.listSum probability
    (fun row => (map.apply_mean probability tangent row).smul (cotangent row))
    (List.finRange rows)

end RandomLinearMap

/-- A finite rational table integrates the real image of an observable to the
real image of its expectation. -/
theorem hasRealIntegral_toMeasure_ofRat {Outcome : Type w} (table : FiniteMeasure Outcome)
    (observable : Outcome → Rat) :
    HasRealIntegral (table.toMeasure (Space.discrete Outcome))
      (fun outcome => selection.ofRat (observable outcome))
      (selection.ofRat (table.expectation observable)) := by
  cases table with
  | mk weights =>
      induction weights with
      | nil =>
          have vanishes := zero_hasRealIntegral
            (MeasurableMap.from_discrete borel fun outcome => selection.ofRat (observable outcome))
          rw [← ofRat_zero] at vanishes
          exact vanishes
      | cons head rest induction =>
          cases head with
          | mk value weight =>
              have point := smul_hasRealIntegral
                (Measure.dirac (Space.discrete Outcome) value) _
                (Problib.Real.NNReal.ofRat weight.val weight.nonnegative)
                (Continuous.hasRealIntegral_dirac (Space.discrete Outcome) value
                  (MeasurableMap.from_discrete borel fun outcome =>
                    selection.ofRat (observable outcome)))
              have split : selection.ofRat
                    ((FiniteMeasure.mk ((value, weight) :: rest)).expectation observable) =
                  add (mul (Problib.Real.NNReal.ofRat weight.val weight.nonnegative).toReal
                      (selection.ofRat (observable value)))
                    (selection.ofRat ((FiniteMeasure.mk rest).expectation observable)) := by
                show selection.ofRat (weight.val * observable value +
                    (FiniteMeasure.mk rest).expectation observable) = _
                rw [ofRat_add, ofRat_mul]
                rfl
              rw [split]
              exact add_hasRealIntegral point induction

/-- A finite rational linearization is a random real linear map under its
interpreted law, whose expected map is the real image of its target. -/
noncomputable def RandomLinearization.toRandomLinearMap {Outcome : Type w} {rows columns : Nat}
    {target : Matrix rows columns} (linearization : RandomLinearization Outcome rows columns target) :
    RandomLinearMap (linearization.law.measure.toMeasure (Space.discrete Outcome)) rows columns where
  coefficient outcome row column := selection.ofRat (linearization.estimate outcome row column)
  expected row column := selection.ofRat (target row column)
  integrable row column := by
    show HasRealIntegral _ (fun outcome => selection.ofRat (linearization.estimate outcome row column))
      (selection.ofRat (target row column))
    rw [← congrFun (congrFun linearization.coefficientwiseUnbiased row) column]
    exact hasRealIntegral_toMeasure_ofRat linearization.law.measure _

/-- The interpreted law of a finite linearization is a probability. -/
theorem RandomLinearization.law_isProbability {Outcome : Type w} {rows columns : Nat}
    {target : Matrix rows columns} (linearization : RandomLinearization Outcome rows columns target) :
    Measure.IsProbability (linearization.law.measure.toMeasure (Space.discrete Outcome)) :=
  FiniteMeasure.toMeasure_isProbability _ _ linearization.law.total_one

end Problib.Inference.Derivative
