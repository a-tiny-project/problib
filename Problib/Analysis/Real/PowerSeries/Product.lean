module

public import Problib.Analysis.Real.PowerSeries.Raw

/-! Products of normally convergent multivariate power series. -/

set_option autoImplicit false

namespace Problib.Analysis.Real.PowerSeries

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real.SignedSeries

noncomputable section

/-- A homogeneous finite-term series with a summable magnitude majorant
aggregates into a normally convergent canonical power series. -/
@[expose] public noncomputable def aggregateSeries {dimension : Nat}
    (terms : Nat → List (FinitePolynomial.Term dimension))
    (homogeneous : ∀ degreeValue,
      FinitePolynomial.Homogeneous degreeValue (terms degreeValue))
    (radius : selection.Carrier) (positive : lt zero radius)
    (majorant : ∀ displacement : FiniteVector.carrier dimension,
      FiniteVector.ball (FiniteVector.zeroVector dimension) radius displacement →
      Summable (fun degreeValue =>
        FinitePolynomial.magnitude (terms degreeValue) displacement)) :
    Convergent dimension where
  coefficients := aggregateCoefficients terms
  radius := radius
  radiusPositive := positive
  normalOn := by
    intro displacement inside
    let magnitudes := fun degreeValue =>
      FinitePolynomial.magnitude (terms degreeValue) displacement
    let certificate := majorant displacement inside
    refine ⟨sum magnitudes certificate, fun count => ?_⟩
    have pointwise : ∀ degreeValue,
        le (shellMagnitude (aggregateCoefficients terms)
          displacement degreeValue) (magnitudes degreeValue) :=
      fun degreeValue => shellMagnitude_aggregate_le terms homogeneous
        displacement
    have tailBound := partial_sum_le
      (fun index => pointwise (index + 1)) count
    have firstNonnegative := FinitePolynomial.magnitude_nonnegative
      (terms 0) displacement
    have included : le
        (partialSum (fun index => magnitudes (index + 1)) count)
        (partialSum magnitudes (count + 1)) := by
      rw [partial_sum_cons]
      have augmented := add_le_add firstNonnegative
        (le_refl (partialSum
          (fun index => magnitudes (index + 1)) count))
      simpa only [zero_add,
        add_comm (partialSum
          (fun index => magnitudes (index + 1)) count) (magnitudes 0)]
        using augmented
    exact le_trans tailBound
      (le_trans included
        (partial_sum_le_sum_nonnegative
          (fun degreeValue => FinitePolynomial.magnitude_nonnegative
            (terms degreeValue) displacement)
          certificate (count + 1)))

/-- Multiply every pair of canonical shell terms before collecting equal
multiindices. -/
@[expose] public noncomputable def multiplySeries {dimension : Nat}
    (first second : Convergent dimension) : Convergent dimension := by
  let witness := small_positive first.radiusPositive second.radiusPositive
  let radius := Classical.choose witness
  have radiusFacts := Classical.choose_spec witness
  refine aggregateSeries
    (rawProductTerms first.coefficients second.coefficients)
    (raw_product_homogeneous first.coefficients second.coefficients)
    radius radiusFacts.left ?_
  intro displacement inside
  have firstInside := FiniteVector.ball_mono radiusFacts.right.left inside
  have secondInside := FiniteVector.ball_mono radiusFacts.right.right inside
  have firstSummable := fullShellMagnitudes_summable first displacement
    firstInside
  have secondSummable := fullShellMagnitudes_summable second displacement
    secondInside
  have firstNonnegative : ∀ degreeValue,
      le zero (fullShellMagnitudes first displacement degreeValue) :=
    fun degreeValue => shellMagnitude_nonnegative
      first.coefficients displacement degreeValue
  have secondNonnegative : ∀ degreeValue,
      le zero (fullShellMagnitudes second displacement degreeValue) :=
    fun degreeValue => shellMagnitude_nonnegative
      second.coefficients displacement degreeValue
  have equal :
      (fun degreeValue => FinitePolynomial.magnitude
        (rawProductTerms first.coefficients second.coefficients degreeValue)
          displacement) =
      convolution (fullShellMagnitudes first displacement)
        (fullShellMagnitudes second displacement) := by
    funext degreeValue
    exact magnitude_raw_product first.coefficients second.coefficients
      displacement degreeValue
  rw [equal]
  exact convolution_summable_nonnegative firstNonnegative secondNonnegative
    firstSummable secondSummable

public theorem multiplySeries_radius_le_first {dimension : Nat}
    (first second : Convergent dimension) :
    le (multiplySeries first second).radius first.radius := by
  change le (Classical.choose
    (small_positive first.radiusPositive second.radiusPositive)) first.radius
  exact (Classical.choose_spec
    (small_positive first.radiusPositive second.radiusPositive)).right.left

public theorem multiplySeries_radius_le_second {dimension : Nat}
    (first second : Convergent dimension) :
    le (multiplySeries first second).radius second.radius := by
  change le (Classical.choose
    (small_positive first.radiusPositive second.radiusPositive)) second.radius
  exact (Classical.choose_spec
    (small_positive first.radiusPositive second.radiusPositive)).right.right

private theorem product_sum_congr {first second : Nat → selection.Carrier}
    (equal : first = second)
    (firstSummable : Summable first) (secondSummable : Summable second) :
    sum first firstSummable = sum second secondSummable := by
  cases equal
  rfl

/-- The local value of a product series is the product of the two local
values. Absolute normal convergence justifies the infinite Cauchy product. -/
public theorem multiplySeries_value {dimension : Nat}
    (first second : Convergent dimension)
    (displacement : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball (FiniteVector.zeroVector dimension)
      (multiplySeries first second).radius displacement) :
    value (multiplySeries first second) displacement inside =
      mul
        (value first displacement
          (FiniteVector.ball_mono
            (multiplySeries_radius_le_first first second) inside))
        (value second displacement
          (FiniteVector.ball_mono
            (multiplySeries_radius_le_second first second) inside)) := by
  let firstInside := FiniteVector.ball_mono
    (multiplySeries_radius_le_first first second) inside
  let secondInside := FiniteVector.ball_mono
    (multiplySeries_radius_le_second first second) inside
  let firstAbsolute := fullShellTerms_absolute first displacement firstInside
  let secondAbsolute := fullShellTerms_absolute second displacement secondInside
  let productAbsolute := fullShellTerms_absolute
    (multiplySeries first second) displacement inside
  have termsEqual : fullShellTerms (multiplySeries first second) displacement =
      convolution (fullShellTerms first displacement)
        (fullShellTerms second displacement) := by
    funext degreeValue
    change shellTerm
        (aggregateCoefficients
          (rawProductTerms first.coefficients second.coefficients))
        displacement degreeValue = _
    rw [shellTerm_aggregate _
      (raw_product_homogeneous first.coefficients second.coefficients),
      evaluate_raw_product]
    rfl
  have sumsEqual :
      sum (fullShellTerms (multiplySeries first second) displacement)
          (summable_of_absolute_bound productAbsolute) =
      sum (convolution (fullShellTerms first displacement)
        (fullShellTerms second displacement))
          (convolution_summable_absolute firstAbsolute secondAbsolute) := by
    exact product_sum_congr termsEqual _ _
  calc
    value (multiplySeries first second) displacement inside =
      sum (fullShellTerms (multiplySeries first second) displacement)
        (summable_of_absolute_bound productAbsolute) :=
      (full_shell_sum_eq_value _ _ inside).symm
    _ = sum (convolution (fullShellTerms first displacement)
          (fullShellTerms second displacement))
          (convolution_summable_absolute firstAbsolute secondAbsolute) :=
      sumsEqual
    _ = mul
          (sum (fullShellTerms first displacement)
            (summable_of_absolute_bound firstAbsolute))
          (sum (fullShellTerms second displacement)
            (summable_of_absolute_bound secondAbsolute)) :=
      sum_convolution_absolute firstAbsolute secondAbsolute
    _ = mul (value first displacement firstInside)
          (value second displacement secondInside) := by
      rw [full_shell_sum_eq_value first displacement firstInside,
        full_shell_sum_eq_value second displacement secondInside]

/-- Analytic local representations are closed under pointwise products. -/
public theorem analytic_on_mul {dimension : Nat}
    {region : FiniteVector.carrier dimension → Prop}
    {first second : FiniteVector.carrier dimension → selection.Carrier}
    (firstAnalytic : AnalyticOn region first)
    (secondAnalytic : AnalyticOn region second) :
    AnalyticOn region (fun point => mul (first point) (second point)) := by
  refine ⟨firstAnalytic.left, fun center member => ?_⟩
  rcases firstAnalytic.right center member with
    ⟨firstSeries, firstWithin, firstAgree⟩
  rcases secondAnalytic.right center member with
    ⟨secondSeries, _, secondAgree⟩
  refine ⟨multiplySeries firstSeries secondSeries, ?_, ?_⟩
  · intro point inside
    exact firstWithin point
      (FiniteVector.ball_mono
        (multiplySeries_radius_le_first firstSeries secondSeries) inside)
  · intro point inside
    have firstInside := FiniteVector.ball_mono
      (multiplySeries_radius_le_first firstSeries secondSeries) inside
    have secondInside := FiniteVector.ball_mono
      (multiplySeries_radius_le_second firstSeries secondSeries) inside
    have displacedInside : FiniteVector.ball
        (FiniteVector.zeroVector dimension)
        (multiplySeries firstSeries secondSeries).radius
        (FiniteVector.subVector point center) := by
      intro coordinate
      simpa only [FiniteVector.ball, FiniteVector.zeroVector,
        FiniteVector.subVector, sub_zero] using inside coordinate
    change mul (first point) (second point) =
      value (multiplySeries firstSeries secondSeries)
        (FiniteVector.subVector point center) displacedInside
    rw [firstAgree point firstInside, secondAgree point secondInside]
    exact (multiplySeries_value firstSeries secondSeries
      (FiniteVector.subVector point center) displacedInside).symm

/-- Natural powers of a coordinate inherit a local Taylor representation. -/
public theorem analytic_on_power_coordinate {dimension : Nat}
    {region : FiniteVector.carrier dimension → Prop}
    (openRegion : FiniteVector.IsOpen region)
    (selected : Fin dimension) (count : Nat) :
    AnalyticOn region (fun point => power (point selected) count) := by
  induction count with
  | zero =>
      simpa only [power_zero] using
        (analytic_on_constant openRegion one)
  | succ count induction =>
      have coordinate := analytic_on_coordinate openRegion selected
      have product := analytic_on_mul coordinate induction
      simpa only [power_succ] using product

end

end Problib.Analysis.Real.PowerSeries
