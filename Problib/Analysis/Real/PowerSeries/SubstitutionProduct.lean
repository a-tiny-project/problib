module

public import Problib.Analysis.Real.PowerSeries.Product
public import Problib.Analysis.Real.PowerSeries.SubstitutionMajorant

/-! Products of normal power series at a prescribed common radius. The
ordinary binary product chooses a fresh radius, which would shrink once per
factor in the finite powers used by analytic substitution. -/

set_option autoImplicit false

namespace Problib.Analysis.Real.PowerSeries

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real.SignedSeries

noncomputable section

@[expose] public noncomputable def multiplySeriesWithin {dimension : Nat}
    (first second : Convergent dimension)
    (radius : selection.Carrier) (positive : lt zero radius)
    (belowFirst : le radius first.radius)
    (belowSecond : le radius second.radius) : Convergent dimension := by
  refine aggregateSeries
    (rawProductTerms first.coefficients second.coefficients)
    (raw_product_homogeneous first.coefficients second.coefficients)
    radius positive ?_
  intro displacement inside
  have firstInside := FiniteVector.ball_mono belowFirst inside
  have secondInside := FiniteVector.ball_mono belowSecond inside
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

public theorem multiplySeriesWithin_value {dimension : Nat}
    (first second : Convergent dimension)
    (radius : selection.Carrier) (positive : lt zero radius)
    (belowFirst : le radius first.radius)
    (belowSecond : le radius second.radius)
    (displacement : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball (FiniteVector.zeroVector dimension)
      (multiplySeriesWithin first second radius positive belowFirst
        belowSecond).radius displacement) :
    value (multiplySeriesWithin first second radius positive belowFirst
        belowSecond) displacement inside =
      mul
        (value first displacement
          (FiniteVector.ball_mono belowFirst inside))
        (value second displacement
          (FiniteVector.ball_mono belowSecond inside)) := by
  let firstInside := FiniteVector.ball_mono belowFirst inside
  let secondInside := FiniteVector.ball_mono belowSecond inside
  let firstAbsolute := fullShellTerms_absolute first displacement firstInside
  let secondAbsolute := fullShellTerms_absolute second displacement
    secondInside
  let productAbsolute := fullShellTerms_absolute
    (multiplySeriesWithin first second radius positive belowFirst
      belowSecond) displacement inside
  have termsEqual :
      fullShellTerms
        (multiplySeriesWithin first second radius positive belowFirst
          belowSecond) displacement =
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
  have sum_congr {left right : Nat → selection.Carrier}
      (equal : left = right)
      (leftSummable : Summable left) (rightSummable : Summable right) :
      sum left leftSummable = sum right rightSummable := by
    cases equal
    rfl
  have sumsEqual :
      sum (fullShellTerms
          (multiplySeriesWithin first second radius positive belowFirst
            belowSecond) displacement)
          (summable_of_absolute_bound productAbsolute) =
      sum (convolution (fullShellTerms first displacement)
        (fullShellTerms second displacement))
          (convolution_summable_absolute firstAbsolute secondAbsolute) := by
    exact sum_congr termsEqual _ _
  calc
    value (multiplySeriesWithin first second radius positive belowFirst
        belowSecond) displacement inside =
      sum (fullShellTerms
          (multiplySeriesWithin first second radius positive belowFirst
            belowSecond) displacement)
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

@[expose] public noncomputable def seriesPowerWithinWitness {dimension : Nat}
    (series : Convergent dimension)
    (radius : selection.Carrier) (positive : lt zero radius)
    (below : le radius series.radius) :
    Nat → { product : Convergent dimension // product.radius = radius }
  | 0 => ⟨constantSeries dimension one radius positive, rfl⟩
  | count + 1 => by
      let previous := seriesPowerWithinWitness series radius positive below
        count
      have belowPrevious : le radius previous.val.radius := by
        rw [previous.property]
        exact le_refl radius
      exact ⟨multiplySeriesWithin previous.val series radius positive
        belowPrevious below, rfl⟩

@[expose] public noncomputable def seriesPowerWithin {dimension : Nat}
    (series : Convergent dimension)
    (radius : selection.Carrier) (positive : lt zero radius)
    (below : le radius series.radius) (count : Nat) :
    Convergent dimension :=
  (seriesPowerWithinWitness series radius positive below count).val

public theorem seriesPowerWithin_radius {dimension : Nat}
    (series : Convergent dimension)
    (radius : selection.Carrier) (positive : lt zero radius)
    (below : le radius series.radius) (count : Nat) :
    (seriesPowerWithin series radius positive below count).radius = radius :=
  (seriesPowerWithinWitness series radius positive below count).property

public theorem seriesPowerWithin_value {dimension : Nat}
    (series : Convergent dimension)
    (radius : selection.Carrier) (positive : lt zero radius)
    (below : le radius series.radius) (count : Nat)
    (displacement : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball (FiniteVector.zeroVector dimension)
      (seriesPowerWithin series radius positive below count).radius
      displacement) :
    value (seriesPowerWithin series radius positive below count)
      displacement inside =
      power (value series displacement
        (FiniteVector.ball_mono below
          (by simpa only [seriesPowerWithin_radius] using inside)))
        count := by
  induction count with
  | zero =>
      change FiniteVector.ball (FiniteVector.zeroVector dimension)
        radius displacement at inside
      exact (constantSeries_value dimension one radius positive
        displacement inside).trans (power_zero _).symm
  | succ count induction =>
      unfold seriesPowerWithin at inside ⊢
      dsimp only [seriesPowerWithinWitness] at inside ⊢
      change value
        (multiplySeriesWithin
          (seriesPowerWithin series radius positive below count)
          series radius positive
          (by rw [seriesPowerWithin_radius]; exact le_refl radius)
          below)
        displacement inside = _
      rw [multiplySeriesWithin_value]
      have previousInside : FiniteVector.ball
          (FiniteVector.zeroVector dimension)
          (seriesPowerWithin series radius positive below count).radius
          displacement := by
        rw [seriesPowerWithin_radius]
        exact inside
      rw [induction previousInside, power_succ, mul_comm]

end

end Problib.Analysis.Real.PowerSeries
