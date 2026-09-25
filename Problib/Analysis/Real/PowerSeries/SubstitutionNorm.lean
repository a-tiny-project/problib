module

public import Problib.Analysis.Real.PowerSeries.SubstitutionCoefficients

/-! The sum of absolute homogeneous shells is submultiplicative at a fixed
evaluation point. This is the norm estimate for the substitution majorant. -/

set_option autoImplicit false

namespace Problib.Analysis.Real.PowerSeries

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real.SignedSeries

noncomputable section

@[expose] public noncomputable def normalSum {dimension : Nat}
    (series : Convergent dimension)
    (displacement : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius displacement) :
    selection.Carrier :=
  sum (fullShellMagnitudes series displacement)
    (fullShellMagnitudes_summable series displacement inside)

public theorem normalSum_nonnegative {dimension : Nat}
    (series : Convergent dimension)
    (displacement : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius displacement) :
    le zero (normalSum series displacement inside) := by
  have finite := partial_sum_le_sum_nonnegative
    (fun degreeValue => shellMagnitude_nonnegative
      series.coefficients displacement degreeValue)
    (fullShellMagnitudes_summable series displacement inside) 0
  change le zero (normalSum series displacement inside) at finite
  simpa only [partial_sum_zero] using finite

public theorem partial_sum_tail_le_normalSum {dimension : Nat}
    (series : Convergent dimension)
    (displacement : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius displacement)
    (count : Nat) :
    le (partialSum (tailMagnitudes series.coefficients displacement)
        count)
      (normalSum series displacement inside) := by
  have fullBound := partial_sum_le_sum_nonnegative
    (fun degreeValue => shellMagnitude_nonnegative
      series.coefficients displacement degreeValue)
    (fullShellMagnitudes_summable series displacement inside)
    (count + 1)
  rw [partial_sum_cons] at fullBound
  have firstNonnegative := shellMagnitude_nonnegative
    series.coefficients displacement 0
  have addBound := add_le_add (le_refl
      (partialSum (tailMagnitudes series.coefficients displacement)
        count)) firstNonnegative
  rw [add_zero, add_comm
    (partialSum (tailMagnitudes series.coefficients displacement) count)
    (shellMagnitude series.coefficients displacement 0)] at addBound
  exact le_trans addBound fullBound

public theorem normalSum_multiply_within_le {dimension : Nat}
    (first second : Convergent dimension)
    (radius : selection.Carrier) (positive : lt zero radius)
    (belowFirst : le radius first.radius)
    (belowSecond : le radius second.radius)
    (displacement : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball (FiniteVector.zeroVector dimension)
      (multiplySeriesWithin first second radius positive belowFirst
        belowSecond).radius displacement) :
    le (normalSum
        (multiplySeriesWithin first second radius positive belowFirst
          belowSecond) displacement inside)
      (mul
        (normalSum first displacement
          (FiniteVector.ball_mono belowFirst inside))
        (normalSum second displacement
          (FiniteVector.ball_mono belowSecond inside))) := by
  let firstInside := FiniteVector.ball_mono belowFirst inside
  let secondInside := FiniteVector.ball_mono belowSecond inside
  let firstMagnitudes := fullShellMagnitudes first displacement
  let secondMagnitudes := fullShellMagnitudes second displacement
  have firstNonnegative : ∀ degreeValue, le zero
      (firstMagnitudes degreeValue) := fun degreeValue =>
    shellMagnitude_nonnegative first.coefficients displacement degreeValue
  have secondNonnegative : ∀ degreeValue, le zero
      (secondMagnitudes degreeValue) := fun degreeValue =>
    shellMagnitude_nonnegative second.coefficients displacement degreeValue
  have firstSummable := fullShellMagnitudes_summable first displacement
    firstInside
  have secondSummable := fullShellMagnitudes_summable second displacement
    secondInside
  have pointwise : ∀ degreeValue,
      le (fullShellMagnitudes
          (multiplySeriesWithin first second radius positive belowFirst
            belowSecond) displacement degreeValue)
        (convolution firstMagnitudes secondMagnitudes degreeValue) := by
    intro degreeValue
    change le (shellMagnitude
      (aggregateCoefficients
        (rawProductTerms first.coefficients second.coefficients))
      displacement degreeValue)
      (convolution
        (fun degreeValue => shellMagnitude first.coefficients
          displacement degreeValue)
        (fun degreeValue => shellMagnitude second.coefficients
          displacement degreeValue) degreeValue)
    rw [← magnitude_raw_product first.coefficients second.coefficients
      displacement degreeValue]
    exact shellMagnitude_aggregate_le _
      (raw_product_homogeneous first.coefficients second.coefficients)
      displacement
  have convolutionSummable := convolution_summable_nonnegative
    firstNonnegative secondNonnegative firstSummable secondSummable
  have bound := summable_sum_le
    (fullShellMagnitudes_summable
      (multiplySeriesWithin first second radius positive belowFirst
        belowSecond) displacement inside)
    convolutionSummable pointwise
  rw [sum_convolution_nonnegative firstNonnegative secondNonnegative
    firstSummable secondSummable] at bound
  exact bound

public theorem normalSum_constant (dimension : Nat)
    (constant radius : selection.Carrier) (positive : lt zero radius)
    (displacement : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) radius displacement) :
    normalSum (constantSeries dimension constant radius positive)
      displacement inside = abs constant := by
  let values := fullShellMagnitudes
    (constantSeries dimension constant radius positive) displacement
  have first : values 0 = abs constant := by
    change shellMagnitude (constantCoefficients dimension constant)
      displacement 0 = abs constant
    rw [shellMagnitude_zero_degree]
    simp only [constantCoefficients, MultiIndex.degree_zeroIndex,
      ↓reduceIte]
  have later : ∀ degreeValue, 1 ≤ degreeValue →
      values degreeValue = zero := by
    intro degreeValue positiveDegree
    obtain ⟨previous, equal⟩ := Nat.exists_eq_add_of_le positiveDegree
    subst degreeValue
    rw [Nat.add_comm 1 previous]
    change tailMagnitudes (constantCoefficients dimension constant)
      displacement previous = zero
    exact constant_tailMagnitudes_zero dimension constant displacement
      previous
  have partialOne : partialSum values 1 = abs constant := by
    rw [partial_sum_succ, partial_sum_zero, zero_add, first]
  have eventual : Problib.Analysis.Real.ConvergesTo
      (partialSum values) (abs constant) := by
    intro tolerance tolerancePositive
    refine ⟨1, fun count countLarge => ?_⟩
    rw [partial_sum_zero_after later countLarge, partialOne,
      sub_self, abs_zero]
    exact tolerancePositive
  have total := sum_eq_of_converges values
    (fullShellMagnitudes_summable
      (constantSeries dimension constant radius positive) displacement inside)
    eventual
  exact total

public theorem normalSum_constant_one (dimension : Nat)
    (radius : selection.Carrier) (positive : lt zero radius)
    (displacement : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) radius displacement) :
    normalSum (constantSeries dimension one radius positive)
      displacement inside = one := by
  rw [normalSum_constant]
  exact abs_of_nonnegative one_nonnegative

public theorem normalSum_product_steps_le
    {source target : Nat}
    (series : Fin target → Convergent source)
    (radius : selection.Carrier) (positive : lt zero radius)
    (below : ∀ coordinate, le radius (series coordinate).radius)
    (steps : List (Fin target))
    (displacement : FiniteVector.carrier source)
    (insideRadius : FiniteVector.ball
      (FiniteVector.zeroVector source) radius displacement) :
    le (normalSum (seriesProductSteps series radius positive below steps)
        displacement
        (by simpa only [seriesProductSteps_radius] using insideRadius))
      (steps.foldr (fun coordinate total =>
        mul (normalSum (series coordinate) displacement
          (FiniteVector.ball_mono (below coordinate) insideRadius)) total)
        one) := by
  induction steps with
  | nil =>
      change le (normalSum
        (constantSeries source one radius positive) displacement
        insideRadius) one
      rw [normalSum_constant_one source radius positive
        displacement insideRadius]
      exact le_refl one
  | cons coordinate rest induction =>
      have previousInside : FiniteVector.ball
          (FiniteVector.zeroVector source)
          (seriesProductSteps series radius positive below rest).radius
          displacement := by
        simpa only [seriesProductSteps_radius] using insideRadius
      have productInside : FiniteVector.ball
          (FiniteVector.zeroVector source)
          (multiplySeriesWithin (series coordinate)
            (seriesProductSteps series radius positive below rest) radius
            positive (below coordinate)
            (by rw [seriesProductSteps_radius]; exact le_refl radius)).radius
          displacement := by
        exact insideRadius
      have productBound := normalSum_multiply_within_le
        (series coordinate)
        (seriesProductSteps series radius positive below rest)
        radius positive (below coordinate)
        (by rw [seriesProductSteps_radius]; exact le_refl radius)
        displacement productInside
      have multiplyBound := mul_le_mul_nonnegative_left induction
        (normalSum_nonnegative (series coordinate) displacement
          (FiniteVector.ball_mono (below coordinate) insideRadius))
      exact le_trans productBound multiplyBound

public theorem normalSum_monomial_le
    {source target : Nat}
    (series : Fin target → Convergent source)
    (radius : selection.Carrier) (positive : lt zero radius)
    (below : ∀ coordinate, le radius (series coordinate).radius)
    (index : MultiIndex.carrier target)
    (displacement : FiniteVector.carrier source)
    (insideRadius : FiniteVector.ball
      (FiniteVector.zeroVector source) radius displacement) :
    le (normalSum (seriesMonomialWithin series radius positive below index)
        displacement
        (by simpa only [seriesMonomialWithin,
          seriesProductSteps_radius] using insideRadius))
      (MultiIndex.monomial target index
        (fun coordinate => normalSum (series coordinate) displacement
          (FiniteVector.ball_mono (below coordinate) insideRadius))) := by
  have bound := normalSum_product_steps_le series radius positive below
    (canonicalDerivativeSteps index) displacement insideRadius
  rw [fold_steps_eq_monomial, derivative_count_canonical] at bound
  exact bound

public theorem normalSum_zero_constant_eq_tail {dimension : Nat}
    (series : Convergent dimension)
    (zeroConstant : series.coefficients
      (MultiIndex.zeroIndex dimension) = zero)
    (displacement : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius displacement)
    (tailSummable : Summable
      (tailMagnitudes series.coefficients displacement)) :
    normalSum series displacement inside =
      sum (tailMagnitudes series.coefficients displacement)
        tailSummable := by
  let full := fullShellMagnitudes series displacement
  let tail := tailMagnitudes series.coefficients displacement
  have first : full 0 = zero := by
    change shellMagnitude series.coefficients displacement 0 = zero
    rw [shellMagnitude_zero_degree, zeroConstant, abs_zero]
  have shifted : ∀ degreeValue, full (degreeValue + 1) =
      tail degreeValue := fun _ => rfl
  have finiteShift : ∀ count,
      partialSum full (count + 1) = partialSum tail count := by
    intro count
    rw [partial_sum_cons, first, zero_add]
    congr 1
  have fullConverges := converges_to_shift
    (partial_sum_converges full
      (fullShellMagnitudes_summable series displacement inside))
  have sequencesEqual :
      (fun count => partialSum full (count + 1)) =
        partialSum tail := by
    funext count
    exact finiteShift count
  rw [sequencesEqual] at fullConverges
  exact converges_to_unique fullConverges
    (partial_sum_converges tail tailSummable)

public theorem abs_value_le_normalSum_zero_constant {dimension : Nat}
    (series : Convergent dimension)
    (zeroConstant : series.coefficients
      (MultiIndex.zeroIndex dimension) = zero)
    (displacement : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius displacement) :
    le (abs (value series displacement inside))
      (normalSum series displacement inside) := by
  let terms := tailTerms series.coefficients displacement
  have finiteBound : ∀ count,
      le (abs (partialSum terms count))
        (normalSum series displacement inside) := by
    intro count
    exact le_trans
      (abs_partial_sum_le_magnitudes series.coefficients displacement
        count)
      (partial_sum_tail_le_normalSum series displacement inside count)
  have limitBound := abs_le_of_convergesTo
    (partial_sum_converges terms
      (summable_of_absolute_bound (series.absoluteOn displacement inside)))
    finiteBound
  simpa only [value, zeroConstant, zero_add] using limitBound

public theorem normalSum_le_diagonal_tail {dimension : Nat}
    (series : Convergent dimension)
    (zeroConstant : series.coefficients
      (MultiIndex.zeroIndex dimension) = zero)
    (displacement : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius displacement)
    (radius : selection.Carrier) (positive : lt zero radius)
    (coordinates : ∀ coordinate,
      le (abs (displacement coordinate)) radius)
    (diagonalSummable : Summable
      (tailMagnitudes series.coefficients (fun _ => radius))) :
    le (normalSum series displacement inside)
      (sum (tailMagnitudes series.coefficients (fun _ => radius))
        diagonalSummable) := by
  have displacementSummable : Summable
      (tailMagnitudes series.coefficients displacement) :=
    summable_of_nonnegative_bounded
      (fun degreeValue => shellMagnitude_nonnegative
        series.coefficients displacement (degreeValue + 1))
      (series.normalOn displacement inside)
  rw [normalSum_zero_constant_eq_tail series zeroConstant displacement
    inside displacementSummable]
  exact summable_sum_le displacementSummable diagonalSummable
    (fun degreeValue => tailMagnitudes_le_constant
      series.coefficients displacement positive.left coordinates
      degreeValue)

public theorem component_normal_sums_small_radius
    {source target : Nat}
    (series : Fin target → Convergent source)
    (zeroConstant : ∀ coordinate,
      (series coordinate).coefficients
        (MultiIndex.zeroIndex source) = zero)
    {bound : selection.Carrier} (boundPositive : lt zero bound) :
    ∃ radius : selection.Carrier,
      lt zero radius ∧
      (∀ coordinate, le radius (series coordinate).radius) ∧
      ∀ displacement : FiniteVector.carrier source,
        FiniteVector.ball (FiniteVector.zeroVector source)
          radius displacement →
        ∀ coordinate : Fin target,
          ∃ inside : FiniteVector.ball
              (FiniteVector.zeroVector source)
              (series coordinate).radius displacement,
            lt (normalSum (series coordinate) displacement inside)
              bound := by
  rcases component_tail_majorants_small_radius series boundPositive with
    ⟨radius, radiusPositive, componentBound⟩
  refine ⟨radius, radiusPositive,
    (fun coordinate => (componentBound coordinate).1.left),
    fun displacement insideRadius coordinate => ?_⟩
  rcases componentBound coordinate with
    ⟨radiusBelow, diagonalInside, diagonalSummable, diagonalBound⟩
  let inside := FiniteVector.ball_mono radiusBelow.left insideRadius
  refine ⟨inside, ?_⟩
  have coordinates : ∀ input,
      le (abs (displacement input)) radius := by
    intro input
    have near := insideRadius input
    change lt (abs (sub (displacement input) zero)) radius at near
    rw [sub_zero] at near
    exact near.left
  exact lt_of_le_of_lt
    (normalSum_le_diagonal_tail (series coordinate)
      (zeroConstant coordinate) displacement inside radius radiusPositive
      coordinates diagonalSummable)
    diagonalBound

end

end Problib.Analysis.Real.PowerSeries
