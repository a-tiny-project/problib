module

public import Problib.Analysis.Real.PowerSeries.SubstitutionValue

/-! A normal bound on a larger diagonal box controls all tails on a
strictly smaller box, uniformly across finite outer truncations. -/

set_option autoImplicit false

namespace Problib.Analysis.Real.PowerSeries

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real.SignedSeries

noncomputable section

public theorem power_le_of_le_exponent
    {ratio : selection.Carrier}
    (nonnegative : le zero ratio) (atMostOne : le ratio one)
    {small large : Nat} (included : small ≤ large) :
    le (power ratio large) (power ratio small) := by
  obtain ⟨extra, equal⟩ := Nat.exists_eq_add_of_le included
  subst large
  rw [power_add]
  have bounded := power_le_one nonnegative atMostOne extra
  have scaled := mul_le_mul_nonnegative_left bounded
    (power_nonnegative nonnegative small)
  rwa [mul_one] at scaled

public theorem partial_sum_shifted_tail_le_normalSum
    {dimension : Nat}
    (series : Convergent dimension)
    (displacement : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius displacement)
    (start count : Nat) :
    le (partialSum
        (fun index => tailMagnitudes series.coefficients displacement
          (start + index)) count)
      (normalSum series displacement inside) := by
  let values := tailMagnitudes series.coefficients displacement
  have append := partial_sum_append values start count
  have firstNonnegative := partial_sum_nonnegative
    (fun index => shellMagnitude_nonnegative series.coefficients
      displacement (index + 1)) start
  have included : le
      (partialSum (fun index => values (start + index)) count)
      (partialSum values (start + count)) := by
    rw [append]
    have raised := add_le_add firstNonnegative
      (le_refl (partialSum (fun index => values (start + index)) count))
    rw [zero_add] at raised
    exact raised
  exact le_trans included
    (partial_sum_tail_le_normalSum series displacement inside
      (start + count))

public theorem finite_tail_bound_of_diagonal
    {dimension : Nat}
    (series : Convergent dimension)
    (displacement : FiniteVector.carrier dimension)
    (radius ratio : selection.Carrier)
    (radiusPositive : lt zero radius)
    (ratioNonnegative : le zero ratio) (ratioAtMostOne : le ratio one)
    (coordinates : ∀ coordinate,
      le (abs (displacement coordinate)) (mul ratio radius))
    (diagonalInside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius
      (fun _ => radius))
    (start count : Nat) :
    le (abs (partialSum
        (fun index => tailTerms series.coefficients displacement
          (start + index)) count))
      (mul (power ratio (start + 1))
        (normalSum series (fun _ => radius) diagonalInside)) := by
  have shiftedSignedBound :
      le (abs (partialSum
        (fun index => tailTerms series.coefficients displacement
          (start + index)) count))
        (partialSum
          (fun index => tailMagnitudes series.coefficients displacement
            (start + index)) count) := by
    induction count with
    | zero =>
        rw [partial_sum_zero, partial_sum_zero, abs_zero]
        exact le_refl zero
    | succ count induction =>
        rw [partial_sum_succ, partial_sum_succ]
        exact le_trans (abs_add_le _ _)
          (add_le_add induction
            (abs_shellTerm_le_magnitude series.coefficients
              displacement (start + count + 1)))
  have ratioRadiusNonnegative := mul_nonnegative ratioNonnegative
    radiusPositive.left
  have pointwise : ∀ index,
      le (tailMagnitudes series.coefficients displacement (start + index))
        (mul (power ratio (start + 1))
          (tailMagnitudes series.coefficients (fun _ => radius)
            (start + index))) := by
    intro index
    have constantBound := tailMagnitudes_le_constant
      series.coefficients displacement ratioRadiusNonnegative
      coordinates (start + index)
    rw [tail_magnitude_scale_radius series.coefficients ratio radius
      ratioNonnegative radiusPositive.left] at constantBound
    have powerBound := power_le_of_le_exponent ratioNonnegative
      ratioAtMostOne (small := start + 1)
      (large := start + index + 1) (by omega)
    exact le_trans constantBound
      (mul_le_mul_nonnegative_right powerBound
        (shellMagnitude_nonnegative series.coefficients
          (fun _ => radius) (start + index + 1)))
  have partialBound := partial_sum_le pointwise count
  rw [partial_sum_scale] at partialBound
  exact le_trans shiftedSignedBound
    (le_trans partialBound
      (mul_le_mul_nonnegative_left
        (partial_sum_shifted_tail_le_normalSum series
          (fun _ => radius) diagonalInside start count)
        (power_nonnegative ratioNonnegative (start + 1))))

public theorem value_tail_bound_of_diagonal
    {dimension : Nat}
    (series : Convergent dimension)
    (displacement : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius displacement)
    (radius ratio : selection.Carrier)
    (radiusPositive : lt zero radius)
    (ratioNonnegative : le zero ratio) (ratioAtMostOne : le ratio one)
    (coordinates : ∀ coordinate,
      le (abs (displacement coordinate)) (mul ratio radius))
    (diagonalInside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius
      (fun _ => radius))
    (start : Nat) :
    le (abs (sub (value series displacement inside)
        (add (series.coefficients (MultiIndex.zeroIndex dimension))
          (partialSum (tailTerms series.coefficients displacement)
            start))))
      (mul (power ratio (start + 1))
        (normalSum series (fun _ => radius) diagonalInside)) := by
  let terms := tailTerms series.coefficients displacement
  let certificate := summable_of_absolute_bound
    (series.absoluteOn displacement inside)
  have tailConverges := partial_sum_tail_converges terms certificate start
  have finiteBound : ∀ count,
      le (abs (partialSum (fun index => terms (start + index)) count))
        (mul (power ratio (start + 1))
          (normalSum series (fun _ => radius) diagonalInside)) :=
    fun count => finite_tail_bound_of_diagonal series displacement
      radius ratio radiusPositive ratioNonnegative ratioAtMostOne
      coordinates diagonalInside start count
  have limitBound := abs_le_of_convergesTo tailConverges finiteBound
  change le
    (abs (sub (value series displacement inside)
      (add (series.coefficients (MultiIndex.zeroIndex dimension))
        (partialSum terms start)))) _
  unfold value
  rw [add_sub_add_comm, sub_self, zero_add]
  exact limitBound

public theorem geometric_scaled_power_small
    {ratio : selection.Carrier}
    (ratioNonnegative : le zero ratio)
    (ratioBelowOne : lt ratio one)
    (bound : selection.Carrier)
    {tolerance : selection.Carrier}
    (tolerancePositive : lt zero tolerance) :
    ∃ stage : Nat,
      ∀ count, stage ≤ count →
        lt (mul (power ratio (count + 1)) bound) tolerance := by
  have baseConverges := terms_converge_zero
    (geometric_summable ratioNonnegative ratioBelowOne)
  have scaled := converges_to_scale bound
    (converges_to_shift baseConverges)
  rw [mul_zero] at scaled
  rcases scaled tolerance tolerancePositive with ⟨stage, close⟩
  refine ⟨stage, fun count later => ?_⟩
  have near := close count later
  rw [sub_zero] at near
  dsimp only at near
  rw [mul_comm bound (power ratio (count + 1))] at near
  exact lt_of_le_of_lt (le_abs _) near

public theorem outer_truncations_uniform_tail
    {source target : Nat}
    (outer : Convergent target)
    (inner : Fin target → Convergent source)
    (radius : selection.Carrier) (positive : lt zero radius)
    (below : ∀ coordinate, le radius (inner coordinate).radius)
    (outerInside : ∀ displacement : FiniteVector.carrier source,
      ∀ insideRadius : FiniteVector.ball
        (FiniteVector.zeroVector source) radius displacement,
        FiniteVector.ball (FiniteVector.zeroVector target)
          outer.radius
          (fun coordinate => normalSum (inner coordinate) displacement
            (FiniteVector.ball_mono (below coordinate) insideRadius)))
    (displacement : FiniteVector.carrier source)
    (insideRadius : FiniteVector.ball
      (FiniteVector.zeroVector source) radius displacement)
    {tolerance : selection.Carrier}
    (tolerancePositive : lt zero tolerance) :
    ∃ stage : Nat,
      ∀ degreeBound start, stage ≤ start →
        lt (abs (sub
          (value (outerTruncationSeries outer.coefficients inner radius
            positive below degreeBound) displacement
            (by simpa only [outerTruncationSeries,
              finiteSeriesSum_radius] using insideRadius))
          (add ((outerTruncationSeries outer.coefficients inner radius
            positive below degreeBound).coefficients
              (MultiIndex.zeroIndex source))
            (partialSum (tailTerms
              (outerTruncationSeries outer.coefficients inner radius
                positive below degreeBound).coefficients displacement)
              start)))) tolerance := by
  let size := FiniteVector.supNorm displacement
  have sizeNonnegative := FiniteVector.sup_norm_nonnegative displacement
  have sizeBelow : lt size radius :=
    FiniteVector.sup_norm_lt positive (fun coordinate => by
      have bounded := insideRadius coordinate
      change lt (abs (sub (displacement coordinate) zero)) radius
        at bounded
      rwa [sub_zero] at bounded)
  rcases positive_midpoint sizeNonnegative sizeBelow with
    ⟨smallRadius, smallPositive, sizeBelowSmall, smallBelowRadius⟩
  rcases positive_midpoint smallPositive.left smallBelowRadius with
    ⟨largeRadius, largePositive, smallBelowLarge, largeBelowRadius⟩
  let ratio := div smallRadius largeRadius
  have largeNonzero := nonzero_of_positive largePositive
  have ratioPositive : lt zero ratio :=
    div_positive smallPositive largePositive
  have ratioBelowOne : lt ratio one := by
    have inversePositive := inverse_of_positive_positive largePositive
    have scaled := mul_lt_mul_positive_right smallBelowLarge
      inversePositive
    rw [mul_inverse_cancel largeNonzero] at scaled
    change lt (div smallRadius largeRadius) one
    rwa [div_eq_mul_inverse]
  have ratioProduct : mul ratio largeRadius = smallRadius :=
    div_mul_cancel smallRadius largeNonzero
  have diagonalInside : FiniteVector.ball
      (FiniteVector.zeroVector source) radius
      (fun _ => largeRadius) := by
    intro coordinate
    change lt (abs (sub largeRadius zero)) radius
    rw [sub_zero, abs_of_nonnegative largePositive.left]
    exact largeBelowRadius
  have coordinates : ∀ coordinate,
      le (abs (displacement coordinate))
        (mul ratio largeRadius) := by
    intro coordinate
    rw [ratioProduct]
    exact le_trans (FiniteVector.coordinate_le_sup_norm displacement
      coordinate) sizeBelowSmall.left
  let bound := normalSum outer
    (fun coordinate => normalSum (inner coordinate)
      (fun _ => largeRadius)
      (FiniteVector.ball_mono (below coordinate) diagonalInside))
    (outerInside (fun _ => largeRadius) diagonalInside)
  rcases geometric_scaled_power_small ratioPositive.left ratioBelowOne
    bound tolerancePositive with ⟨stage, small⟩
  refine ⟨stage, fun degreeBound start later => ?_⟩
  let series := outerTruncationSeries outer.coefficients inner radius
    positive below degreeBound
  have inside : FiniteVector.ball
      (FiniteVector.zeroVector source) series.radius displacement := by
    simpa only [series, outerTruncationSeries,
      finiteSeriesSum_radius] using insideRadius
  have diagonal : FiniteVector.ball
      (FiniteVector.zeroVector source) series.radius
      (fun _ => largeRadius) := by
    simpa only [series, outerTruncationSeries,
      finiteSeriesSum_radius] using diagonalInside
  have tailBound := value_tail_bound_of_diagonal series displacement
    inside largeRadius ratio largePositive ratioPositive.left
    ratioBelowOne.left coordinates diagonal start
  have normalBound := outer_truncation_normalSum_le_outer outer inner
    radius positive below degreeBound (fun _ => largeRadius)
    diagonalInside (outerInside (fun _ => largeRadius) diagonalInside)
  have scaled := mul_le_mul_nonnegative_left normalBound
    (power_nonnegative ratioPositive.left (start + 1))
  exact lt_of_le_of_lt (le_trans tailBound scaled) (small start later)

end

end Problib.Analysis.Real.PowerSeries
