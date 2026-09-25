module

public import Problib.Analysis.Real.PowerSeries.SubstitutionSum

/-! Finite outer Taylor polynomials after analytic substitution. -/

set_option autoImplicit false

namespace Problib.Analysis.Real.PowerSeries

open Problib.Real.Construction.Dedekind

noncomputable section

@[expose] public noncomputable def outerTermSeries
    {source target : Nat}
    (outer : MultiIndex.carrier target → selection.Carrier)
    (inner : Fin target → Convergent source)
    (radius : selection.Carrier) (positive : lt zero radius)
    (below : ∀ coordinate, le radius (inner coordinate).radius)
    (outerIndex : MultiIndex.carrier target) : Convergent source :=
  scaleSeries (outer outerIndex)
    (seriesMonomialWithin inner radius positive below outerIndex)

public theorem outerTermSeries_radius
    {source target : Nat}
    (outer : MultiIndex.carrier target → selection.Carrier)
    (inner : Fin target → Convergent source)
    (radius : selection.Carrier) (positive : lt zero radius)
    (below : ∀ coordinate, le radius (inner coordinate).radius)
    (outerIndex : MultiIndex.carrier target) :
    (outerTermSeries outer inner radius positive below
      outerIndex).radius = radius :=
  seriesProductSteps_radius inner radius positive below
    (canonicalDerivativeSteps outerIndex)

@[expose] public noncomputable def outerTruncationSeries
    {source target : Nat}
    (outer : MultiIndex.carrier target → selection.Carrier)
    (inner : Fin target → Convergent source)
    (radius : selection.Carrier) (positive : lt zero radius)
    (below : ∀ coordinate, le radius (inner coordinate).radius)
    (degreeBound : Nat) : Convergent source :=
  finiteSeriesSum (outerTermSeries outer inner radius positive below)
    radius positive (outerTermSeries_radius outer inner radius positive
      below) (outerIndicesThrough target degreeBound)

public theorem outer_truncation_coefficients
    {source target : Nat}
    (outer : MultiIndex.carrier target → selection.Carrier)
    (inner : Fin target → Convergent source)
    (radius : selection.Carrier) (positive : lt zero radius)
    (below : ∀ coordinate, le radius (inner coordinate).radius)
    (degreeBound : Nat) (index : MultiIndex.carrier source) :
    (outerTruncationSeries outer inner radius positive below
      degreeBound).coefficients index =
    substitutionCoefficientThrough outer inner radius positive below
      degreeBound index := by
  unfold outerTruncationSeries substitutionCoefficientThrough
  rw [finiteSeriesSum_coefficients]
  rfl

public theorem outer_truncation_value
    {source target : Nat}
    (outer : MultiIndex.carrier target → selection.Carrier)
    (inner : Fin target → Convergent source)
    (radius : selection.Carrier) (positive : lt zero radius)
    (below : ∀ coordinate, le radius (inner coordinate).radius)
    (degreeBound : Nat)
    (displacement : FiniteVector.carrier source)
    (insideRadius : FiniteVector.ball
      (FiniteVector.zeroVector source) radius displacement) :
    value (outerTruncationSeries outer inner radius positive below
      degreeBound) displacement
      (by simpa only [outerTruncationSeries,
        finiteSeriesSum_radius] using insideRadius) =
    (outerIndicesThrough target degreeBound).foldr
      (fun outerIndex total =>
        add (mul (outer outerIndex)
          (MultiIndex.monomial target outerIndex
            (fun coordinate => value (inner coordinate) displacement
              (FiniteVector.ball_mono (below coordinate)
                insideRadius)))) total) zero := by
  unfold outerTruncationSeries
  rw [finiteSeriesSum_value
    (outerTermSeries outer inner radius positive below) radius positive
    (outerTermSeries_radius outer inner radius positive below)
    (outerIndicesThrough target degreeBound) displacement insideRadius]
  have termEqual : ∀ outerIndex,
      value (outerTermSeries outer inner radius positive below
          outerIndex) displacement
        (by rw [outerTermSeries_radius]; exact insideRadius) =
      mul (outer outerIndex)
        (MultiIndex.monomial target outerIndex
          (fun coordinate => value (inner coordinate) displacement
            (FiniteVector.ball_mono (below coordinate)
              insideRadius))) := by
    intro outerIndex
    unfold outerTermSeries
    rw [scaleSeries_value,
      seriesMonomialWithin_value]
  induction outerIndicesThrough target degreeBound with
  | nil => rfl
  | cons index rest induction =>
      rw [List.foldr_cons, List.foldr_cons, termEqual index, induction]

private theorem foldr_add_le {α : Type}
    (indices : List α)
    (first second : α → selection.Carrier)
    (pointwise : ∀ index, le (first index) (second index)) :
    le (indices.foldr (fun index total => add (first index) total) zero)
      (indices.foldr (fun index total => add (second index) total) zero) := by
  induction indices with
  | nil => exact le_refl zero
  | cons index rest induction =>
      exact add_le_add (pointwise index) induction

public theorem outer_truncation_normalSum_le
    {source target : Nat}
    (outer : MultiIndex.carrier target → selection.Carrier)
    (inner : Fin target → Convergent source)
    (radius : selection.Carrier) (positive : lt zero radius)
    (below : ∀ coordinate, le radius (inner coordinate).radius)
    (degreeBound : Nat)
    (displacement : FiniteVector.carrier source)
    (insideRadius : FiniteVector.ball
      (FiniteVector.zeroVector source) radius displacement) :
    le (normalSum
        (outerTruncationSeries outer inner radius positive below
          degreeBound) displacement
        (by simpa only [outerTruncationSeries,
          finiteSeriesSum_radius] using insideRadius))
      ((outerIndicesThrough target degreeBound).foldr
        (fun outerIndex total =>
          add (mul (abs (outer outerIndex))
            (MultiIndex.monomial target outerIndex
              (fun coordinate => normalSum (inner coordinate)
                displacement (FiniteVector.ball_mono (below coordinate)
                  insideRadius)))) total) zero) := by
  have finiteBound := normalSum_finite_series_le
    (outerTermSeries outer inner radius positive below) radius positive
    (outerTermSeries_radius outer inner radius positive below)
    (outerIndicesThrough target degreeBound) displacement insideRadius
  have termBound : ∀ outerIndex,
      le (normalSum (outerTermSeries outer inner radius positive below
          outerIndex) displacement
        (by rw [outerTermSeries_radius]; exact insideRadius))
        (mul (abs (outer outerIndex))
          (MultiIndex.monomial target outerIndex
            (fun coordinate => normalSum (inner coordinate)
              displacement (FiniteVector.ball_mono (below coordinate)
                insideRadius)))) := by
    intro outerIndex
    unfold outerTermSeries
    rw [normalSum_scale]
    exact mul_le_mul_nonnegative_left
      (normalSum_monomial_le inner radius positive below outerIndex
        displacement insideRadius)
      (abs_nonnegative (outer outerIndex))
  exact le_trans finiteBound
    (foldr_add_le (outerIndicesThrough target degreeBound) _ _ termBound)

end

end Problib.Analysis.Real.PowerSeries
