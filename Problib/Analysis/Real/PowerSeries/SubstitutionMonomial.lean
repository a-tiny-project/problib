module

public import Problib.Analysis.Real.PowerSeries.SubstitutionOrder
public import Problib.Analysis.Real.PowerSeries.TaylorCoefficients

/-! Finite monomials of inner analytic series at one radius. -/

set_option autoImplicit false

namespace Problib.Analysis.Real.PowerSeries

open Problib.Real.Construction.Dedekind

noncomputable section

@[expose] public noncomputable def seriesProductStepsWitness
    {source target : Nat}
    (series : Fin target → Convergent source)
    (radius : selection.Carrier) (positive : lt zero radius)
    (below : ∀ coordinate, le radius (series coordinate).radius) :
    List (Fin target) →
      { product : Convergent source // product.radius = radius }
  | [] => ⟨constantSeries source one radius positive, rfl⟩
  | coordinate :: rest => by
      let previous := seriesProductStepsWitness series radius positive
        below rest
      have belowPrevious : le radius previous.val.radius := by
        rw [previous.property]
        exact le_refl radius
      exact ⟨multiplySeriesWithin (series coordinate) previous.val radius
        positive (below coordinate) belowPrevious, rfl⟩

@[expose] public noncomputable def seriesProductSteps
    {source target : Nat}
    (series : Fin target → Convergent source)
    (radius : selection.Carrier) (positive : lt zero radius)
    (below : ∀ coordinate, le radius (series coordinate).radius)
    (steps : List (Fin target)) : Convergent source :=
  (seriesProductStepsWitness series radius positive below steps).val

public theorem seriesProductSteps_radius
    {source target : Nat}
    (series : Fin target → Convergent source)
    (radius : selection.Carrier) (positive : lt zero radius)
    (below : ∀ coordinate, le radius (series coordinate).radius)
    (steps : List (Fin target)) :
    (seriesProductSteps series radius positive below steps).radius = radius :=
  (seriesProductStepsWitness series radius positive below steps).property

public theorem seriesProductSteps_order
    {source target : Nat}
    (series : Fin target → Convergent source)
    (radius : selection.Carrier) (positive : lt zero radius)
    (below : ∀ coordinate, le radius (series coordinate).radius)
    (zeroConstant : ∀ coordinate, (series coordinate).coefficients
      (MultiIndex.zeroIndex source) = zero)
    (steps : List (Fin target)) :
    CoefficientsVanishBelow
      (seriesProductSteps series radius positive below steps).coefficients
      steps.length := by
  induction steps with
  | nil =>
      intro index indexBelow
      change MultiIndex.degree source index < 0 at indexBelow
      omega
  | cons coordinate rest induction =>
      change CoefficientsVanishBelow
        (multiplySeriesWithin (series coordinate)
          (seriesProductSteps series radius positive below rest) radius
          positive (below coordinate)
          (by rw [seriesProductSteps_radius]; exact le_refl radius)).coefficients
        (coordinate :: rest).length
      have coordinateOrder : CoefficientsVanishBelow
          (series coordinate).coefficients 1 := by
        intro index indexBelow
        have zeroIndex := MultiIndex.eq_zeroIndex_of_degree_zero
          source index (by omega)
        simpa only [zeroIndex] using zeroConstant coordinate
      simpa only [List.length_cons, Nat.add_comm] using
        (multiplySeriesWithin_order _ _ _ _ _ _
          coordinateOrder induction)

public theorem seriesProductSteps_value
    {source target : Nat}
    (series : Fin target → Convergent source)
    (radius : selection.Carrier) (positive : lt zero radius)
    (below : ∀ coordinate, le radius (series coordinate).radius)
    (steps : List (Fin target))
    (displacement : FiniteVector.carrier source)
    (inside : FiniteVector.ball (FiniteVector.zeroVector source)
      (seriesProductSteps series radius positive below steps).radius
      displacement) :
    value (seriesProductSteps series radius positive below steps)
      displacement inside =
      steps.foldr (fun coordinate total =>
        mul (value (series coordinate) displacement
          (FiniteVector.ball_mono (below coordinate)
            (by simpa only [seriesProductSteps_radius] using inside)))
          total) one := by
  induction steps with
  | nil =>
      change FiniteVector.ball (FiniteVector.zeroVector source)
        radius displacement at inside
      exact constantSeries_value source one radius positive
        displacement inside
  | cons coordinate rest induction =>
      unfold seriesProductSteps at inside ⊢
      dsimp only [seriesProductStepsWitness] at inside ⊢
      change value
        (multiplySeriesWithin (series coordinate)
          (seriesProductSteps series radius positive below rest) radius
          positive (below coordinate)
          (by rw [seriesProductSteps_radius]; exact le_refl radius))
        displacement inside = _
      rw [multiplySeriesWithin_value]
      have previousInside : FiniteVector.ball
          (FiniteVector.zeroVector source)
          (seriesProductSteps series radius positive below rest).radius
          displacement := by
        rw [seriesProductSteps_radius]
        exact inside
      rw [induction previousInside]
      rfl

public theorem derivativeCountIndex_degree {dimension : Nat}
    (steps : List (Fin dimension)) :
    MultiIndex.degree dimension (derivativeCountIndex steps) =
      steps.length := by
  induction steps with
  | nil => exact MultiIndex.degree_zeroIndex dimension
  | cons coordinate rest induction =>
      change MultiIndex.degree dimension
        (MultiIndex.addIndex (derivativeCountIndex rest)
          (MultiIndex.unitIndex coordinate)) = _
      rw [MultiIndex.degree_addIndex,
        MultiIndex.degree_unitIndex, induction]
      simp only [List.length_cons]

public theorem canonicalDerivativeSteps_length {dimension : Nat}
    (index : MultiIndex.carrier dimension) :
    (canonicalDerivativeSteps index).length =
      MultiIndex.degree dimension index := by
  rw [← derivativeCountIndex_degree,
    derivative_count_canonical]

public theorem fold_steps_eq_monomial {dimension : Nat}
    (steps : List (Fin dimension))
    (point : FiniteVector.carrier dimension) :
    steps.foldr (fun coordinate total => mul (point coordinate) total) one =
      MultiIndex.monomial dimension (derivativeCountIndex steps) point := by
  induction steps with
  | nil =>
      exact (MultiIndex.monomial_zeroIndex dimension point).symm
  | cons coordinate rest induction =>
      change mul (point coordinate)
        (rest.foldr (fun selected total => mul (point selected) total) one) =
        MultiIndex.monomial dimension
          (MultiIndex.addIndex (derivativeCountIndex rest)
            (MultiIndex.unitIndex coordinate)) point
      rw [MultiIndex.monomial_addIndex,
        MultiIndex.monomial_unitIndex, ← induction, mul_comm]

@[expose] public noncomputable def seriesMonomialWithin
    {source target : Nat}
    (series : Fin target → Convergent source)
    (radius : selection.Carrier) (positive : lt zero radius)
    (below : ∀ coordinate, le radius (series coordinate).radius)
    (index : MultiIndex.carrier target) : Convergent source :=
  seriesProductSteps series radius positive below
    (canonicalDerivativeSteps index)

public theorem seriesMonomialWithin_order
    {source target : Nat}
    (series : Fin target → Convergent source)
    (radius : selection.Carrier) (positive : lt zero radius)
    (below : ∀ coordinate, le radius (series coordinate).radius)
    (zeroConstant : ∀ coordinate, (series coordinate).coefficients
      (MultiIndex.zeroIndex source) = zero)
    (index : MultiIndex.carrier target) :
    CoefficientsVanishBelow
      (seriesMonomialWithin series radius positive below index).coefficients
      (MultiIndex.degree target index) := by
  simpa only [seriesMonomialWithin, canonicalDerivativeSteps_length]
    using seriesProductSteps_order series radius positive below
      zeroConstant (canonicalDerivativeSteps index)

public theorem seriesMonomialWithin_value
    {source target : Nat}
    (series : Fin target → Convergent source)
    (radius : selection.Carrier) (positive : lt zero radius)
    (below : ∀ coordinate, le radius (series coordinate).radius)
    (index : MultiIndex.carrier target)
    (displacement : FiniteVector.carrier source)
    (inside : FiniteVector.ball (FiniteVector.zeroVector source)
      (seriesMonomialWithin series radius positive below index).radius
      displacement) :
    value (seriesMonomialWithin series radius positive below index)
      displacement inside =
      MultiIndex.monomial target index
        (fun coordinate =>
          value (series coordinate) displacement
            (FiniteVector.ball_mono (below coordinate)
              (by simpa only [seriesMonomialWithin,
                seriesProductSteps_radius] using inside))) := by
  change value (seriesProductSteps series radius positive below
      (canonicalDerivativeSteps index)) displacement inside = _
  rw [seriesProductSteps_value]
  rw [fold_steps_eq_monomial, derivative_count_canonical]

end

end Problib.Analysis.Real.PowerSeries
