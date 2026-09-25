module

public import Problib.Analysis.Real.PowerSeries.SubstitutionBound

/-! Normal convergence of the canonical coefficient family obtained by
substituting zero-constant inner series into a normally convergent outer
series. -/

set_option autoImplicit false

namespace Problib.Analysis.Real.PowerSeries

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real.SignedSeries

noncomputable section

public theorem substituted_partial_magnitudes_eq_truncation
    {source target : Nat}
    (outer : MultiIndex.carrier target → selection.Carrier)
    (inner : Fin target → Convergent source)
    (radius : selection.Carrier) (positive : lt zero radius)
    (below : ∀ coordinate, le radius (inner coordinate).radius)
    (zeroConstant : ∀ coordinate,
      (inner coordinate).coefficients
        (MultiIndex.zeroIndex source) = zero)
    (displacement : FiniteVector.carrier source) (count : Nat) :
    partialSum
      (tailMagnitudes
        (substitutionCoefficients outer inner radius positive below)
        displacement) count =
    partialSum
      (tailMagnitudes
        (outerTruncationSeries outer inner radius positive below
          count).coefficients displacement) count := by
  apply partial_sum_congr_below count
  intro degreeValue degreeBelow
  apply shellMagnitude_congr_on displacement
  intro index member
  have indexDegree := MultiIndex.degree_of_mem_shell member
  have included : MultiIndex.degree source index ≤ count := by
    omega
  rw [outer_truncation_coefficients]
  exact (substitutionCoefficientThrough_stable outer inner radius
    positive below zeroConstant index count included).symm

public theorem substitution_normally_convergent
    {source target : Nat}
    (outer : Convergent target)
    (inner : Fin target → Convergent source)
    (radius : selection.Carrier) (positive : lt zero radius)
    (below : ∀ coordinate, le radius (inner coordinate).radius)
    (zeroConstant : ∀ coordinate,
      (inner coordinate).coefficients
        (MultiIndex.zeroIndex source) = zero)
    (outerInside : ∀ displacement : FiniteVector.carrier source,
      ∀ insideRadius : FiniteVector.ball
        (FiniteVector.zeroVector source) radius displacement,
        FiniteVector.ball (FiniteVector.zeroVector target)
          outer.radius
          (fun coordinate => normalSum (inner coordinate) displacement
            (FiniteVector.ball_mono (below coordinate) insideRadius)))
    (displacement : FiniteVector.carrier source)
    (insideRadius : FiniteVector.ball
      (FiniteVector.zeroVector source) radius displacement) :
    NormallyConvergent
      (substitutionCoefficients outer.coefficients inner radius positive
        below) displacement := by
  let point : FiniteVector.carrier target := fun coordinate =>
    normalSum (inner coordinate) displacement
      (FiniteVector.ball_mono (below coordinate) insideRadius)
  refine ⟨normalSum outer point (outerInside displacement insideRadius),
    fun count => ?_⟩
  rw [substituted_partial_magnitudes_eq_truncation
    outer.coefficients inner radius positive below zeroConstant
    displacement count]
  have truncationInside : FiniteVector.ball
      (FiniteVector.zeroVector source)
      (outerTruncationSeries outer.coefficients inner radius positive
        below count).radius displacement := by
    simpa only [outerTruncationSeries, finiteSeriesSum_radius] using
      insideRadius
  exact le_trans
    (partial_sum_tail_le_normalSum
      (outerTruncationSeries outer.coefficients inner radius positive below
        count) displacement truncationInside count)
    (outer_truncation_normalSum_le_outer outer inner radius positive below
      count displacement insideRadius
      (outerInside displacement insideRadius))

@[expose] public noncomputable def substituteSeriesWithin
    {source target : Nat}
    (outer : Convergent target)
    (inner : Fin target → Convergent source)
    (radius : selection.Carrier) (positive : lt zero radius)
    (below : ∀ coordinate, le radius (inner coordinate).radius)
    (zeroConstant : ∀ coordinate,
      (inner coordinate).coefficients
        (MultiIndex.zeroIndex source) = zero)
    (outerInside : ∀ displacement : FiniteVector.carrier source,
      ∀ insideRadius : FiniteVector.ball
        (FiniteVector.zeroVector source) radius displacement,
        FiniteVector.ball (FiniteVector.zeroVector target)
          outer.radius
          (fun coordinate => normalSum (inner coordinate) displacement
            (FiniteVector.ball_mono (below coordinate) insideRadius))) :
    Convergent source where
  coefficients := substitutionCoefficients outer.coefficients inner
    radius positive below
  radius := radius
  radiusPositive := positive
  normalOn := substitution_normally_convergent outer inner radius positive
    below zeroConstant outerInside

@[expose] public noncomputable def substituteSeries
    {source target : Nat}
    (outer : Convergent target)
    (inner : Fin target → Convergent source)
    (zeroConstant : ∀ coordinate,
      (inner coordinate).coefficients
        (MultiIndex.zeroIndex source) = zero) :
    Convergent source := by
  let witness := substitution_common_radius outer inner zeroConstant
  let radius := Classical.choose witness
  let positiveWitness := Classical.choose_spec witness
  let positive := Classical.choose positiveWitness
  let belowWitness := Classical.choose_spec positiveWitness
  let below := Classical.choose belowWitness
  let outerInside := Classical.choose_spec belowWitness
  exact substituteSeriesWithin outer inner radius positive below
    zeroConstant outerInside

end

end Problib.Analysis.Real.PowerSeries
