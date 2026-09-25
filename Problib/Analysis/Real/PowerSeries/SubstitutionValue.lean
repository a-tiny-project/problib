module

public import Problib.Analysis.Real.PowerSeries.SubstitutionConvergence

/-! Identify the value of a substituted series by its finite outer Taylor
polynomials and an absolute rearrangement. -/

set_option autoImplicit false

namespace Problib.Analysis.Real.PowerSeries

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real.SignedSeries

noncomputable section

@[expose] public noncomputable def innerValuePoint
    {source target : Nat}
    (inner : Fin target → Convergent source)
    (radius : selection.Carrier)
    (below : ∀ coordinate, le radius (inner coordinate).radius)
    (displacement : FiniteVector.carrier source)
    (insideRadius : FiniteVector.ball
      (FiniteVector.zeroVector source) radius displacement) :
    FiniteVector.carrier target :=
  fun coordinate => value (inner coordinate) displacement
    (FiniteVector.ball_mono (below coordinate) insideRadius)

public theorem innerValuePoint_inside_outer
    {source target : Nat}
    (outer : Convergent target)
    (inner : Fin target → Convergent source)
    (radius : selection.Carrier)
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
    FiniteVector.ball (FiniteVector.zeroVector target) outer.radius
      (innerValuePoint inner radius below displacement insideRadius) := by
  intro coordinate
  have valueBound := abs_value_le_normalSum_zero_constant
    (inner coordinate) (zeroConstant coordinate) displacement
    (FiniteVector.ball_mono (below coordinate) insideRadius)
  have normalInside := outerInside displacement insideRadius coordinate
  have normalNonnegative := normalSum_nonnegative (inner coordinate)
    displacement (FiniteVector.ball_mono (below coordinate) insideRadius)
  change lt (abs (sub (normalSum (inner coordinate) displacement
    (FiniteVector.ball_mono (below coordinate) insideRadius)) zero))
      outer.radius at normalInside
  rw [sub_zero, abs_of_nonnegative normalNonnegative] at normalInside
  change lt (abs (sub (value (inner coordinate) displacement
    (FiniteVector.ball_mono (below coordinate) insideRadius)) zero))
    outer.radius
  rw [sub_zero]
  exact lt_of_le_of_lt valueBound normalInside

public theorem outer_truncation_value_eq_outer_partial_sum
    {source target : Nat}
    (outer : Convergent target)
    (inner : Fin target → Convergent source)
    (radius : selection.Carrier) (positive : lt zero radius)
    (below : ∀ coordinate, le radius (inner coordinate).radius)
    (degreeBound : Nat)
    (displacement : FiniteVector.carrier source)
    (insideRadius : FiniteVector.ball
      (FiniteVector.zeroVector source) radius displacement) :
    value (outerTruncationSeries outer.coefficients inner radius positive
      below degreeBound) displacement
      (by simpa only [outerTruncationSeries,
        finiteSeriesSum_radius] using insideRadius) =
    partialSum
      (fullShellTerms outer
        (innerValuePoint inner radius below displacement insideRadius))
      (degreeBound + 1) := by
  rw [outer_truncation_value outer.coefficients inner radius positive below
    degreeBound displacement insideRadius]
  exact outer_indices_value_eq_partial_sum outer
    (innerValuePoint inner radius below displacement insideRadius)
    degreeBound

public theorem substituted_prefix_eq_truncation
    {source target : Nat}
    (outer : Convergent target)
    (inner : Fin target → Convergent source)
    (radius : selection.Carrier) (positive : lt zero radius)
    (below : ∀ coordinate, le radius (inner coordinate).radius)
    (zeroConstant : ∀ coordinate,
      (inner coordinate).coefficients
        (MultiIndex.zeroIndex source) = zero)
    (displacement : FiniteVector.carrier source)
    (count degreeBound : Nat) (included : count ≤ degreeBound) :
    add
      ((substitutionCoefficients outer.coefficients inner radius positive
        below) (MultiIndex.zeroIndex source))
      (partialSum
        (tailTerms (substitutionCoefficients outer.coefficients inner
          radius positive below) displacement) count) =
    add
      ((outerTruncationSeries outer.coefficients inner radius positive below
        degreeBound).coefficients (MultiIndex.zeroIndex source))
      (partialSum
        (tailTerms
          (outerTruncationSeries outer.coefficients inner radius positive
            below degreeBound).coefficients displacement) count) := by
  have constantEqual :
      (substitutionCoefficients outer.coefficients inner radius positive
        below) (MultiIndex.zeroIndex source) =
      (outerTruncationSeries outer.coefficients inner radius positive below
        degreeBound).coefficients (MultiIndex.zeroIndex source) := by
    rw [outer_truncation_coefficients]
    exact (substitutionCoefficientThrough_stable outer.coefficients inner
      radius positive below zeroConstant (MultiIndex.zeroIndex source)
      degreeBound (by rw [MultiIndex.degree_zeroIndex]; omega)).symm
  have tailsEqual :
      partialSum
        (tailTerms (substitutionCoefficients outer.coefficients inner
          radius positive below) displacement) count =
      partialSum
        (tailTerms
          (outerTruncationSeries outer.coefficients inner radius positive
            below degreeBound).coefficients displacement) count := by
    apply partial_sum_congr_below count
    intro degreeValue degreeBelow
    apply shellTerm_congr_on displacement
    intro index member
    have indexDegree := MultiIndex.degree_of_mem_shell member
    have bound : MultiIndex.degree source index ≤ degreeBound := by
      omega
    rw [outer_truncation_coefficients]
    exact (substitutionCoefficientThrough_stable outer.coefficients inner
      radius positive below zeroConstant index degreeBound bound).symm
  rw [constantEqual, tailsEqual]

end

end Problib.Analysis.Real.PowerSeries
