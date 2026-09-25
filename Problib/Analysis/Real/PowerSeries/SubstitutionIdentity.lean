module

public import Problib.Analysis.Real.PowerSeries.SubstitutionUniform

/-! The normally convergent canonical substitution has the composed value.
The proof compares one common finite coefficient prefix with finite outer
Taylor polynomials and controls the latter's tails by a shared majorant. -/

set_option autoImplicit false

namespace Problib.Analysis.Real.PowerSeries

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real.SignedSeries

noncomputable section

public theorem finite_prefix_converges_to_value {dimension : Nat}
    (series : Convergent dimension)
    (displacement : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius displacement) :
    Problib.Analysis.Real.ConvergesTo
      (fun count => add
        (series.coefficients (MultiIndex.zeroIndex dimension))
        (partialSum (tailTerms series.coefficients displacement) count))
      (value series displacement inside) := by
  have tailConverges := partial_sum_converges
    (tailTerms series.coefficients displacement)
    (summable_of_absolute_bound (series.absoluteOn displacement inside))
  have combined := converges_to_add
    (converges_to_const
      (series.coefficients (MultiIndex.zeroIndex dimension)))
    tailConverges
  exact combined

public theorem outer_prefix_converges_to_value {dimension : Nat}
    (series : Convergent dimension)
    (displacement : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius displacement) :
    Problib.Analysis.Real.ConvergesTo
      (fun count => partialSum (fullShellTerms series displacement)
        (count + 1))
      (value series displacement inside) := by
  have fullAbsolute := fullShellTerms_absolute series displacement inside
  have fullConverges := converges_to_shift
    (partial_sum_converges (fullShellTerms series displacement)
      (summable_of_absolute_bound fullAbsolute))
  rw [full_shell_sum_eq_value series displacement inside] at fullConverges
  exact fullConverges

public theorem substituteSeriesWithin_value
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
    value (substituteSeriesWithin outer inner radius positive below
      zeroConstant outerInside) displacement insideRadius =
    value outer
      (innerValuePoint inner radius below displacement insideRadius)
      (innerValuePoint_inside_outer outer inner radius below zeroConstant
        outerInside displacement insideRadius) := by
  let composite := substituteSeriesWithin outer inner radius positive below
    zeroConstant outerInside
  let innerPoint := innerValuePoint inner radius below displacement
    insideRadius
  let outerPointInside := innerValuePoint_inside_outer outer inner radius
    below zeroConstant outerInside displacement insideRadius
  have prefixConvergesOuter : Problib.Analysis.Real.ConvergesTo
      (fun count => add
        (composite.coefficients (MultiIndex.zeroIndex source))
        (partialSum (tailTerms composite.coefficients displacement)
          count))
      (value outer innerPoint outerPointInside) := by
    intro tolerance tolerancePositive
    let half := Problib.Analysis.Real.half tolerance
    have halfPositive := Problib.Analysis.Real.half_positive
      tolerancePositive
    rcases outer_prefix_converges_to_value outer innerPoint
      outerPointInside half halfPositive with
      ⟨outerStage, outerClose⟩
    rcases outer_truncations_uniform_tail outer inner radius positive
      below outerInside displacement insideRadius halfPositive with
      ⟨truncStage, truncClose⟩
    refine ⟨max outerStage truncStage, fun count later => ?_⟩
    let truncation := outerTruncationSeries outer.coefficients inner radius
      positive below count
    have prefixEqual := substituted_prefix_eq_truncation outer inner
      radius positive below zeroConstant displacement count count
      (Nat.le_refl count)
    have tailClose := truncClose count count
      (Nat.le_trans (Nat.le_max_right _ _) later)
    have outerNear := outerClose count
      (Nat.le_trans (Nat.le_max_left _ _) later)
    dsimp only at outerNear
    rw [← outer_truncation_value_eq_outer_partial_sum outer inner radius
      positive below count displacement insideRadius] at outerNear
    change lt (abs (sub
      (add (composite.coefficients (MultiIndex.zeroIndex source))
        (partialSum (tailTerms composite.coefficients displacement) count))
      (value outer innerPoint outerPointInside))) tolerance
    change add (composite.coefficients (MultiIndex.zeroIndex source))
      (partialSum (tailTerms composite.coefficients displacement) count) =
      add (truncation.coefficients (MultiIndex.zeroIndex source))
        (partialSum (tailTerms truncation.coefficients displacement) count)
        at prefixEqual
    rw [prefixEqual]
    let prefixValue := add (truncation.coefficients
      (MultiIndex.zeroIndex source))
      (partialSum (tailTerms truncation.coefficients displacement) count)
    let truncValue := value truncation displacement
      (by simpa only [truncation, outerTruncationSeries,
        finiteSeriesSum_radius] using insideRadius)
    have firstNear : lt (abs (sub prefixValue truncValue)) half := by
      rw [abs_sub_comm]
      exact tailClose
    have triangle : le (abs (sub prefixValue
        (value outer innerPoint outerPointInside)))
        (add (abs (sub prefixValue truncValue))
          (abs (sub truncValue
            (value outer innerPoint outerPointInside)))) := by
      rw [← sub_add_sub prefixValue truncValue
        (value outer innerPoint outerPointInside)]
      exact abs_add_le _ _
    have combined := add_lt_add firstNear outerNear
    rw [Problib.Analysis.Real.add_half] at combined
    exact lt_of_le_of_lt triangle combined
  exact (converges_to_unique
    (finite_prefix_converges_to_value composite displacement insideRadius)
    prefixConvergesOuter)

end

end Problib.Analysis.Real.PowerSeries
