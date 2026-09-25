module

public import Problib.Analysis.Real.PowerSeries.SubstitutionFinite

/-! A finite substituted Taylor polynomial has a normal sum no larger than
the outer series' normal sum at the vector of inner normal sums. -/

set_option autoImplicit false

namespace Problib.Analysis.Real.PowerSeries

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real.SignedSeries

noncomputable section

private instance : Std.Associative (α := selection.Carrier) add :=
  ⟨fun left middle right => add_assoc left middle right⟩

public theorem monomial_nonnegative {dimension : Nat}
    (index : MultiIndex.carrier dimension)
    (point : FiniteVector.carrier dimension)
    (nonnegative : ∀ coordinate, le zero (point coordinate)) :
    le zero (MultiIndex.monomial dimension index point) := by
  induction dimension with
  | zero => exact one_nonnegative
  | succ dimension induction =>
      change le zero (mul (power (point 0) (index 0))
        (MultiIndex.monomial dimension
          (fun coordinate => index coordinate.succ)
          (fun coordinate => point coordinate.succ)))
      exact mul_nonnegative (power_nonnegative (nonnegative 0) _)
        (induction (fun coordinate => index coordinate.succ)
          (fun coordinate => point coordinate.succ)
          (fun coordinate => nonnegative coordinate.succ))

public theorem shellMagnitude_at_nonnegative_point
    {dimension degreeValue : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (point : FiniteVector.carrier dimension)
    (nonnegative : ∀ coordinate, le zero (point coordinate)) :
    shellMagnitude coefficients point degreeValue =
      (MultiIndex.degreeShell dimension degreeValue).foldr
        (fun index total => add
          (mul (abs (coefficients index))
            (MultiIndex.monomial dimension index point)) total) zero := by
  unfold shellMagnitude
  congr 1
  funext index total
  rw [abs_mul, abs_of_nonnegative
    (monomial_nonnegative index point nonnegative)]

private theorem foldr_flatmap_sum {α β : Type}
    (indices : List α) (fibers : α → List β)
    (term : β → selection.Carrier) :
    (indices.flatMap fibers).foldr
      (fun index total => add (term index) total) zero =
    indices.foldr (fun index total =>
      add ((fibers index).foldr
        (fun entry accumulated => add (term entry) accumulated) zero)
        total) zero := by
  induction indices with
  | nil => rfl
  | cons index rest induction =>
      rw [List.flatMap_cons, List.foldr_append, List.foldr_cons]
      have foldr_init (entries : List β) (initial : selection.Carrier) :
          entries.foldr (fun entry total => add (term entry) total)
            initial =
          add (entries.foldr (fun entry total => add (term entry) total)
            zero) initial := by
        induction entries with
        | nil => rw [List.foldr_nil, List.foldr_nil, zero_add]
        | cons entry tail induction =>
            rw [List.foldr_cons, List.foldr_cons, induction, add_assoc]
      rw [foldr_init, induction]

private theorem foldr_range_partial_sum (values : Nat → selection.Carrier)
    (count : Nat) :
    (List.range count).foldr
      (fun index total => add (values index) total) zero =
    partialSum values count := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.range_succ, List.foldr_append]
      change (List.range count).foldr
        (fun index total => add (values index) total)
        (add (values count) zero) = partialSum values (count + 1)
      rw [add_zero]
      have foldr_init (entries : List Nat)
          (initial : selection.Carrier) :
          entries.foldr (fun index total => add (values index) total)
            initial =
          add (entries.foldr (fun index total => add (values index) total)
            zero) initial := by
        induction entries with
        | nil => rw [List.foldr_nil, List.foldr_nil, zero_add]
        | cons index rest induction =>
            rw [List.foldr_cons, List.foldr_cons, induction, add_assoc]
      rw [foldr_init, induction, partial_sum_succ]

public theorem outer_indices_majorant_eq_partial_sum
    {target : Nat}
    (outer : Convergent target)
    (point : FiniteVector.carrier target)
    (nonnegative : ∀ coordinate, le zero (point coordinate))
    (degreeBound : Nat) :
    (outerIndicesThrough target degreeBound).foldr
      (fun index total => add
        (mul (abs (outer.coefficients index))
          (MultiIndex.monomial target index point)) total) zero =
    partialSum (fullShellMagnitudes outer point) (degreeBound + 1) := by
  unfold outerIndicesThrough
  rw [foldr_flatmap_sum]
  have shellEqual : ∀ degreeValue,
      (MultiIndex.degreeShell target degreeValue).foldr
        (fun index total => add
          (mul (abs (outer.coefficients index))
            (MultiIndex.monomial target index point)) total) zero =
      fullShellMagnitudes outer point degreeValue := by
    intro degreeValue
    exact (shellMagnitude_at_nonnegative_point outer.coefficients
      point nonnegative).symm
  have mappedEqual :
      (List.range (degreeBound + 1)).foldr
        (fun degreeValue total => add
          ((MultiIndex.degreeShell target degreeValue).foldr
            (fun index accumulated => add
              (mul (abs (outer.coefficients index))
                (MultiIndex.monomial target index point)) accumulated)
            zero) total) zero =
      (List.range (degreeBound + 1)).foldr
        (fun degreeValue total => add
          (fullShellMagnitudes outer point degreeValue) total) zero := by
    congr 1
    funext degreeValue total
    rw [shellEqual]
  rw [mappedEqual, foldr_range_partial_sum]

public theorem outer_indices_value_eq_partial_sum
    {target : Nat}
    (outer : Convergent target)
    (point : FiniteVector.carrier target)
    (degreeBound : Nat) :
    (outerIndicesThrough target degreeBound).foldr
      (fun index total => add
        (mul (outer.coefficients index)
          (MultiIndex.monomial target index point)) total) zero =
    partialSum (fullShellTerms outer point) (degreeBound + 1) := by
  unfold outerIndicesThrough
  rw [foldr_flatmap_sum]
  change (List.range (degreeBound + 1)).foldr
    (fun degreeValue total => add
      (shellTerm outer.coefficients point degreeValue) total) zero = _
  exact foldr_range_partial_sum _ (degreeBound + 1)

public theorem outer_truncation_normalSum_le_outer
    {source target : Nat}
    (outer : Convergent target)
    (inner : Fin target → Convergent source)
    (radius : selection.Carrier) (positive : lt zero radius)
    (below : ∀ coordinate, le radius (inner coordinate).radius)
    (degreeBound : Nat)
    (displacement : FiniteVector.carrier source)
    (insideRadius : FiniteVector.ball
      (FiniteVector.zeroVector source) radius displacement)
    (insideOuter : FiniteVector.ball
      (FiniteVector.zeroVector target) outer.radius
      (fun coordinate => normalSum (inner coordinate) displacement
        (FiniteVector.ball_mono (below coordinate) insideRadius))) :
    le (normalSum
        (outerTruncationSeries outer.coefficients inner radius positive
          below degreeBound) displacement
        (by simpa only [outerTruncationSeries,
          finiteSeriesSum_radius] using insideRadius))
      (normalSum outer
        (fun coordinate => normalSum (inner coordinate) displacement
          (FiniteVector.ball_mono (below coordinate) insideRadius))
        insideOuter) := by
  let point : FiniteVector.carrier target := fun coordinate =>
    normalSum (inner coordinate) displacement
      (FiniteVector.ball_mono (below coordinate) insideRadius)
  have pointNonnegative : ∀ coordinate, le zero (point coordinate) :=
    fun coordinate => normalSum_nonnegative (inner coordinate)
      displacement (FiniteVector.ball_mono (below coordinate)
        insideRadius)
  have finiteBound := outer_truncation_normalSum_le
    outer.coefficients inner radius positive below degreeBound
    displacement insideRadius
  rw [outer_indices_majorant_eq_partial_sum outer point
    pointNonnegative degreeBound] at finiteBound
  exact le_trans finiteBound
    (partial_sum_le_sum_nonnegative
      (fun degreeValue => shellMagnitude_nonnegative
        outer.coefficients point degreeValue)
      (fullShellMagnitudes_summable outer point insideOuter)
      (degreeBound + 1))

public theorem substitution_common_radius
    {source target : Nat}
    (outer : Convergent target)
    (inner : Fin target → Convergent source)
    (zeroConstant : ∀ coordinate,
      (inner coordinate).coefficients
        (MultiIndex.zeroIndex source) = zero) :
    ∃ radius : selection.Carrier,
      ∃ _positive : lt zero radius,
      ∃ below : ∀ coordinate, le radius (inner coordinate).radius,
      ∀ displacement : FiniteVector.carrier source,
        ∀ insideRadius : FiniteVector.ball
          (FiniteVector.zeroVector source) radius displacement,
        FiniteVector.ball (FiniteVector.zeroVector target)
          outer.radius
          (fun coordinate => normalSum (inner coordinate) displacement
            (FiniteVector.ball_mono (below coordinate) insideRadius)) := by
  rcases component_normal_sums_small_radius inner zeroConstant
    outer.radiusPositive with
    ⟨radius, radiusPositive, below, componentBound⟩
  refine ⟨radius, radiusPositive, below,
    fun displacement insideRadius coordinate => ?_⟩
  rcases componentBound displacement insideRadius coordinate with
    ⟨componentInside, componentSmall⟩
  have nonnegative := normalSum_nonnegative (inner coordinate)
    displacement componentInside
  change lt (abs (sub (normalSum (inner coordinate) displacement
    (FiniteVector.ball_mono (below coordinate) insideRadius)) zero))
      outer.radius
  rw [sub_zero, abs_of_nonnegative nonnegative]
  exact componentSmall

end

end Problib.Analysis.Real.PowerSeries
