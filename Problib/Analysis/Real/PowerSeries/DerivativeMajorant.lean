module

public import Problib.Analysis.Real.PowerSeries.MonomialDerivative

/-! Coefficientwise majorants for finite differentiated degree shells. -/

set_option autoImplicit false

namespace Problib.Analysis.Real.PowerSeries

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real.SignedSeries

noncomputable section

private instance : Std.Associative (α := selection.Carrier) add :=
  ⟨fun left middle right => add_assoc left middle right⟩

private instance : Std.Commutative (α := selection.Carrier) add :=
  ⟨add_comm⟩

private instance : Std.Associative (α := selection.Carrier) mul :=
  ⟨fun left middle right => mul_assoc left middle right⟩

private instance : Std.Commutative (α := selection.Carrier) mul :=
  ⟨mul_comm⟩

@[expose] public def coefficientMagnitude {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (indices : List (MultiIndex.carrier dimension)) : selection.Carrier :=
  indices.foldr (fun index total => add (abs (coefficients index)) total)
    zero

public theorem coefficientMagnitude_nonnegative {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (indices : List (MultiIndex.carrier dimension)) :
    le zero (coefficientMagnitude coefficients indices) := by
  induction indices with
  | nil => exact le_refl zero
  | cons index rest induction =>
      change le zero (add (abs (coefficients index))
        (coefficientMagnitude coefficients rest))
      exact add_nonnegative (abs_nonnegative _) induction

public theorem finite_shell_bound_le_degree {dimension degreeValue : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (indices : List (MultiIndex.carrier dimension))
    (homogeneous : ∀ index, index ∈ indices →
      MultiIndex.degree dimension index = degreeValue)
    {radius : selection.Carrier} (nonnegative : le zero radius)
    (selected : Fin dimension) :
    le (finiteShellSliceBound coefficients indices radius selected)
      (mul (powerDerivative radius degreeValue)
        (coefficientMagnitude coefficients indices)) := by
  induction indices with
  | nil =>
      change le zero (mul (powerDerivative radius degreeValue) zero)
      rw [mul_zero]
      exact le_refl zero
  | cons index rest induction =>
      have degree := homogeneous index List.mem_cons_self
      have tailHomogeneous : ∀ later, later ∈ rest →
          MultiIndex.degree dimension later = degreeValue :=
        fun later member => homogeneous later (List.mem_cons_of_mem index member)
      have indexBound := monomialSliceBound_le_degree dimension index
        nonnegative selected
      rw [degree] at indexBound
      have termBound := mul_le_mul_nonnegative_left indexBound
        (abs_nonnegative (coefficients index))
      have tailBound := induction tailHomogeneous
      have combined := add_le_add termBound tailBound
      change le (add
          (mul (abs (coefficients index))
            (monomialSliceBound dimension index radius selected))
          (finiteShellSliceBound coefficients rest radius selected))
        (mul (powerDerivative radius degreeValue)
          (add (abs (coefficients index))
            (coefficientMagnitude coefficients rest)))
      rw [mul_add]
      have equal : mul (abs (coefficients index))
          (powerDerivative radius degreeValue) =
          mul (powerDerivative radius degreeValue)
            (abs (coefficients index)) := mul_comm _ _
      rw [equal] at combined
      exact combined

public theorem shellMagnitude_constant_eq {dimension degreeValue : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    {radius : selection.Carrier} (nonnegative : le zero radius) :
    shellMagnitude coefficients (fun _ => radius) degreeValue =
      mul (power radius degreeValue)
        (coefficientMagnitude coefficients
          (MultiIndex.degreeShell dimension degreeValue)) := by
  have go : ∀ indices : List (MultiIndex.carrier dimension),
      (∀ index, index ∈ indices →
        MultiIndex.degree dimension index = degreeValue) →
      indices.foldr
        (fun index total => add
          (abs (mul (coefficients index)
            (MultiIndex.monomial dimension index (fun _ => radius))))
          total) zero =
      mul (power radius degreeValue)
        (coefficientMagnitude coefficients indices) := by
    intro indices
    induction indices with
    | nil =>
        intro _
        simp only [List.foldr_nil, coefficientMagnitude, mul_zero]
    | cons index rest induction =>
        intro homogeneous
        have degree := homogeneous index List.mem_cons_self
        have tailHomogeneous : ∀ later, later ∈ rest →
            MultiIndex.degree dimension later = degreeValue :=
          fun later member => homogeneous later
            (List.mem_cons_of_mem index member)
        simp only [List.foldr_cons]
        rw [MultiIndex.monomial_constant_radius, degree, abs_mul,
          abs_of_nonnegative (power_nonnegative nonnegative degreeValue),
          induction tailHomogeneous]
        change add
            (mul (abs (coefficients index)) (power radius degreeValue))
            (mul (power radius degreeValue)
              (coefficientMagnitude coefficients rest)) =
          mul (power radius degreeValue)
            (add (abs (coefficients index))
              (coefficientMagnitude coefficients rest))
        rw [mul_add, mul_comm (abs (coefficients index))]
  exact go (MultiIndex.degreeShell dimension degreeValue)
    (fun index member => MultiIndex.degree_of_mem_shell member)

/-- After shrinking by a ratio below one, every coordinate's finite shell
Lipschitz bound is controlled by the original coefficientwise shell majorant. -/
public theorem shell_derivative_bound_le_large {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    {ratio radius : selection.Carrier}
    (ratioNonnegative : le zero ratio) (ratioBelowOne : lt ratio one)
    (radiusPositive : lt zero radius)
    (selected : Fin dimension) (degreeValue : Nat) :
    le (finiteShellSliceBound coefficients
        (MultiIndex.degreeShell dimension degreeValue)
        (mul ratio radius) selected)
      (mul (mul (inverse (sub one ratio)) (inverse radius))
        (shellMagnitude coefficients (fun _ => radius) degreeValue)) := by
  have shrunkNonnegative := mul_nonnegative ratioNonnegative radiusPositive.left
  have source := finite_shell_bound_le_degree coefficients
    (MultiIndex.degreeShell dimension degreeValue)
    (fun index member => MultiIndex.degree_of_mem_shell member)
    shrunkNonnegative selected
  let coefficientSum := coefficientMagnitude coefficients
    (MultiIndex.degreeShell dimension degreeValue)
  have coefficientNonnegative := coefficientMagnitude_nonnegative
    coefficients (MultiIndex.degreeShell dimension degreeValue)
  rw [shellMagnitude_constant_eq coefficients radiusPositive.left]
  cases degreeValue with
  | zero =>
      change le _
        (mul (mul (inverse (sub one ratio)) (inverse radius))
          (mul (power radius 0) coefficientSum))
      have sourceZero : le
          (finiteShellSliceBound coefficients
            (MultiIndex.degreeShell dimension 0)
            (mul ratio radius) selected) zero := by
        simpa only [powerDerivative, zero_mul] using source
      have constantNonnegative :
          le zero (mul (inverse (sub one ratio)) (inverse radius)) :=
        mul_nonnegative
          (le_of_lt (inverse_of_positive_positive
            (sub_positive_iff.mpr ratioBelowOne)))
          (le_of_lt (inverse_of_positive_positive radiusPositive))
      have magnitudeNonnegative :
          le zero (mul (power radius 0) coefficientSum) := by
        rw [power_zero, one_mul]
        exact coefficientNonnegative
      exact le_trans sourceZero
        (mul_nonnegative constantNonnegative magnitudeNonnegative)
  | succ count =>
      have derivativeBound := powerDerivative_shrunk
        ratioNonnegative ratioBelowOne radiusPositive count
      have scaled := mul_le_mul_nonnegative_right derivativeBound
        coefficientNonnegative
      have combined := le_trans source scaled
      change le _
        (mul (mul (inverse (sub one ratio)) (inverse radius))
          (mul (power radius (count + 1)) coefficientSum))
      simpa only [mul_assoc] using combined

/-- The finite-difference bounds of all degree shells form a summable
nonnegative series on every sufficiently smaller coordinate box. -/
public theorem derivative_shell_bounds_summable {dimension : Nat}
    (series : Convergent dimension)
    {ratio radius : selection.Carrier}
    (ratioNonnegative : le zero ratio) (ratioBelowOne : lt ratio one)
    (radiusPositive : lt zero radius)
    (inside : FiniteVector.ball (FiniteVector.zeroVector dimension)
      series.radius (fun _ => radius))
    (selected : Fin dimension) :
    Summable (fun degreeValue => finiteShellSliceBound series.coefficients
      (MultiIndex.degreeShell dimension degreeValue)
      (mul ratio radius) selected) := by
  let constant := mul (inverse (sub one ratio)) (inverse radius)
  let original := fullShellMagnitudes series (fun _ => radius)
  let bounds := fun degreeValue => finiteShellSliceBound series.coefficients
    (MultiIndex.degreeShell dimension degreeValue)
    (mul ratio radius) selected
  have constantNonnegative : le zero constant :=
    mul_nonnegative
      (le_of_lt (inverse_of_positive_positive
        (sub_positive_iff.mpr ratioBelowOne)))
      (le_of_lt (inverse_of_positive_positive radiusPositive))
  have originalNonnegative : ∀ degreeValue,
      le zero (original degreeValue) :=
    fun degreeValue => shellMagnitude_nonnegative series.coefficients
      (fun _ => radius) degreeValue
  let originalSummable := fullShellMagnitudes_summable series
    (fun _ => radius) inside
  have boundNonnegative : ∀ degreeValue, le zero (bounds degreeValue) :=
    fun degreeValue => finiteShellSliceBound_nonnegative
      series.coefficients (MultiIndex.degreeShell dimension degreeValue)
      (mul_nonnegative ratioNonnegative radiusPositive.left) selected
  have pointwise : ∀ degreeValue,
      le (bounds degreeValue) (mul constant (original degreeValue)) :=
    fun degreeValue => shell_derivative_bound_le_large
      series.coefficients ratioNonnegative ratioBelowOne radiusPositive
      selected degreeValue
  apply summable_of_nonnegative_bounded boundNonnegative
  refine ⟨mul constant (sum original originalSummable), fun count => ?_⟩
  have finiteBound := partial_sum_le pointwise count
  rw [partial_sum_scale] at finiteBound
  exact le_trans finiteBound
    (mul_le_mul_nonnegative_left
      (partial_sum_le_sum_nonnegative originalNonnegative
        originalSummable count)
      constantNonnegative)

public theorem derivative_shell_tails_small {dimension : Nat}
    (series : Convergent dimension)
    {ratio radius : selection.Carrier}
    (ratioNonnegative : le zero ratio) (ratioBelowOne : lt ratio one)
    (radiusPositive : lt zero radius)
    (inside : FiniteVector.ball (FiniteVector.zeroVector dimension)
      series.radius (fun _ => radius))
    (selected : Fin dimension)
    {tolerance : selection.Carrier} (tolerancePositive : lt zero tolerance) :
    ∃ stage : Nat, ∀ start, stage ≤ start → ∀ count,
      lt (degreeTailBound series.coefficients start count
        (mul ratio radius) selected) tolerance := by
  let bounds := fun degreeValue => finiteShellSliceBound series.coefficients
    (MultiIndex.degreeShell dimension degreeValue)
    (mul ratio radius) selected
  have certificate := derivative_shell_bounds_summable series
    ratioNonnegative ratioBelowOne radiusPositive inside selected
  rcases summable_cauchy certificate tolerance tolerancePositive with
    ⟨stage, close⟩
  refine ⟨stage, fun start later count => ?_⟩
  have nonnegativeBounds : ∀ degreeValue, le zero (bounds degreeValue) :=
    fun degreeValue => finiteShellSliceBound_nonnegative
      series.coefficients (MultiIndex.degreeShell dimension degreeValue)
      (mul_nonnegative ratioNonnegative radiusPositive.left) selected
  have tailNonnegative := partial_sum_nonnegative
    (fun index => nonnegativeBounds (start + index)) count
  have identity :
      degreeTailBound series.coefficients start count
        (mul ratio radius) selected =
      sub (partialSum bounds (start + count))
        (partialSum bounds start) := by
    have append := partial_sum_append bounds start count
    rw [append, add_sub_self]
    rfl
  have near := close (start + count) start
    (Nat.le_trans later (Nat.le_add_right _ _)) later
  rw [← identity] at near
  have nonnegativeTail : le zero
      (degreeTailBound series.coefficients start count
        (mul ratio radius) selected) := tailNonnegative
  rw [abs_of_nonnegative nonnegativeTail] at near
  exact near

public theorem degreeTail_difference_small {dimension : Nat}
    (series : Convergent dimension)
    {ratio radius : selection.Carrier}
    (ratioNonnegative : le zero ratio) (ratioBelowOne : lt ratio one)
    (radiusPositive : lt zero radius)
    (inside : FiniteVector.ball (FiniteVector.zeroVector dimension)
      series.radius (fun _ => radius))
    (selected : Fin dimension)
    {tolerance : selection.Carrier} (tolerancePositive : lt zero tolerance) :
    ∃ stage : Nat, ∀ start, stage ≤ start → ∀ count,
      ∀ point : FiniteVector.carrier dimension,
      (∀ coordinate, le (abs (point coordinate)) (mul ratio radius)) →
      ∀ first second : selection.Carrier,
      le (abs first) (mul ratio radius) →
      le (abs second) (mul ratio radius) →
      le (abs (sub
        (degreeTail series.coefficients start count
          (replaceCoordinate point selected second))
        (degreeTail series.coefficients start count
          (replaceCoordinate point selected first))))
        (mul tolerance (abs (sub second first))) := by
  rcases derivative_shell_tails_small series ratioNonnegative
    ratioBelowOne radiusPositive inside selected tolerancePositive with
    ⟨stage, small⟩
  refine ⟨stage, fun start later count point coordinates first second
    firstBound secondBound => ?_⟩
  have finiteBound := degreeTail_difference_bound series.coefficients
    start count point (mul_nonnegative ratioNonnegative radiusPositive.left)
    coordinates selected firstBound secondBound
  have scaled := mul_le_mul_nonnegative_right
    (le_of_lt (small start later count))
    (abs_nonnegative (sub second first))
  exact le_trans finiteBound scaled

end

end Problib.Analysis.Real.PowerSeries
