module

public import Problib.Analysis.Real.PowerSeries.FiniteDerivative

/-! Coordinate slices of finite multiindex monomials. -/

set_option autoImplicit false

namespace Problib.Analysis.Real.PowerSeries

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real
open Problib.Analysis.Real.SignedSeries

noncomputable section

@[expose] public def replaceCoordinate {dimension : Nat}
    (point : FiniteVector.carrier dimension)
    (selected : Fin dimension) (argument : selection.Carrier) :
    FiniteVector.carrier dimension :=
  fun coordinate => if coordinate = selected then argument else point coordinate

public theorem replaceCoordinate_at_point {dimension : Nat}
    (point : FiniteVector.carrier dimension)
    (selected : Fin dimension) :
    replaceCoordinate point selected (point selected) = point := by
  funext coordinate
  by_cases equal : coordinate = selected
  · subst coordinate
    simp [replaceCoordinate]
  · simp [replaceCoordinate, equal]

@[expose] public def monomialSlice :
    (dimension : Nat) → MultiIndex.carrier dimension →
    FiniteVector.carrier dimension → Fin dimension →
    selection.Carrier → selection.Carrier
  | 0, _, _, selected => selected.elim0
  | dimension + 1, index, point, selected =>
      Fin.cases
        (fun argument => mul (power argument (index 0))
          (MultiIndex.monomial dimension
            (fun coordinate => index coordinate.succ)
            (fun coordinate => point coordinate.succ)))
        (fun coordinate argument => mul (power (point 0) (index 0))
          (monomialSlice dimension
            (fun later => index later.succ)
            (fun later => point later.succ) coordinate argument))
        selected

@[expose] public def monomialSliceDerivative :
    (dimension : Nat) → MultiIndex.carrier dimension →
    FiniteVector.carrier dimension → Fin dimension → selection.Carrier
  | 0, _, _, selected => selected.elim0
  | dimension + 1, index, point, selected =>
      Fin.cases
        (mul (powerDerivative (point 0) (index 0))
          (MultiIndex.monomial dimension
            (fun coordinate => index coordinate.succ)
            (fun coordinate => point coordinate.succ)))
        (fun coordinate => mul (power (point 0) (index 0))
          (monomialSliceDerivative dimension
            (fun later => index later.succ)
            (fun later => point later.succ) coordinate))
        selected

@[expose] public def monomialSliceBound :
    (dimension : Nat) → MultiIndex.carrier dimension →
    selection.Carrier → Fin dimension → selection.Carrier
  | 0, _, _, selected => selected.elim0
  | dimension + 1, index, radius, selected =>
      Fin.cases
        (mul (powerDerivative radius (index 0))
          (MultiIndex.monomial dimension
            (fun coordinate => index coordinate.succ)
            (fun _ => radius)))
        (fun coordinate => mul (power radius (index 0))
          (monomialSliceBound dimension
            (fun later => index later.succ) radius coordinate))
        selected

public theorem monomialSliceBound_nonnegative (dimension : Nat)
    (index : MultiIndex.carrier dimension)
    {radius : selection.Carrier} (nonnegative : le zero radius)
    (selected : Fin dimension) :
    le zero (monomialSliceBound dimension index radius selected) := by
  induction dimension with
  | zero => exact selected.elim0
  | succ dimension induction =>
      cases selected using Fin.cases with
      | zero =>
          change le zero (mul (powerDerivative radius (index 0))
            (MultiIndex.monomial dimension
              (fun coordinate => index coordinate.succ)
              (fun _ => radius)))
          rw [MultiIndex.monomial_constant_radius]
          exact mul_nonnegative
            (powerDerivative_nonnegative nonnegative (index 0))
            (power_nonnegative nonnegative _)
      | succ selected =>
          change le zero (mul (power radius (index 0))
            (monomialSliceBound dimension
              (fun coordinate => index coordinate.succ) radius selected))
          exact mul_nonnegative (power_nonnegative nonnegative _)
            (induction (fun coordinate => index coordinate.succ) selected)

public theorem monomialSliceBound_le_degree (dimension : Nat)
    (index : MultiIndex.carrier dimension)
    {radius : selection.Carrier} (nonnegative : le zero radius)
    (selected : Fin dimension) :
    le (monomialSliceBound dimension index radius selected)
      (powerDerivative radius (MultiIndex.degree dimension index)) := by
  induction dimension with
  | zero => exact selected.elim0
  | succ dimension induction =>
      let tailIndex : MultiIndex.carrier dimension :=
        fun coordinate => index coordinate.succ
      cases selected using Fin.cases with
      | zero =>
          change le
            (mul (powerDerivative radius (index 0))
              (MultiIndex.monomial dimension tailIndex (fun _ => radius)))
            (powerDerivative radius
              (index 0 + MultiIndex.degree dimension tailIndex))
          rw [MultiIndex.monomial_constant_radius,
            powerDerivative_add]
          have nonnegativeTerm := mul_nonnegative
            (power_nonnegative nonnegative (index 0))
            (powerDerivative_nonnegative nonnegative
              (MultiIndex.degree dimension tailIndex))
          have included := add_le_add
            (le_refl (mul (powerDerivative radius (index 0))
              (power radius (MultiIndex.degree dimension tailIndex))))
            nonnegativeTerm
          rwa [add_zero] at included
      | succ selected =>
          change le
            (mul (power radius (index 0))
              (monomialSliceBound dimension tailIndex radius selected))
            (powerDerivative radius
              (index 0 + MultiIndex.degree dimension tailIndex))
          rw [powerDerivative_add]
          have tailBound := induction tailIndex selected
          have scaled := mul_le_mul_nonnegative_left tailBound
            (power_nonnegative nonnegative (index 0))
          have nonnegativeTerm := mul_nonnegative
            (powerDerivative_nonnegative nonnegative (index 0))
            (power_nonnegative nonnegative
              (MultiIndex.degree dimension tailIndex))
          have included := add_le_add nonnegativeTerm
            (le_refl (mul (power radius (index 0))
              (powerDerivative radius
                (MultiIndex.degree dimension tailIndex))))
          rw [zero_add] at included
          exact le_trans scaled included

/-- Every coordinate slice of a monomial has an explicit finite-difference
bound, obtained from the product rule for natural powers. -/
public theorem monomialSlice_difference_bound (dimension : Nat)
    (index : MultiIndex.carrier dimension)
    (point : FiniteVector.carrier dimension)
    {radius : selection.Carrier} (nonnegative : le zero radius)
    (coordinates : ∀ coordinate, le (abs (point coordinate)) radius)
    (selected : Fin dimension)
    {first second : selection.Carrier}
    (firstBound : le (abs first) radius)
    (secondBound : le (abs second) radius) :
    le (abs (sub
      (monomialSlice dimension index point selected second)
      (monomialSlice dimension index point selected first)))
      (mul (monomialSliceBound dimension index radius selected)
        (abs (sub second first))) := by
  induction dimension with
  | zero => exact selected.elim0
  | succ dimension induction =>
      cases selected using Fin.cases with
      | zero =>
          let tail := MultiIndex.monomial dimension
            (fun coordinate => index coordinate.succ)
            (fun coordinate => point coordinate.succ)
          let tailRadius := MultiIndex.monomial dimension
            (fun coordinate => index coordinate.succ)
            (fun _ => radius)
          have tailBound : le (abs tail) tailRadius := by
            change le (abs tail)
              (MultiIndex.monomial dimension
                (fun coordinate => index coordinate.succ)
                (fun _ => radius))
            rw [MultiIndex.monomial_constant_radius]
            exact MultiIndex.abs_monomial_le_power dimension
              (fun coordinate => index coordinate.succ)
              (fun coordinate => point coordinate.succ)
              nonnegative (fun coordinate => coordinates coordinate.succ)
          have powerBound := power_difference_bound nonnegative
            firstBound secondBound (index 0)
          have firstStep := mul_le_mul_nonnegative_right powerBound
            (abs_nonnegative tail)
          have secondStep := mul_le_mul_nonnegative_left tailBound
            (mul_nonnegative
              (powerDerivative_nonnegative nonnegative (index 0))
              (abs_nonnegative (sub second first)))
          have combined := le_trans firstStep secondStep
          change le
            (abs (sub (mul (power second (index 0)) tail)
              (mul (power first (index 0)) tail)))
            (mul (mul (powerDerivative radius (index 0)) tailRadius)
              (abs (sub second first)))
          rw [← sub_mul, abs_mul]
          have equal :
              mul (mul (powerDerivative radius (index 0))
                (abs (sub second first))) tailRadius =
              mul (mul (powerDerivative radius (index 0)) tailRadius)
                (abs (sub second first)) := by
            rw [mul_assoc, mul_comm (abs (sub second first)) tailRadius,
              ← mul_assoc]
          rw [equal] at combined
          exact combined
      | succ selected =>
          let head := power (point 0) (index 0)
          have headBound : le (abs head) (power radius (index 0)) := by
            change le (abs (power (point 0) (index 0))) _
            rw [abs_power]
            exact MultiIndex.power_mono_base (abs_nonnegative (point 0))
              (coordinates 0) (index 0)
          have tailBound := induction
            (fun coordinate => index coordinate.succ)
            (fun coordinate => point coordinate.succ)
            (fun coordinate => coordinates coordinate.succ)
            selected
          have firstStep := mul_le_mul_nonnegative_left tailBound
            (abs_nonnegative head)
          have secondStep := mul_le_mul_nonnegative_right headBound
            (mul_nonnegative
              (monomialSliceBound_nonnegative dimension
                (fun coordinate => index coordinate.succ) nonnegative selected)
              (abs_nonnegative (sub second first)))
          have combined := le_trans firstStep secondStep
          change le
            (abs (sub (mul head
              (monomialSlice dimension
                (fun coordinate => index coordinate.succ)
                (fun coordinate => point coordinate.succ) selected second))
              (mul head
                (monomialSlice dimension
                  (fun coordinate => index coordinate.succ)
                  (fun coordinate => point coordinate.succ) selected first))))
            (mul (mul (power radius (index 0))
              (monomialSliceBound dimension
                (fun coordinate => index coordinate.succ) radius selected))
              (abs (sub second first)))
          rw [← mul_sub, abs_mul]
          simpa only [mul_assoc] using combined

public theorem monomialSlice_at_point (dimension : Nat)
    (index : MultiIndex.carrier dimension)
    (point : FiniteVector.carrier dimension)
    (selected : Fin dimension) :
    monomialSlice dimension index point selected (point selected) =
      MultiIndex.monomial dimension index point := by
  induction dimension with
  | zero => exact selected.elim0
  | succ dimension induction =>
      cases selected using Fin.cases with
      | zero => rfl
      | succ selected =>
          change mul (power (point 0) (index 0))
              (monomialSlice dimension
                (fun coordinate => index coordinate.succ)
                (fun coordinate => point coordinate.succ)
                selected (point selected.succ)) =
            mul (power (point 0) (index 0))
              (MultiIndex.monomial dimension
                (fun coordinate => index coordinate.succ)
                (fun coordinate => point coordinate.succ))
          rw [induction]

public theorem monomialSlice_eq_replaced (dimension : Nat)
    (index : MultiIndex.carrier dimension)
    (point : FiniteVector.carrier dimension)
    (selected : Fin dimension) (argument : selection.Carrier) :
    monomialSlice dimension index point selected argument =
      MultiIndex.monomial dimension index
        (replaceCoordinate point selected argument) := by
  induction dimension with
  | zero => exact selected.elim0
  | succ dimension induction =>
      cases selected using Fin.cases with
      | zero =>
          change mul (power argument (index 0))
              (MultiIndex.monomial dimension
                (fun coordinate => index coordinate.succ)
                (fun coordinate => point coordinate.succ)) =
            mul (power ((replaceCoordinate point 0 argument) 0) (index 0))
              (MultiIndex.monomial dimension
                (fun coordinate => index coordinate.succ)
                (fun coordinate => (replaceCoordinate point 0 argument)
                  coordinate.succ))
          congr 1
      | succ selected =>
          change mul (power (point 0) (index 0))
              (monomialSlice dimension
                (fun coordinate => index coordinate.succ)
                (fun coordinate => point coordinate.succ) selected argument) =
            mul (power ((replaceCoordinate point selected.succ argument) 0)
                (index 0))
              (MultiIndex.monomial dimension
                (fun coordinate => index coordinate.succ)
                (fun coordinate =>
                  (replaceCoordinate point selected.succ argument)
                    coordinate.succ))
          have head : (replaceCoordinate point selected.succ argument) 0 =
              point 0 := by
            have distinct : (0 : Fin (dimension + 1)) ≠
                selected.succ :=
              fun equal => Fin.succ_ne_zero selected equal.symm
            simp [replaceCoordinate, distinct]
          rw [head]
          have tail :
              (fun coordinate : Fin dimension =>
                (replaceCoordinate point selected.succ argument)
                  coordinate.succ) =
              replaceCoordinate (fun coordinate => point coordinate.succ)
                selected argument := by
            funext coordinate
            simp [replaceCoordinate]
          rw [tail, induction]

public theorem has_derivative_monomialSlice (dimension : Nat)
    (index : MultiIndex.carrier dimension)
    (point : FiniteVector.carrier dimension)
    (selected : Fin dimension) :
    HasDerivative (monomialSlice dimension index point selected)
      (point selected)
      (monomialSliceDerivative dimension index point selected) := by
  induction dimension with
  | zero => exact selected.elim0
  | succ dimension induction =>
      cases selected using Fin.cases with
      | zero =>
          have product := hasDerivative_mul
            (has_derivative_power (point 0) (index 0))
            (hasDerivative_const
              (MultiIndex.monomial dimension
                (fun coordinate => index coordinate.succ)
                (fun coordinate => point coordinate.succ)) (point 0))
          change HasDerivative
            (fun argument => mul (power argument (index 0))
              (MultiIndex.monomial dimension
                (fun coordinate => index coordinate.succ)
                (fun coordinate => point coordinate.succ)))
            (point 0)
            (mul (powerDerivative (point 0) (index 0))
              (MultiIndex.monomial dimension
                (fun coordinate => index coordinate.succ)
                (fun coordinate => point coordinate.succ)))
          simpa only [mul_zero, add_zero] using product
      | succ selected =>
          have product := hasDerivative_mul
            (hasDerivative_const (power (point 0) (index 0))
              (point selected.succ))
            (induction (fun coordinate => index coordinate.succ)
              (fun coordinate => point coordinate.succ) selected)
          change HasDerivative
            (fun argument => mul (power (point 0) (index 0))
              (monomialSlice dimension
                (fun coordinate => index coordinate.succ)
                (fun coordinate => point coordinate.succ)
                selected argument))
            (point selected.succ)
            (mul (power (point 0) (index 0))
              (monomialSliceDerivative dimension
                (fun coordinate => index coordinate.succ)
                (fun coordinate => point coordinate.succ) selected))
          simpa only [zero_mul, zero_add] using product

public theorem monomialSliceDerivative_zero_high (dimension : Nat)
    (index : MultiIndex.carrier dimension)
    (selected : Fin dimension)
    (high : 2 ≤ MultiIndex.degree dimension index) :
    monomialSliceDerivative dimension index
      (FiniteVector.zeroVector dimension) selected = zero := by
  induction dimension with
  | zero => exact selected.elim0
  | succ dimension induction =>
      let tailIndex : MultiIndex.carrier dimension :=
        fun coordinate => index coordinate.succ
      cases selected using Fin.cases with
      | zero =>
          change mul (powerDerivative zero (index 0))
            (MultiIndex.monomial dimension tailIndex
              (FiniteVector.zeroVector dimension)) = zero
          cases head : index 0 with
          | zero =>
              rw [powerDerivative_zero_at_zero, zero_mul]
          | succ count =>
              cases count with
              | zero =>
                  have tailPositive : 0 <
                      MultiIndex.degree dimension tailIndex := by
                    change 2 ≤ index 0 +
                      MultiIndex.degree dimension tailIndex at high
                    omega
                  rw [powerDerivative_one_at_zero,
                    MultiIndex.monomial_zero_of_positive_degree
                      dimension tailIndex tailPositive,
                    mul_zero]
              | succ count =>
                  rw [powerDerivative_high_at_zero, zero_mul]
      | succ selected =>
          change mul (power zero (index 0))
            (monomialSliceDerivative dimension tailIndex
              (FiniteVector.zeroVector dimension) selected) = zero
          cases head : index 0 with
          | zero =>
              have tailHigh : 2 ≤ MultiIndex.degree dimension tailIndex := by
                change 2 ≤ index 0 +
                  MultiIndex.degree dimension tailIndex at high
                omega
              rw [power_zero, one_mul]
              exact induction tailIndex selected tailHigh
          | succ count =>
              rw [power_succ, zero_mul, zero_mul]

public theorem monomialSliceDerivative_unit (dimension : Nat)
    (selected : Fin dimension) :
    monomialSliceDerivative dimension (MultiIndex.unitIndex selected)
      (FiniteVector.zeroVector dimension) selected = one := by
  induction dimension with
  | zero => exact selected.elim0
  | succ dimension induction =>
      cases selected using Fin.cases with
      | zero =>
          have tailZero :
              (fun coordinate : Fin dimension =>
                MultiIndex.unitIndex (0 : Fin (dimension + 1))
                  coordinate.succ) =
              MultiIndex.zeroIndex dimension := by
            funext coordinate
            have distinct : coordinate.succ ≠
                (0 : Fin (dimension + 1)) := Fin.succ_ne_zero coordinate
            simp [MultiIndex.unitIndex, MultiIndex.zeroIndex, distinct]
          change mul (powerDerivative zero 1)
            (MultiIndex.monomial dimension
              (fun coordinate => MultiIndex.unitIndex
                (0 : Fin (dimension + 1)) coordinate.succ)
              (FiniteVector.zeroVector dimension)) = one
          rw [tailZero, powerDerivative_one_at_zero,
            MultiIndex.monomial_zeroIndex, one_mul]
      | succ selected =>
          have headZero : MultiIndex.unitIndex selected.succ
              (0 : Fin (dimension + 1)) = 0 := by
            have distinct : (0 : Fin (dimension + 1)) ≠
                selected.succ :=
              fun equal => Fin.succ_ne_zero selected equal.symm
            simp [MultiIndex.unitIndex, distinct]
          have tailUnit :
              (fun coordinate : Fin dimension =>
                MultiIndex.unitIndex selected.succ coordinate.succ) =
              MultiIndex.unitIndex selected := by
            funext coordinate
            simp [MultiIndex.unitIndex]
          change mul
            (power zero (MultiIndex.unitIndex selected.succ 0))
            (monomialSliceDerivative dimension
              (fun coordinate => MultiIndex.unitIndex
                selected.succ coordinate.succ)
              (FiniteVector.zeroVector dimension) selected) = one
          rw [headZero, tailUnit, power_zero, one_mul, induction]

public theorem monomialSliceDerivative_zero_coordinate (dimension : Nat)
    (index : MultiIndex.carrier dimension)
    (selected : Fin dimension) (vanished : index selected = 0) :
    monomialSliceDerivative dimension index
      (FiniteVector.zeroVector dimension) selected = zero := by
  induction dimension with
  | zero => exact selected.elim0
  | succ dimension induction =>
      cases selected using Fin.cases with
      | zero =>
          change mul (powerDerivative zero (index 0))
            (MultiIndex.monomial dimension
              (fun coordinate => index coordinate.succ)
              (FiniteVector.zeroVector dimension)) = zero
          rw [vanished, powerDerivative_zero_at_zero, zero_mul]
      | succ selected =>
          change mul (power zero (index 0))
            (monomialSliceDerivative dimension
              (fun coordinate => index coordinate.succ)
              (FiniteVector.zeroVector dimension) selected) = zero
          rw [induction (fun coordinate => index coordinate.succ)
            selected vanished, mul_zero]

public theorem monomialSliceDerivative_degree_one_other (dimension : Nat)
    (index : MultiIndex.carrier dimension) (selected : Fin dimension)
    (degreeOne : MultiIndex.degree dimension index = 1)
    (different : index ≠ MultiIndex.unitIndex selected) :
    monomialSliceDerivative dimension index
      (FiniteVector.zeroVector dimension) selected = zero := by
  have coordinateAtMost := MultiIndex.coordinate_le_degree
    dimension index selected
  rw [degreeOne] at coordinateAtMost
  have coordinateZero : index selected = 0 := by
    by_cases vanished : index selected = 0
    · exact vanished
    · have coordinateOne : index selected = 1 := by omega
      exact False.elim (different
        (MultiIndex.eq_unitIndex_of_degree_one_at_coordinate
          dimension index selected degreeOne coordinateOne))
  exact monomialSliceDerivative_zero_coordinate dimension index
    selected coordinateZero

@[expose] public def finiteShellSlice {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (indices : List (MultiIndex.carrier dimension))
    (point : FiniteVector.carrier dimension)
    (selected : Fin dimension) (argument : selection.Carrier) :
    selection.Carrier :=
  indices.foldr
    (fun index total => add
      (mul (coefficients index)
        (monomialSlice dimension index point selected argument)) total)
    zero

@[expose] public def finiteShellSliceDerivative {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (indices : List (MultiIndex.carrier dimension))
    (point : FiniteVector.carrier dimension)
    (selected : Fin dimension) : selection.Carrier :=
  indices.foldr
    (fun index total => add
      (mul (coefficients index)
        (monomialSliceDerivative dimension index point selected)) total)
    zero

public theorem finite_shell_derivative_zero_high {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (degreeValue : Nat) (high : 2 ≤ degreeValue)
    (selected : Fin dimension) :
    finiteShellSliceDerivative coefficients
      (MultiIndex.degreeShell dimension degreeValue)
      (FiniteVector.zeroVector dimension) selected = zero := by
  have go : ∀ indices : List (MultiIndex.carrier dimension),
      (∀ index, index ∈ indices →
        MultiIndex.degree dimension index = degreeValue) →
      finiteShellSliceDerivative coefficients indices
        (FiniteVector.zeroVector dimension) selected = zero := by
    intro indices
    induction indices with
    | nil => intro _; rfl
    | cons index rest induction =>
        intro homogeneous
        have indexHigh : 2 ≤ MultiIndex.degree dimension index := by
          rw [homogeneous index List.mem_cons_self]
          exact high
        have tailHomogeneous : ∀ later, later ∈ rest →
            MultiIndex.degree dimension later = degreeValue :=
          fun later member => homogeneous later
            (List.mem_cons_of_mem index member)
        change add (mul (coefficients index)
            (monomialSliceDerivative dimension index
              (FiniteVector.zeroVector dimension) selected))
          (finiteShellSliceDerivative coefficients rest
            (FiniteVector.zeroVector dimension) selected) = zero
        rw [monomialSliceDerivative_zero_high dimension index selected
          indexHigh, mul_zero, induction tailHomogeneous, zero_add]
  exact go (MultiIndex.degreeShell dimension degreeValue)
    (fun index member => MultiIndex.degree_of_mem_shell member)

public theorem finite_shell_derivative_one {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (selected : Fin dimension) :
    finiteShellSliceDerivative coefficients
      (MultiIndex.degreeShell dimension 1)
      (FiniteVector.zeroVector dimension) selected =
    coefficients (MultiIndex.unitIndex selected) := by
  classical
  let unit := MultiIndex.unitIndex selected
  have on :
      mul (coefficients unit)
        (monomialSliceDerivative dimension unit
          (FiniteVector.zeroVector dimension) selected) =
      coefficients unit := by
    rw [show unit = MultiIndex.unitIndex selected by rfl,
      monomialSliceDerivative_unit, mul_one]
  have off : ∀ index : MultiIndex.carrier dimension,
      index ≠ unit →
      mul (coefficients index)
        (monomialSliceDerivative dimension index
          (FiniteVector.zeroVector dimension) selected) = zero := by
    intro index different
    cases degree : MultiIndex.degree dimension index with
    | zero =>
        have zeroIndex := MultiIndex.eq_zeroIndex_of_degree_zero
          dimension index degree
        have zeroCoordinate : index selected = 0 := by
          rw [zeroIndex]
          rfl
        rw [monomialSliceDerivative_zero_coordinate dimension index
          selected zeroCoordinate, mul_zero]
    | succ count =>
        cases count with
        | zero =>
            rw [monomialSliceDerivative_degree_one_other dimension
              index selected degree different, mul_zero]
        | succ count =>
            have high : 2 ≤ MultiIndex.degree dimension index := by
              rw [degree]
              omega
            rw [monomialSliceDerivative_zero_high dimension index
              selected high, mul_zero]
  have folded := fold_single_support
    (MultiIndex.degreeShell dimension 1)
    (MultiIndex.degreeShell_nodup dimension 1)
    (fun index => mul (coefficients index)
      (monomialSliceDerivative dimension index
        (FiniteVector.zeroVector dimension) selected))
    unit (coefficients unit) on off
  change finiteShellSliceDerivative coefficients
      (MultiIndex.degreeShell dimension 1)
      (FiniteVector.zeroVector dimension) selected =
    if unit ∈ MultiIndex.degreeShell dimension 1 then
      coefficients unit else zero at folded
  rw [folded, if_pos (MultiIndex.mem_degreeShell_iff.mpr
    (MultiIndex.degree_unitIndex dimension selected))]

public theorem finite_shell_derivative_zero {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (selected : Fin dimension) :
    finiteShellSliceDerivative coefficients
      (MultiIndex.degreeShell dimension 0)
      (FiniteVector.zeroVector dimension) selected = zero := by
  rw [MultiIndex.degreeShell_zero_singleton]
  have coordinateZero :
      (MultiIndex.zeroIndex dimension) selected = 0 := rfl
  change add
    (mul (coefficients (MultiIndex.zeroIndex dimension))
      (monomialSliceDerivative dimension
        (MultiIndex.zeroIndex dimension)
        (FiniteVector.zeroVector dimension) selected)) zero = zero
  rw [monomialSliceDerivative_zero_coordinate dimension
    (MultiIndex.zeroIndex dimension) selected coordinateZero,
    mul_zero, zero_add]

@[expose] public def finiteShellSliceBound {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (indices : List (MultiIndex.carrier dimension))
    (radius : selection.Carrier)
    (selected : Fin dimension) : selection.Carrier :=
  indices.foldr
    (fun index total => add
      (mul (abs (coefficients index))
        (monomialSliceBound dimension index radius selected)) total) zero

public theorem finiteShellSliceBound_nonnegative {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (indices : List (MultiIndex.carrier dimension))
    {radius : selection.Carrier} (nonnegative : le zero radius)
    (selected : Fin dimension) :
    le zero (finiteShellSliceBound coefficients indices radius selected) := by
  induction indices with
  | nil => exact le_refl zero
  | cons index rest induction =>
      change le zero (add
        (mul (abs (coefficients index))
          (monomialSliceBound dimension index radius selected))
        (finiteShellSliceBound coefficients rest radius selected))
      exact add_nonnegative
        (mul_nonnegative (abs_nonnegative _)
          (monomialSliceBound_nonnegative dimension index nonnegative
            selected)) induction

public theorem finiteShellSlice_difference_bound {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (indices : List (MultiIndex.carrier dimension))
    (point : FiniteVector.carrier dimension)
    {radius : selection.Carrier} (nonnegative : le zero radius)
    (coordinates : ∀ coordinate, le (abs (point coordinate)) radius)
    (selected : Fin dimension)
    {first second : selection.Carrier}
    (firstBound : le (abs first) radius)
    (secondBound : le (abs second) radius) :
    le (abs (sub
      (finiteShellSlice coefficients indices point selected second)
      (finiteShellSlice coefficients indices point selected first)))
      (mul (finiteShellSliceBound coefficients indices radius selected)
        (abs (sub second first))) := by
  induction indices with
  | nil =>
      change le (abs (sub zero zero))
        (mul zero (abs (sub second first)))
      rw [sub_self, abs_zero, zero_mul]
      exact le_refl zero
  | cons index rest induction =>
      have split :
          sub (finiteShellSlice coefficients (index :: rest) point
              selected second)
            (finiteShellSlice coefficients (index :: rest) point
              selected first) =
          add
            (mul (coefficients index)
              (sub (monomialSlice dimension index point selected second)
                (monomialSlice dimension index point selected first)))
            (sub (finiteShellSlice coefficients rest point selected second)
              (finiteShellSlice coefficients rest point selected first)) := by
        change sub (add _ _) (add _ _) = add (mul _ (sub _ _)) (sub _ _)
        rw [add_sub_add_comm, ← mul_sub]
        rfl
      rw [split]
      have triangle := abs_add_le
        (mul (coefficients index)
          (sub (monomialSlice dimension index point selected second)
            (monomialSlice dimension index point selected first)))
        (sub (finiteShellSlice coefficients rest point selected second)
          (finiteShellSlice coefficients rest point selected first))
      rw [abs_mul] at triangle
      have termBound := monomialSlice_difference_bound dimension index
        point nonnegative coordinates selected firstBound secondBound
      have scaled := mul_le_mul_nonnegative_left termBound
        (abs_nonnegative (coefficients index))
      have tailBound := induction
      have combined := le_trans triangle (add_le_add scaled tailBound)
      change le _
        (mul (add
          (mul (abs (coefficients index))
            (monomialSliceBound dimension index radius selected))
          (finiteShellSliceBound coefficients rest radius selected))
          (abs (sub second first)))
      rw [add_mul]
      have equal :
          mul (abs (coefficients index))
            (mul (monomialSliceBound dimension index radius selected)
              (abs (sub second first))) =
          mul (mul (abs (coefficients index))
            (monomialSliceBound dimension index radius selected))
            (abs (sub second first)) := by
        rw [mul_assoc]
      rw [equal] at combined
      exact combined

public theorem has_derivative_finiteShellSlice {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (indices : List (MultiIndex.carrier dimension))
    (point : FiniteVector.carrier dimension)
    (selected : Fin dimension) :
    HasDerivative (finiteShellSlice coefficients indices point selected)
      (point selected)
      (finiteShellSliceDerivative coefficients indices point selected) := by
  induction indices with
  | nil =>
      change HasDerivative (fun _ => zero) (point selected) zero
      exact hasDerivative_const zero (point selected)
  | cons index rest induction =>
      have termDerivative := hasDerivative_smul (coefficients index)
        (has_derivative_monomialSlice dimension index point selected)
      have combined := hasDerivative_add termDerivative induction
      change HasDerivative
        (fun argument => add
          (mul (coefficients index)
            (monomialSlice dimension index point selected argument))
          (finiteShellSlice coefficients rest point selected argument))
        (point selected)
        (add
          (mul (coefficients index)
            (monomialSliceDerivative dimension index point selected))
          (finiteShellSliceDerivative coefficients rest point selected))
      exact combined

public theorem finiteShellSlice_at_point {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (indices : List (MultiIndex.carrier dimension))
    (point : FiniteVector.carrier dimension)
    (selected : Fin dimension) :
    finiteShellSlice coefficients indices point selected (point selected) =
      indices.foldr
        (fun index total => add
          (mul (coefficients index)
            (MultiIndex.monomial dimension index point)) total) zero := by
  induction indices with
  | nil => rfl
  | cons index rest induction =>
      change add (mul (coefficients index)
          (monomialSlice dimension index point selected (point selected)))
          (finiteShellSlice coefficients rest point selected (point selected)) =
        add (mul (coefficients index)
          (MultiIndex.monomial dimension index point))
          (rest.foldr
            (fun later total => add
              (mul (coefficients later)
                (MultiIndex.monomial dimension later point)) total) zero)
      rw [monomialSlice_at_point, induction]

public theorem finiteShellSlice_eq_replaced {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (indices : List (MultiIndex.carrier dimension))
    (point : FiniteVector.carrier dimension)
    (selected : Fin dimension) (argument : selection.Carrier) :
    finiteShellSlice coefficients indices point selected argument =
      indices.foldr
        (fun index total => add
          (mul (coefficients index)
            (MultiIndex.monomial dimension index
              (replaceCoordinate point selected argument))) total) zero := by
  induction indices with
  | nil => rfl
  | cons index rest induction =>
      change add (mul (coefficients index)
          (monomialSlice dimension index point selected argument))
          (finiteShellSlice coefficients rest point selected argument) =
        add (mul (coefficients index)
          (MultiIndex.monomial dimension index
            (replaceCoordinate point selected argument)))
          (rest.foldr
            (fun later total => add
              (mul (coefficients later)
                (MultiIndex.monomial dimension later
                  (replaceCoordinate point selected argument))) total) zero)
      rw [monomialSlice_eq_replaced, induction]

public theorem has_derivative_shell_coordinate {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (degreeValue : Nat)
    (point : FiniteVector.carrier dimension)
    (selected : Fin dimension) :
    HasDerivative
      (fun argument => shellTerm coefficients
        (replaceCoordinate point selected argument) degreeValue)
      (point selected)
      (finiteShellSliceDerivative coefficients
        (MultiIndex.degreeShell dimension degreeValue) point selected) := by
  have equal :
      (fun argument => shellTerm coefficients
        (replaceCoordinate point selected argument) degreeValue) =
      finiteShellSlice coefficients
        (MultiIndex.degreeShell dimension degreeValue) point selected := by
    funext argument
    exact (finiteShellSlice_eq_replaced coefficients
      (MultiIndex.degreeShell dimension degreeValue)
      point selected argument).symm
  rw [equal]
  exact has_derivative_finiteShellSlice coefficients
    (MultiIndex.degreeShell dimension degreeValue) point selected

@[expose] public def degreePolynomial {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (count : Nat) (point : FiniteVector.carrier dimension) :
    selection.Carrier :=
  partialSum (shellTerm coefficients point) count

@[expose] public def degreePolynomialDerivative {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (count : Nat) (point : FiniteVector.carrier dimension)
    (selected : Fin dimension) : selection.Carrier :=
  partialSum
    (fun degreeValue => finiteShellSliceDerivative coefficients
      (MultiIndex.degreeShell dimension degreeValue) point selected) count

@[expose] public def degreePolynomialBound {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (count : Nat) (radius : selection.Carrier)
    (selected : Fin dimension) : selection.Carrier :=
  partialSum
    (fun degreeValue => finiteShellSliceBound coefficients
      (MultiIndex.degreeShell dimension degreeValue) radius selected) count

public theorem degreePolynomialDerivative_stable_zero {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (selected : Fin dimension) (count : Nat) :
    degreePolynomialDerivative coefficients (count + 2)
      (FiniteVector.zeroVector dimension) selected =
    degreePolynomialDerivative coefficients 2
      (FiniteVector.zeroVector dimension) selected := by
  induction count with
  | zero => rfl
  | succ count induction =>
      have step :
          degreePolynomialDerivative coefficients ((count + 2) + 1)
            (FiniteVector.zeroVector dimension) selected =
          add
            (degreePolynomialDerivative coefficients (count + 2)
              (FiniteVector.zeroVector dimension) selected)
            (finiteShellSliceDerivative coefficients
              (MultiIndex.degreeShell dimension (count + 2))
              (FiniteVector.zeroVector dimension) selected) := by
        unfold degreePolynomialDerivative
        rw [partial_sum_succ]
      rw [show count + 1 + 2 = (count + 2) + 1 by omega,
        step, finite_shell_derivative_zero_high coefficients (count + 2)
          (by omega) selected, add_zero, induction]

public theorem degreePolynomialDerivative_two {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (selected : Fin dimension) :
    degreePolynomialDerivative coefficients 2
      (FiniteVector.zeroVector dimension) selected =
    coefficients (MultiIndex.unitIndex selected) := by
  unfold degreePolynomialDerivative
  rw [show (2 : Nat) = 1 + 1 by rfl,
    partial_sum_succ, partial_sum_succ, partial_sum_zero]
  change add
      (add zero
        (finiteShellSliceDerivative coefficients
          (MultiIndex.degreeShell dimension 0)
          (FiniteVector.zeroVector dimension) selected))
      (finiteShellSliceDerivative coefficients
        (MultiIndex.degreeShell dimension 1)
        (FiniteVector.zeroVector dimension) selected) =
    coefficients (MultiIndex.unitIndex selected)
  rw [finite_shell_derivative_zero, finite_shell_derivative_one,
    zero_add, zero_add]

public theorem degreePolynomial_difference_bound {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (count : Nat) (point : FiniteVector.carrier dimension)
    {radius : selection.Carrier} (nonnegative : le zero radius)
    (coordinates : ∀ coordinate, le (abs (point coordinate)) radius)
    (selected : Fin dimension)
    {first second : selection.Carrier}
    (firstBound : le (abs first) radius)
    (secondBound : le (abs second) radius) :
    le (abs (sub
      (degreePolynomial coefficients count
        (replaceCoordinate point selected second))
      (degreePolynomial coefficients count
        (replaceCoordinate point selected first))))
      (mul (degreePolynomialBound coefficients count radius selected)
        (abs (sub second first))) := by
  induction count with
  | zero =>
      change le (abs (sub zero zero))
        (mul zero (abs (sub second first)))
      rw [sub_self, abs_zero, zero_mul]
      exact le_refl zero
  | succ count induction =>
      have split :
          sub (degreePolynomial coefficients (count + 1)
              (replaceCoordinate point selected second))
            (degreePolynomial coefficients (count + 1)
              (replaceCoordinate point selected first)) =
          add
            (sub (degreePolynomial coefficients count
                (replaceCoordinate point selected second))
              (degreePolynomial coefficients count
                (replaceCoordinate point selected first)))
            (sub (shellTerm coefficients
                (replaceCoordinate point selected second) count)
              (shellTerm coefficients
                (replaceCoordinate point selected first) count)) := by
        unfold degreePolynomial
        rw [partial_sum_succ, partial_sum_succ, add_sub_add_comm]
      rw [split]
      have shellEqual : ∀ argument,
          shellTerm coefficients (replaceCoordinate point selected argument)
            count =
          finiteShellSlice coefficients
            (MultiIndex.degreeShell dimension count) point selected argument := by
        intro argument
        exact (finiteShellSlice_eq_replaced coefficients
          (MultiIndex.degreeShell dimension count)
          point selected argument).symm
      have shellBound := finiteShellSlice_difference_bound coefficients
        (MultiIndex.degreeShell dimension count) point nonnegative
        coordinates selected firstBound secondBound
      rw [← shellEqual second, ← shellEqual first] at shellBound
      have triangle := abs_add_le
        (sub (degreePolynomial coefficients count
          (replaceCoordinate point selected second))
          (degreePolynomial coefficients count
            (replaceCoordinate point selected first)))
        (sub (shellTerm coefficients
          (replaceCoordinate point selected second) count)
          (shellTerm coefficients
            (replaceCoordinate point selected first) count))
      have combined := le_trans triangle
        (add_le_add induction shellBound)
      change le _
        (mul (add (degreePolynomialBound coefficients count radius selected)
          (finiteShellSliceBound coefficients
            (MultiIndex.degreeShell dimension count) radius selected))
          (abs (sub second first)))
      rw [add_mul]
      exact combined

@[expose] public def degreeTail {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (start count : Nat) (point : FiniteVector.carrier dimension) :
    selection.Carrier :=
  partialSum (fun index => shellTerm coefficients point (start + index)) count

@[expose] public def degreeTailBound {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (start count : Nat) (radius : selection.Carrier)
    (selected : Fin dimension) : selection.Carrier :=
  partialSum (fun index => finiteShellSliceBound coefficients
    (MultiIndex.degreeShell dimension (start + index)) radius selected) count

public theorem degreeTail_difference_bound {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (start count : Nat) (point : FiniteVector.carrier dimension)
    {radius : selection.Carrier} (nonnegative : le zero radius)
    (coordinates : ∀ coordinate, le (abs (point coordinate)) radius)
    (selected : Fin dimension)
    {first second : selection.Carrier}
    (firstBound : le (abs first) radius)
    (secondBound : le (abs second) radius) :
    le (abs (sub
      (degreeTail coefficients start count
        (replaceCoordinate point selected second))
      (degreeTail coefficients start count
        (replaceCoordinate point selected first))))
      (mul (degreeTailBound coefficients start count radius selected)
        (abs (sub second first))) := by
  induction count with
  | zero =>
      change le (abs (sub zero zero))
        (mul zero (abs (sub second first)))
      rw [sub_self, abs_zero, zero_mul]
      exact le_refl zero
  | succ count induction =>
      have split :
          sub (degreeTail coefficients start (count + 1)
              (replaceCoordinate point selected second))
            (degreeTail coefficients start (count + 1)
              (replaceCoordinate point selected first)) =
          add
            (sub (degreeTail coefficients start count
                (replaceCoordinate point selected second))
              (degreeTail coefficients start count
                (replaceCoordinate point selected first)))
            (sub (shellTerm coefficients
                (replaceCoordinate point selected second) (start + count))
              (shellTerm coefficients
                (replaceCoordinate point selected first) (start + count))) := by
        unfold degreeTail
        rw [partial_sum_succ, partial_sum_succ, add_sub_add_comm]
      rw [split]
      have shellEqual : ∀ argument,
          shellTerm coefficients (replaceCoordinate point selected argument)
            (start + count) =
          finiteShellSlice coefficients
            (MultiIndex.degreeShell dimension (start + count))
            point selected argument := by
        intro argument
        exact (finiteShellSlice_eq_replaced coefficients
          (MultiIndex.degreeShell dimension (start + count))
          point selected argument).symm
      have shellBound := finiteShellSlice_difference_bound coefficients
        (MultiIndex.degreeShell dimension (start + count)) point
        nonnegative coordinates selected firstBound secondBound
      rw [← shellEqual second, ← shellEqual first] at shellBound
      have triangle := abs_add_le
        (sub (degreeTail coefficients start count
          (replaceCoordinate point selected second))
          (degreeTail coefficients start count
            (replaceCoordinate point selected first)))
        (sub (shellTerm coefficients
          (replaceCoordinate point selected second) (start + count))
          (shellTerm coefficients
            (replaceCoordinate point selected first) (start + count)))
      have combined := le_trans triangle
        (add_le_add induction shellBound)
      change le _
        (mul (add (degreeTailBound coefficients start count radius selected)
          (finiteShellSliceBound coefficients
            (MultiIndex.degreeShell dimension (start + count))
            radius selected))
          (abs (sub second first)))
      rw [add_mul]
      exact combined

public theorem has_derivative_degreePolynomial {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (count : Nat) (point : FiniteVector.carrier dimension)
    (selected : Fin dimension) :
    HasDerivative
      (fun argument => degreePolynomial coefficients count
        (replaceCoordinate point selected argument))
      (point selected)
      (degreePolynomialDerivative coefficients count point selected) := by
  induction count with
  | zero =>
      change HasDerivative (fun _ => zero) (point selected) zero
      exact hasDerivative_const zero (point selected)
  | succ count induction =>
      have combined := hasDerivative_add induction
        (has_derivative_shell_coordinate coefficients count point selected)
      have functionEqual :
          (fun argument => degreePolynomial coefficients (count + 1)
            (replaceCoordinate point selected argument)) =
          (fun argument => add
            (degreePolynomial coefficients count
              (replaceCoordinate point selected argument))
            (shellTerm coefficients
              (replaceCoordinate point selected argument) count)) := by
        funext argument
        unfold degreePolynomial
        rw [partial_sum_succ]
      have derivativeEqual :
          degreePolynomialDerivative coefficients (count + 1)
            point selected =
          add (degreePolynomialDerivative coefficients count point selected)
            (finiteShellSliceDerivative coefficients
              (MultiIndex.degreeShell dimension count) point selected) := by
        unfold degreePolynomialDerivative
        rw [partial_sum_succ]
      rw [functionEqual, derivativeEqual]
      exact combined

end

end Problib.Analysis.Real.PowerSeries
