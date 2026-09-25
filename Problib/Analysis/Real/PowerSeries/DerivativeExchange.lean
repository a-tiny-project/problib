module

public import Problib.Analysis.Real.PowerSeries.DerivativeMajorant

/-! Passing finite shell difference estimates to an infinite series value. -/

set_option autoImplicit false

namespace Problib.Analysis.Real.PowerSeries

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real.SignedSeries

noncomputable section

private instance : Std.Associative (α := selection.Carrier) add :=
  ⟨fun left middle right => add_assoc left middle right⟩

private instance : Std.Commutative (α := selection.Carrier) add :=
  ⟨add_comm⟩

public theorem abs_le_of_approaches_bound
    {function : selection.Carrier → selection.Carrier}
    {limit upper radius : selection.Carrier}
    (approaches : Problib.Analysis.Real.Approaches function limit)
    (radiusPositive : lt zero radius)
    (bounded : ∀ step : selection.Carrier, step ≠ zero →
      lt (abs step) radius → le (abs (function step)) upper) :
    le (abs limit) upper := by
  apply Problib.Analysis.Real.le_of_forall_lt_add
  intro tolerance positive
  rcases approaches tolerance positive with
    ⟨closeRadius, closePositive, close⟩
  rcases small_positive radiusPositive closePositive with
    ⟨chosen, chosenPositive, belowBound, belowClose⟩
  rcases exists_nonzero_within chosenPositive with
    ⟨step, nonzero, small⟩
  have near := close step nonzero (lt_of_lt_of_le small belowClose)
  have bound := bounded step nonzero (lt_of_lt_of_le small belowBound)
  have triangle := abs_add_le (function step)
    (sub limit (function step))
  rw [add_sub_cancel] at triangle
  rw [abs_sub_comm] at near
  have closeUpper := add_lt_add_left upper near
  exact lt_of_le_of_lt
    (le_trans triangle (add_le_add bound (le_refl _))) closeUpper

public theorem finite_shell_derivative_le_bound {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (indices : List (MultiIndex.carrier dimension))
    (point : FiniteVector.carrier dimension)
    {radius : selection.Carrier} (radiusPositive : lt zero radius)
    (coordinates : ∀ coordinate, lt (abs (point coordinate)) radius)
    (selected : Fin dimension) :
    le (abs (finiteShellSliceDerivative coefficients indices point selected))
      (finiteShellSliceBound coefficients indices radius selected) := by
  let gap := sub radius (abs (point selected))
  have gapPositive : lt zero gap :=
    sub_positive_iff.mpr (coordinates selected)
  have differentiable := has_derivative_finiteShellSlice coefficients
    indices point selected
  apply abs_le_of_approaches_bound differentiable gapPositive
  intro step nonzero small
  have firstBound : le (abs (point selected)) radius :=
    le_of_lt (coordinates selected)
  have secondBound : le (abs (add (point selected) step)) radius := by
    have triangle := abs_add_le (point selected) step
    have raised := add_lt_add_left (abs (point selected)) small
    rw [add_sub_cancel] at raised
    exact le_of_lt (lt_of_le_of_lt triangle raised)
  have differenceBound := finiteShellSlice_difference_bound
    coefficients indices point radiusPositive.left
    (fun coordinate => le_of_lt (coordinates coordinate))
    selected firstBound secondBound
  have absPositive := abs_positive_of_nonzero nonzero
  have reciprocalNonnegative := le_of_lt
    (inverse_of_positive_positive absPositive)
  have scaled := mul_le_mul_nonnegative_right differenceBound
    reciprocalNonnegative
  have cancel :
      mul (mul (finiteShellSliceBound coefficients indices radius selected)
        (abs step)) (inverse (abs step)) =
      finiteShellSliceBound coefficients indices radius selected := by
    rw [mul_assoc, mul_inverse_cancel
      (nonzero_of_positive absPositive), mul_one]
  rw [add_sub_self] at scaled
  rw [cancel] at scaled
  change le
    (abs (Problib.Analysis.Real.secant
      (finiteShellSlice coefficients indices point selected)
      (point selected) step))
    (finiteShellSliceBound coefficients indices radius selected)
  unfold Problib.Analysis.Real.secant
  rw [abs_div, div_eq_mul_inverse]
  exact scaled

@[expose] public def derivativeShellValues {dimension : Nat}
    (series : Convergent dimension)
    (point : FiniteVector.carrier dimension)
    (selected : Fin dimension) : Nat → selection.Carrier :=
  fun degreeValue => finiteShellSliceDerivative series.coefficients
    (MultiIndex.degreeShell dimension degreeValue) point selected

public theorem derivativeShellValues_absolute {dimension : Nat}
    (series : Convergent dimension)
    {ratio radius : selection.Carrier}
    (ratioPositive : lt zero ratio) (ratioBelowOne : lt ratio one)
    (radiusPositive : lt zero radius)
    (insideRadius : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius (fun _ => radius))
    (point : FiniteVector.carrier dimension)
    (coordinates : ∀ coordinate,
      lt (abs (point coordinate)) (mul ratio radius))
    (selected : Fin dimension) :
    AbsolutelySummable (derivativeShellValues series point selected) := by
  let shrunk := mul ratio radius
  let majorant := fun degreeValue => finiteShellSliceBound
    series.coefficients (MultiIndex.degreeShell dimension degreeValue)
    shrunk selected
  let certificate := derivative_shell_bounds_summable series
    ratioPositive.left ratioBelowOne radiusPositive insideRadius selected
  have nonnegativeMajorant : ∀ degreeValue,
      le zero (majorant degreeValue) :=
    fun degreeValue => finiteShellSliceBound_nonnegative
      series.coefficients (MultiIndex.degreeShell dimension degreeValue)
      (mul_nonnegative ratioPositive.left radiusPositive.left) selected
  have pointwise : ∀ degreeValue,
      le (abs (derivativeShellValues series point selected degreeValue))
        (majorant degreeValue) :=
    fun degreeValue => finite_shell_derivative_le_bound
      series.coefficients (MultiIndex.degreeShell dimension degreeValue)
      point (mul_positive ratioPositive radiusPositive)
      coordinates selected
  refine ⟨sum majorant certificate, fun count => ?_⟩
  exact le_trans (partial_sum_le pointwise count)
    (partial_sum_le_sum_nonnegative nonnegativeMajorant certificate count)

/-- Finite differentiable approximants certify a derivative when their
remainders have arbitrarily small local Lipschitz constants. -/
public theorem has_derivative_of_small_lipschitz_remainders
    (function : selection.Carrier → selection.Carrier)
    (derivative : selection.Carrier)
    (approximants : ∀ tolerance : selection.Carrier,
      lt zero tolerance →
      ∃ polynomial : selection.Carrier → selection.Carrier,
        Problib.Analysis.Real.HasDerivative polynomial zero derivative ∧
        ∃ radius : selection.Carrier, lt zero radius ∧
          ∀ step : selection.Carrier, step ≠ zero →
            lt (abs step) radius →
            le (abs (sub
              (sub (function step) (polynomial step))
              (sub (function zero) (polynomial zero))))
              (mul tolerance (abs step))) :
    Problib.Analysis.Real.HasDerivative function zero derivative := by
  intro epsilon positive
  have halfPositive := Problib.Analysis.Real.half_positive positive
  rcases approximants _ halfPositive with
    ⟨polynomial, polynomialDerivative, remainderRadius,
      remainderPositive, remainderBound⟩
  rcases polynomialDerivative _ halfPositive with
    ⟨polynomialRadius, polynomialPositive, polynomialClose⟩
  rcases small_positive remainderPositive polynomialPositive with
    ⟨radius, radiusPositive, belowRemainder, belowPolynomial⟩
  refine ⟨radius, radiusPositive, fun step nonzero small => ?_⟩
  let remainder := fun argument => sub (function argument)
    (polynomial argument)
  have functionForm (argument : selection.Carrier) :
      function argument = add (polynomial argument)
        (remainder argument) := by
    exact (add_sub_cancel (function argument) (polynomial argument)).symm
  have secantSplit :
      Problib.Analysis.Real.secant function zero step =
      add (Problib.Analysis.Real.secant polynomial zero step)
        (div (sub (remainder step) (remainder zero)) step) := by
    unfold Problib.Analysis.Real.secant
    rw [zero_add, functionForm step, functionForm zero,
      add_sub_add_comm, add_div]
  have quotientBound :
      le (abs (div (sub (remainder step) (remainder zero)) step))
        (Problib.Analysis.Real.half epsilon) := by
    have difference := remainderBound step nonzero
      (lt_of_lt_of_le small belowRemainder)
    have absPositive := abs_positive_of_nonzero nonzero
    have reciprocalNonnegative := le_of_lt
      (inverse_of_positive_positive absPositive)
    have scaled := mul_le_mul_nonnegative_right difference
      reciprocalNonnegative
    rw [abs_div, div_eq_mul_inverse]
    change le
      (mul (abs (sub (remainder step) (remainder zero)))
        (inverse (abs step)))
      (Problib.Analysis.Real.half epsilon)
    have cancel :
        mul (mul (Problib.Analysis.Real.half epsilon) (abs step))
          (inverse (abs step)) =
        Problib.Analysis.Real.half epsilon := by
      rw [mul_assoc, mul_inverse_cancel
        (nonzero_of_positive absPositive), mul_one]
    rw [cancel] at scaled
    exact scaled
  have polynomialNear := polynomialClose step nonzero
    (lt_of_lt_of_le small belowPolynomial)
  have split :
      sub (Problib.Analysis.Real.secant function zero step)
        derivative =
      add
        (sub (Problib.Analysis.Real.secant polynomial zero step)
          derivative)
        (div (sub (remainder step) (remainder zero)) step) := by
    rw [secantSplit]
    simp only [sub_eq_add_neg]
    ac_rfl
  rw [split]
  have triangle := abs_add_le
    (sub (Problib.Analysis.Real.secant polynomial zero step)
      derivative)
    (div (sub (remainder step) (remainder zero)) step)
  have strict := add_lt_add_right
    (Problib.Analysis.Real.half epsilon) polynomialNear
  rw [Problib.Analysis.Real.add_half] at strict
  exact lt_of_le_of_lt triangle
    (lt_of_le_of_lt (add_le_add (le_refl _) quotientBound) strict)

public theorem has_derivative_of_approximate_lipschitz_remainders
    (function : selection.Carrier → selection.Carrier)
    (derivative : selection.Carrier)
    (approximants : ∀ tolerance : selection.Carrier,
      lt zero tolerance →
      ∃ polynomial : selection.Carrier → selection.Carrier,
      ∃ polynomialDerivative : selection.Carrier,
        Problib.Analysis.Real.HasDerivative polynomial zero
          polynomialDerivative ∧
        le (abs (sub polynomialDerivative derivative)) tolerance ∧
        ∃ radius : selection.Carrier, lt zero radius ∧
          ∀ step : selection.Carrier, step ≠ zero →
            lt (abs step) radius →
            le (abs (sub
              (sub (function step) (polynomial step))
              (sub (function zero) (polynomial zero))))
              (mul tolerance (abs step))) :
    Problib.Analysis.Real.HasDerivative function zero derivative := by
  intro epsilon positive
  let quarter := Problib.Analysis.Real.half
    (Problib.Analysis.Real.half epsilon)
  have quarterPositive := Problib.Analysis.Real.half_positive
    (Problib.Analysis.Real.half_positive positive)
  rcases approximants quarter quarterPositive with
    ⟨polynomial, polynomialDerivative, polynomialProof,
      derivativeNear, remainderRadius, remainderPositive, remainderBound⟩
  rcases polynomialProof quarter quarterPositive with
    ⟨polynomialRadius, polynomialPositive, polynomialClose⟩
  rcases small_positive remainderPositive polynomialPositive with
    ⟨radius, radiusPositive, belowRemainder, belowPolynomial⟩
  refine ⟨radius, radiusPositive, fun step nonzero small => ?_⟩
  let remainder := fun argument => sub (function argument)
    (polynomial argument)
  have functionForm (argument : selection.Carrier) :
      function argument = add (polynomial argument)
        (remainder argument) :=
    (add_sub_cancel (function argument) (polynomial argument)).symm
  have secantSplit :
      Problib.Analysis.Real.secant function zero step =
      add (Problib.Analysis.Real.secant polynomial zero step)
        (div (sub (remainder step) (remainder zero)) step) := by
    unfold Problib.Analysis.Real.secant
    rw [zero_add, functionForm step, functionForm zero,
      add_sub_add_comm, add_div]
  have quotientBound :
      le (abs (div (sub (remainder step) (remainder zero)) step))
        quarter := by
    have difference := remainderBound step nonzero
      (lt_of_lt_of_le small belowRemainder)
    have absPositive := abs_positive_of_nonzero nonzero
    have scaled := mul_le_mul_nonnegative_right difference
      (le_of_lt (inverse_of_positive_positive absPositive))
    rw [abs_div, div_eq_mul_inverse]
    change le
      (mul (abs (sub (remainder step) (remainder zero)))
        (inverse (abs step))) quarter
    have cancel :
        mul (mul quarter (abs step)) (inverse (abs step)) =
          quarter := by
      rw [mul_assoc, mul_inverse_cancel
        (nonzero_of_positive absPositive), mul_one]
    rwa [cancel] at scaled
  have polynomialNear := polynomialClose step nonzero
    (lt_of_lt_of_le small belowPolynomial)
  let polynomialError := sub
    (Problib.Analysis.Real.secant polynomial zero step)
    polynomialDerivative
  let derivativeError := sub polynomialDerivative derivative
  let quotient := div (sub (remainder step) (remainder zero)) step
  have split :
      sub (Problib.Analysis.Real.secant function zero step)
        derivative =
      add (add polynomialError derivativeError) quotient := by
    rw [secantSplit]
    change sub (add
        (Problib.Analysis.Real.secant polynomial zero step)
        quotient) derivative =
      add (add (sub
        (Problib.Analysis.Real.secant polynomial zero step)
        polynomialDerivative)
        (sub polynomialDerivative derivative)) quotient
    have first : sub (add
        (Problib.Analysis.Real.secant polynomial zero step)
        quotient) derivative =
      add (sub (Problib.Analysis.Real.secant polynomial zero step)
        derivative) quotient := by
      simp only [sub_eq_add_neg]
      ac_rfl
    rw [first, ← sub_add_sub]
  rw [split]
  have triangle := le_trans
    (abs_add_le (add polynomialError derivativeError) quotient)
    (add_le_add (abs_add_le polynomialError derivativeError)
      (le_refl _))
  have bounds := add_le_add
    (add_le_add (le_refl (abs polynomialError)) derivativeNear)
    quotientBound
  have raised := add_lt_add_left (add quarter quarter) polynomialNear
  have reordered :
      add (add (abs polynomialError) quarter) quarter =
      add (add quarter quarter) (abs polynomialError) := by ac_rfl
  rw [reordered] at bounds
  have halfEqual : add quarter quarter =
      Problib.Analysis.Real.half epsilon :=
    Problib.Analysis.Real.add_half _
  have threeBelow : lt (add (add quarter quarter) quarter) epsilon := by
    rw [halfEqual]
    have quarterBelowHalf : lt quarter
        (Problib.Analysis.Real.half epsilon) := by
      have shifted := add_lt_add_left quarter quarterPositive
      rwa [add_zero, Problib.Analysis.Real.add_half] at shifted
    have upper := add_lt_add_left
      (Problib.Analysis.Real.half epsilon) quarterBelowHalf
    rwa [Problib.Analysis.Real.add_half] at upper
  exact lt_of_le_of_lt (le_trans triangle bounds)
    (lt_trans raised threeBelow)

@[expose] public noncomputable def fullTailValue {dimension : Nat}
    (series : Convergent dimension)
    (displacement : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball (FiniteVector.zeroVector dimension)
      series.radius displacement)
    (start : Nat) : selection.Carrier :=
  sub
    (sum (fullShellTerms series displacement)
      (summable_of_absolute_bound
        (fullShellTerms_absolute series displacement inside)))
    (partialSum (fullShellTerms series displacement) start)

public theorem degreeTail_converges_full_tail {dimension : Nat}
    (series : Convergent dimension)
    (displacement : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball (FiniteVector.zeroVector dimension)
      series.radius displacement) (start : Nat) :
    Problib.Analysis.Real.ConvergesTo
      (fun count => degreeTail series.coefficients start count displacement)
      (fullTailValue series displacement inside start) := by
  exact partial_sum_tail_converges
    (fullShellTerms series displacement)
    (summable_of_absolute_bound
      (fullShellTerms_absolute series displacement inside)) start

/-- The infinite series tail inherits the finite tail's small Lipschitz
constant inside a smaller coordinate box. -/
public theorem full_tail_difference_small {dimension : Nat}
    (series : Convergent dimension)
    {ratio radius : selection.Carrier}
    (ratioNonnegative : le zero ratio) (ratioBelowOne : lt ratio one)
    (radiusPositive : lt zero radius)
    (insideRadius : FiniteVector.ball (FiniteVector.zeroVector dimension)
      series.radius (fun _ => radius))
    (selected : Fin dimension)
    {tolerance : selection.Carrier} (tolerancePositive : lt zero tolerance) :
    ∃ stage : Nat, ∀ start, stage ≤ start →
      ∀ point : FiniteVector.carrier dimension,
      (∀ coordinate, le (abs (point coordinate)) (mul ratio radius)) →
      ∀ first second : selection.Carrier,
      le (abs first) (mul ratio radius) →
      le (abs second) (mul ratio radius) →
      ∀ firstInside : FiniteVector.ball
        (FiniteVector.zeroVector dimension) series.radius
        (replaceCoordinate point selected first),
      ∀ secondInside : FiniteVector.ball
        (FiniteVector.zeroVector dimension) series.radius
        (replaceCoordinate point selected second),
      le (abs (sub
        (fullTailValue series
          (replaceCoordinate point selected second) secondInside start)
        (fullTailValue series
          (replaceCoordinate point selected first) firstInside start)))
        (mul tolerance (abs (sub second first))) := by
  rcases degreeTail_difference_small series ratioNonnegative
    ratioBelowOne radiusPositive insideRadius selected tolerancePositive with
    ⟨stage, finiteSmall⟩
  refine ⟨stage, fun start later point coordinates first second
    firstBound secondBound firstInside secondInside => ?_⟩
  have firstConverges := degreeTail_converges_full_tail series
    (replaceCoordinate point selected first) firstInside start
  have secondConverges := degreeTail_converges_full_tail series
    (replaceCoordinate point selected second) secondInside start
  have differenceConverges := converges_to_sub secondConverges firstConverges
  have finiteBound : ∀ count,
      le (abs (sub
        (degreeTail series.coefficients start count
          (replaceCoordinate point selected second))
        (degreeTail series.coefficients start count
          (replaceCoordinate point selected first))))
        (mul tolerance (abs (sub second first))) :=
    fun count => finiteSmall start later count point coordinates
      first second firstBound secondBound
  exact abs_le_of_convergesTo differenceConverges finiteBound

@[expose] public noncomputable def coordinateValue {dimension : Nat}
    (series : Convergent dimension) (selected : Fin dimension)
    (argument : selection.Carrier) : selection.Carrier := by
  classical
  let displacement := replaceCoordinate
    (FiniteVector.zeroVector dimension) selected argument
  exact if inside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius displacement then
    value series displacement inside
  else zero

public theorem coordinateValue_of_inside {dimension : Nat}
    (series : Convergent dimension) (selected : Fin dimension)
    (argument : selection.Carrier)
    (inside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius
      (replaceCoordinate (FiniteVector.zeroVector dimension)
        selected argument)) :
    coordinateValue series selected argument =
      value series
        (replaceCoordinate (FiniteVector.zeroVector dimension)
          selected argument) inside := by
  classical
  unfold coordinateValue
  rw [dif_pos inside]

public theorem coordinate_displacement_inside {dimension : Nat}
    (series : Convergent dimension) (selected : Fin dimension)
    {ratio radius : selection.Carrier}
    (ratioBelowOne : lt ratio one)
    (radiusPositive : lt zero radius)
    (insideRadius : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius (fun _ => radius))
    (argument : selection.Carrier)
    (bounded : le (abs argument) (mul ratio radius)) :
    FiniteVector.ball (FiniteVector.zeroVector dimension) series.radius
      (replaceCoordinate (FiniteVector.zeroVector dimension)
        selected argument) := by
  have radiusBelow : lt radius series.radius := by
    have selectedInside := insideRadius selected
    change lt (abs (sub radius zero)) series.radius at selectedInside
    rw [sub_zero, abs_of_nonnegative radiusPositive.left] at selectedInside
    exact selectedInside
  have shrunkBelow : lt (mul ratio radius) series.radius := by
    have included := mul_le_mul_nonnegative_right
      (le_of_lt ratioBelowOne) radiusPositive.left
    rw [one_mul] at included
    exact lt_of_le_of_lt included radiusBelow
  intro coordinate
  by_cases equal : coordinate = selected
  · subst coordinate
    change lt
      (abs (sub (replaceCoordinate
        (FiniteVector.zeroVector dimension) selected argument selected)
          zero)) series.radius
    simp only [replaceCoordinate, sub_zero]
    exact lt_of_le_of_lt bounded shrunkBelow
  · change lt
      (abs (sub (replaceCoordinate
        (FiniteVector.zeroVector dimension) selected argument coordinate)
          zero)) series.radius
    simp only [replaceCoordinate, if_neg equal, FiniteVector.zeroVector,
      sub_self, abs_zero]
    exact series.radiusPositive

public theorem closed_box_inside {dimension : Nat}
    (series : Convergent dimension) (selected : Fin dimension)
    {ratio radius : selection.Carrier}
    (ratioBelowOne : lt ratio one)
    (radiusPositive : lt zero radius)
    (insideRadius : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius (fun _ => radius))
    (point : FiniteVector.carrier dimension)
    (coordinates : ∀ coordinate,
      le (abs (point coordinate)) (mul ratio radius)) :
    FiniteVector.ball (FiniteVector.zeroVector dimension)
      series.radius point := by
  have radiusBelow : lt radius series.radius := by
    have selectedInside := insideRadius selected
    change lt (abs (sub radius zero)) series.radius at selectedInside
    rw [sub_zero, abs_of_nonnegative radiusPositive.left] at selectedInside
    exact selectedInside
  have shrunkBelow : lt (mul ratio radius) series.radius := by
    have included := mul_le_mul_nonnegative_right
      (le_of_lt ratioBelowOne) radiusPositive.left
    rw [one_mul] at included
    exact lt_of_le_of_lt included radiusBelow
  intro coordinate
  change lt (abs (sub (point coordinate) zero)) series.radius
  rw [sub_zero]
  exact lt_of_le_of_lt (coordinates coordinate) shrunkBelow

public theorem positive_midpoint {lower upper : selection.Carrier}
    (lowerNonnegative : le zero lower) (included : lt lower upper) :
    ∃ middle : selection.Carrier,
      lt zero middle ∧ lt lower middle ∧ lt middle upper := by
  let gap := sub upper lower
  have gapPositive : lt zero gap := sub_positive_iff.mpr included
  let increment := Problib.Analysis.Real.half gap
  have incrementPositive := Problib.Analysis.Real.half_positive
    gapPositive
  let middle := add lower increment
  have lowerBelow : lt lower middle := by
    have raised := add_lt_add_left lower incrementPositive
    rwa [add_zero] at raised
  have incrementBelow : lt increment gap := by
    have raised := add_lt_add_left increment incrementPositive
    rwa [add_zero, Problib.Analysis.Real.add_half] at raised
  have middleBelow : lt middle upper := by
    have raised := add_lt_add_left lower incrementBelow
    rw [add_sub_cancel] at raised
    exact raised
  exact ⟨middle, lt_of_le_of_lt lowerNonnegative lowerBelow,
    lowerBelow, middleBelow⟩

@[expose] public noncomputable def coordinateValueAround {dimension : Nat}
    (series : Convergent dimension)
    (point : FiniteVector.carrier dimension)
    (selected : Fin dimension)
    (step : selection.Carrier) : selection.Carrier := by
  classical
  let displacement := replaceCoordinate point selected
    (add (point selected) step)
  exact if inside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius displacement then
    value series displacement inside
  else zero

public theorem coordinateValueAround_of_inside {dimension : Nat}
    (series : Convergent dimension)
    (point : FiniteVector.carrier dimension)
    (selected : Fin dimension) (step : selection.Carrier)
    (inside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius
      (replaceCoordinate point selected (add (point selected) step))) :
    coordinateValueAround series point selected step =
      value series
        (replaceCoordinate point selected (add (point selected) step))
        inside := by
  classical
  unfold coordinateValueAround
  rw [dif_pos inside]

public theorem has_derivative_translate_to_zero
    (function : selection.Carrier → selection.Carrier)
    (point derivative : selection.Carrier)
    (differentiable : Problib.Analysis.Real.HasDerivative
      function point derivative) :
    Problib.Analysis.Real.HasDerivative
      (fun step => function (add point step)) zero derivative := by
  intro tolerance positive
  rcases differentiable tolerance positive with
    ⟨radius, radiusPositive, close⟩
  refine ⟨radius, radiusPositive, fun step nonzero small => ?_⟩
  simpa only [Problib.Analysis.Real.secant, zero_add, add_zero]
    using close step nonzero small

public theorem value_eq_polynomial_add_tail {dimension : Nat}
    (series : Convergent dimension)
    (displacement : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball (FiniteVector.zeroVector dimension)
      series.radius displacement) (start : Nat) :
    value series displacement inside =
      add (degreePolynomial series.coefficients start displacement)
        (fullTailValue series displacement inside start) := by
  rw [← full_shell_sum_eq_value series displacement inside]
  unfold degreePolynomial fullTailValue
  change sum (fullShellTerms series displacement)
      (summable_of_absolute_bound
        (fullShellTerms_absolute series displacement inside)) =
    add (partialSum (fullShellTerms series displacement) start)
      (sub (sum (fullShellTerms series displacement)
        (summable_of_absolute_bound
          (fullShellTerms_absolute series displacement inside)))
        (partialSum (fullShellTerms series displacement) start))
  exact (add_sub_cancel _ _).symm

/-- Differentiating the local series along one coordinate at its center is
justified by the summable finite-difference majorant. -/
public theorem coordinateValue_has_derivative_zero {dimension : Nat}
    (series : Convergent dimension) (selected : Fin dimension)
    {ratio radius : selection.Carrier}
    (ratioPositive : lt zero ratio) (ratioBelowOne : lt ratio one)
    (radiusPositive : lt zero radius)
    (insideRadius : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius (fun _ => radius)) :
    Problib.Analysis.Real.HasDerivative
      (coordinateValue series selected) zero
      (degreePolynomialDerivative series.coefficients 2
        (FiniteVector.zeroVector dimension) selected) := by
  apply has_derivative_of_small_lipschitz_remainders
  intro tolerance tolerancePositive
  rcases full_tail_difference_small series ratioPositive.left ratioBelowOne
    radiusPositive insideRadius selected tolerancePositive with
    ⟨stage, tailSmall⟩
  let count := stage + 2
  let polynomial := fun argument => degreePolynomial series.coefficients
    count (replaceCoordinate (FiniteVector.zeroVector dimension)
      selected argument)
  refine ⟨polynomial, ?_, mul ratio radius,
    mul_positive ratioPositive radiusPositive, ?_⟩
  · have finiteDerivative := has_derivative_degreePolynomial
      series.coefficients count (FiniteVector.zeroVector dimension) selected
    have stable := degreePolynomialDerivative_stable_zero
      series.coefficients selected stage
    change degreePolynomialDerivative series.coefficients count
      (FiniteVector.zeroVector dimension) selected = _ at stable
    rw [stable] at finiteDerivative
    exact finiteDerivative
  · intro step nonzero small
    have zeroBound : le (abs zero) (mul ratio radius) := by
      rw [abs_zero]
      exact mul_nonnegative ratioPositive.left radiusPositive.left
    have stepBound : le (abs step) (mul ratio radius) := le_of_lt small
    have zeroInside := coordinate_displacement_inside series selected
      ratioBelowOne radiusPositive insideRadius zero zeroBound
    have stepInside := coordinate_displacement_inside series selected
      ratioBelowOne radiusPositive insideRadius step stepBound
    have coordinates : ∀ coordinate,
        le (abs ((FiniteVector.zeroVector dimension) coordinate))
          (mul ratio radius) := fun _ => zeroBound
    have tailBound := tailSmall count (by dsimp [count]; omega)
      (FiniteVector.zeroVector dimension) coordinates
      zero step zeroBound stepBound zeroInside stepInside
    have stepRemainder :
        sub (coordinateValue series selected step) (polynomial step) =
        fullTailValue series
          (replaceCoordinate (FiniteVector.zeroVector dimension)
            selected step) stepInside count := by
      rw [coordinateValue_of_inside series selected step stepInside,
        value_eq_polynomial_add_tail series _ stepInside count]
      exact add_sub_self _ _
    have zeroRemainder :
        sub (coordinateValue series selected zero) (polynomial zero) =
        fullTailValue series
          (replaceCoordinate (FiniteVector.zeroVector dimension)
            selected zero) zeroInside count := by
      rw [coordinateValue_of_inside series selected zero zeroInside,
        value_eq_polynomial_add_tail series _ zeroInside count]
      exact add_sub_self _ _
    rw [stepRemainder, zeroRemainder]
    simpa only [sub_zero] using tailBound

public theorem coordinateValue_has_derivative_coefficient {dimension : Nat}
    (series : Convergent dimension) (selected : Fin dimension)
    {ratio radius : selection.Carrier}
    (ratioPositive : lt zero ratio) (ratioBelowOne : lt ratio one)
    (radiusPositive : lt zero radius)
    (insideRadius : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius (fun _ => radius)) :
    Problib.Analysis.Real.HasDerivative
      (coordinateValue series selected) zero
      (series.coefficients (MultiIndex.unitIndex selected)) := by
  have derivative := coordinateValue_has_derivative_zero series selected
    ratioPositive ratioBelowOne radiusPositive insideRadius
  rw [degreePolynomialDerivative_two] at derivative
  exact derivative

public theorem coordinateValue_has_derivative {dimension : Nat}
    (series : Convergent dimension) (selected : Fin dimension) :
    Problib.Analysis.Real.HasDerivative
      (coordinateValue series selected) zero
      (series.coefficients (MultiIndex.unitIndex selected)) := by
  let ratio := Problib.Analysis.Real.half one
  let radius := Problib.Analysis.Real.half series.radius
  have ratioPositive := Problib.Analysis.Real.half_positive one_positive
  have radiusPositive := Problib.Analysis.Real.half_positive
    series.radiusPositive
  have ratioBelowOne : lt ratio one := by
    have raised := add_lt_add_left ratio ratioPositive
    rwa [add_zero, Problib.Analysis.Real.add_half] at raised
  have radiusBelow : lt radius series.radius := by
    have raised := add_lt_add_left radius radiusPositive
    rwa [add_zero, Problib.Analysis.Real.add_half] at raised
  have insideRadius : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius
      (fun _ => radius) := by
    intro coordinate
    change lt (abs (sub radius zero)) series.radius
    rw [sub_zero, abs_of_nonnegative radiusPositive.left]
    exact radiusBelow
  exact coordinateValue_has_derivative_coefficient series selected
    ratioPositive ratioBelowOne radiusPositive insideRadius

/-- The coordinate derivative at every point of a smaller box is the sum
of the derivatives of its finite homogeneous shells. -/
public theorem coordinateValueAround_termwise_derivative {dimension : Nat}
    (series : Convergent dimension)
    {ratio radius : selection.Carrier}
    (ratioPositive : lt zero ratio) (ratioBelowOne : lt ratio one)
    (radiusPositive : lt zero radius)
    (insideRadius : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius (fun _ => radius))
    (point : FiniteVector.carrier dimension)
    (coordinates : ∀ coordinate,
      lt (abs (point coordinate)) (mul ratio radius))
    (selected : Fin dimension) :
    Problib.Analysis.Real.HasDerivative
      (coordinateValueAround series point selected) zero
      (sum (derivativeShellValues series point selected)
        (summable_of_absolute_bound
          (derivativeShellValues_absolute series ratioPositive
            ratioBelowOne radiusPositive insideRadius point
            coordinates selected))) := by
  let absoluteCertificate := derivativeShellValues_absolute series
    ratioPositive ratioBelowOne radiusPositive insideRadius point
    coordinates selected
  let certificate := summable_of_absolute_bound absoluteCertificate
  let derivative := sum (derivativeShellValues series point selected)
    certificate
  apply has_derivative_of_approximate_lipschitz_remainders
  intro tolerance tolerancePositive
  rcases (partial_sum_converges
    (derivativeShellValues series point selected) certificate)
      tolerance tolerancePositive with ⟨derivativeStage, derivativeClose⟩
  rcases full_tail_difference_small series ratioPositive.left ratioBelowOne
    radiusPositive insideRadius selected tolerancePositive with
    ⟨tailStage, tailSmall⟩
  let count := max derivativeStage tailStage
  let polynomial := fun step => degreePolynomial series.coefficients count
    (replaceCoordinate point selected (add (point selected) step))
  let polynomialDerivative := degreePolynomialDerivative series.coefficients
    count point selected
  let gap := sub (mul ratio radius) (abs (point selected))
  have gapPositive : lt zero gap :=
    sub_positive_iff.mpr (coordinates selected)
  refine ⟨polynomial, polynomialDerivative, ?_, ?_, gap,
    gapPositive, ?_⟩
  · exact has_derivative_translate_to_zero _ (point selected)
      polynomialDerivative
      (has_derivative_degreePolynomial series.coefficients count point
        selected)
  · exact le_of_lt (derivativeClose count
      (Nat.le_max_left derivativeStage tailStage))
  · intro step nonzero small
    let first := point selected
    let second := add first step
    have firstBound : le (abs first) (mul ratio radius) :=
      le_of_lt (coordinates selected)
    have secondBound : le (abs second) (mul ratio radius) := by
      have triangle := abs_add_le first step
      have raised := add_lt_add_left (abs first) small
      rw [add_sub_cancel] at raised
      exact le_of_lt (lt_of_le_of_lt triangle raised)
    have pointBounds : ∀ coordinate,
        le (abs (point coordinate)) (mul ratio radius) :=
      fun coordinate => le_of_lt (coordinates coordinate)
    have firstInside : FiniteVector.ball
        (FiniteVector.zeroVector dimension) series.radius
        (replaceCoordinate point selected first) := by
      simpa only [first, replaceCoordinate_at_point] using
        (closed_box_inside series selected ratioBelowOne
          radiusPositive insideRadius point pointBounds)
    have secondCoordinates : ∀ coordinate,
        le (abs ((replaceCoordinate point selected second) coordinate))
          (mul ratio radius) := by
      intro coordinate
      by_cases equal : coordinate = selected
      · subst coordinate
        simpa [replaceCoordinate] using secondBound
      · simpa only [replaceCoordinate, if_neg equal] using
          pointBounds coordinate
    have secondInside := closed_box_inside series selected
      ratioBelowOne radiusPositive insideRadius
      (replaceCoordinate point selected second) secondCoordinates
    have tailBound := tailSmall count
      (Nat.le_max_right derivativeStage tailStage)
      point pointBounds first second firstBound secondBound
      firstInside secondInside
    have zeroInside : FiniteVector.ball
        (FiniteVector.zeroVector dimension) series.radius
        (replaceCoordinate point selected
          (add (point selected) zero)) := by
      simpa only [first, add_zero] using firstInside
    have stepRemainder :
        sub (coordinateValueAround series point selected step)
          (polynomial step) =
        fullTailValue series (replaceCoordinate point selected second)
          secondInside count := by
      rw [coordinateValueAround_of_inside series point selected step
        secondInside,
        value_eq_polynomial_add_tail series _ secondInside count]
      exact add_sub_self _ _
    have zeroRemainder :
        sub (coordinateValueAround series point selected zero)
          (polynomial zero) =
        fullTailValue series (replaceCoordinate point selected first)
          firstInside count := by
      rw [coordinateValueAround_of_inside series point selected zero
        zeroInside,
        value_eq_polynomial_add_tail series _ zeroInside count]
      dsimp [polynomial, first]
      simp only [add_zero]
      rw [add_sub_self]
    rw [stepRemainder, zeroRemainder]
    simpa only [second, first, add_sub_self] using tailBound

/-- Every interior point has a smaller box on which the termwise coordinate
derivative theorem applies. -/
public theorem coordinateValueAround_termwise_interior {dimension : Nat}
    (series : Convergent dimension)
    (point : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball (FiniteVector.zeroVector dimension)
      series.radius point)
    (selected : Fin dimension) :
    ∃ certificate : AbsolutelySummable
        (derivativeShellValues series point selected),
      Problib.Analysis.Real.HasDerivative
        (coordinateValueAround series point selected) zero
        (sum (derivativeShellValues series point selected)
          (summable_of_absolute_bound certificate)) := by
  let size := FiniteVector.supNorm point
  have sizeNonnegative := FiniteVector.sup_norm_nonnegative point
  have sizeBelow : lt size series.radius :=
    FiniteVector.sup_norm_lt series.radiusPositive
      (fun coordinate => by
        have bounded := inside coordinate
        change lt (abs (sub (point coordinate) zero))
          series.radius at bounded
        rwa [sub_zero] at bounded)
  rcases positive_midpoint sizeNonnegative sizeBelow with
    ⟨smallRadius, smallPositive, sizeBelowSmall, smallBelowSeries⟩
  rcases positive_midpoint smallPositive.left smallBelowSeries with
    ⟨largeRadius, largePositive, smallBelowLarge, largeBelowSeries⟩
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
  have ratioProduct : mul ratio largeRadius = smallRadius := by
    change mul (div smallRadius largeRadius) largeRadius = smallRadius
    exact div_mul_cancel smallRadius largeNonzero
  have insideRadius : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius
      (fun _ => largeRadius) := by
    intro coordinate
    change lt (abs (sub largeRadius zero)) series.radius
    rw [sub_zero, abs_of_nonnegative largePositive.left]
    exact largeBelowSeries
  have coordinates : ∀ coordinate,
      lt (abs (point coordinate)) (mul ratio largeRadius) := by
    intro coordinate
    rw [ratioProduct]
    exact lt_of_le_of_lt
      (FiniteVector.coordinate_le_sup_norm point coordinate)
      sizeBelowSmall
  let certificate := derivativeShellValues_absolute series
    ratioPositive ratioBelowOne largePositive insideRadius point
    coordinates selected
  refine ⟨certificate, ?_⟩
  exact coordinateValueAround_termwise_derivative series
    ratioPositive ratioBelowOne largePositive insideRadius point
    coordinates selected

/-- At each center, an analytic representation supplies the true coordinate
derivative with its unit-multiindex coefficient. -/
public theorem analytic_on_coordinate_derivative_at_center {dimension : Nat}
    {region : FiniteVector.carrier dimension → Prop}
    {function : FiniteVector.carrier dimension → selection.Carrier}
    (analytic : AnalyticOn region function)
    (center : FiniteVector.carrier dimension) (member : region center)
    (selected : Fin dimension) :
    ∃ series : Convergent dimension,
      Problib.Analysis.Real.HasDerivative
        (fun step => function (FiniteVector.addVector center
          (replaceCoordinate (FiniteVector.zeroVector dimension)
            selected step))) zero
        (series.coefficients (MultiIndex.unitIndex selected)) := by
  rcases analytic.right center member with ⟨series, _, agree⟩
  refine ⟨series, ?_⟩
  apply Problib.Analysis.Real.HasDerivative.congr_near_zero
    (function := coordinateValue series selected)
  · refine ⟨series.radius, series.radiusPositive, fun step small => ?_⟩
    let displacement := replaceCoordinate
      (FiniteVector.zeroVector dimension) selected step
    have displacedInside : FiniteVector.ball
        (FiniteVector.zeroVector dimension) series.radius
        displacement := by
      intro coordinate
      by_cases equal : coordinate = selected
      · subst coordinate
        change lt (abs (sub (displacement selected) zero)) series.radius
        simp only [displacement, replaceCoordinate, sub_zero]
        exact small
      · change lt (abs (sub (displacement coordinate) zero))
          series.radius
        simp only [displacement, replaceCoordinate, if_neg equal,
          FiniteVector.zeroVector, sub_self, abs_zero]
        exact series.radiusPositive
    let point := FiniteVector.addVector center displacement
    have pointInside : FiniteVector.ball center series.radius point := by
      intro coordinate
      change lt (abs (sub (add (center coordinate)
        (displacement coordinate)) (center coordinate))) series.radius
      rw [add_sub_self]
      simpa only [FiniteVector.zeroVector, sub_zero] using
        displacedInside coordinate
    have difference : FiniteVector.subVector point center =
        displacement := by
      funext coordinate
      change sub (add (center coordinate) (displacement coordinate))
        (center coordinate) = displacement coordinate
      exact add_sub_self (center coordinate) (displacement coordinate)
    have functionEqual : function point =
        value series displacement displacedInside := by
      simpa only [difference] using agree point pointInside
    have coordinateEqual := coordinateValue_of_inside series selected
      step displacedInside
    exact coordinateEqual.trans functionEqual.symm
  · exact coordinateValue_has_derivative series selected

end

end Problib.Analysis.Real.PowerSeries
