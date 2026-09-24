module

public import Problib.Analysis.Real.Calculus

/-! Composition and inversion on the real carrier.

The chain rule cannot divide by the inner increment, because it may vanish at
nonzero displacements. It reads the outer function through a slope that is the
outer secant at a nonzero step and the outer derivative at zero, which makes the
outer increment a product at every step. The inverse-function rule needs no
such device. A right inverse that is continuous at the point has a nonzero
increment at every nonzero displacement, so its secant is the reciprocal of the
forward secant at that increment. Two limit lemmas serve both rules and the
logarithm's derivative: a punctured limit composes with an inner function that
stays off the puncture, and a function closer to a limit than a convergent one
converges to it.
-/

set_option autoImplicit false

namespace Problib.Analysis.Real

open Problib.Real.Construction.Dedekind

noncomputable section

/-! ### Limits -/

/-- A punctured limit composes with an inner function that approaches zero and
stays nonzero near the puncture. -/
public theorem approaches_comp
    {outer inner : selection.Carrier → selection.Carrier}
    {limit radius : selection.Carrier}
    (outerApproaches : Approaches outer limit)
    (innerApproaches : Approaches inner zero)
    (radiusPositive : lt zero radius)
    (innerNonzero : ∀ displacement : selection.Carrier, displacement ≠ zero →
      lt (abs displacement) radius → inner displacement ≠ zero) :
    Approaches (fun displacement => outer (inner displacement)) limit := by
  intro epsilon positive
  rcases outerApproaches epsilon positive with ⟨outerRadius, outerPositive, outerBound⟩
  rcases innerApproaches outerRadius outerPositive with
    ⟨innerRadius, innerPositive, innerBound⟩
  rcases small_positive radiusPositive innerPositive with
    ⟨chosen, chosenPositive, belowRadius, belowInner⟩
  refine ⟨chosen, chosenPositive, fun displacement nonzero small => ?_⟩
  have close := innerBound displacement nonzero (lt_of_lt_of_le small belowInner)
  rw [sub_zero] at close
  exact outerBound (inner displacement)
    (innerNonzero displacement nonzero (lt_of_lt_of_le small belowRadius)) close

/-- A function no farther from `limit` than a convergent one, near the
puncture, converges to `limit`. -/
public theorem approaches_of_closer
    {function other : selection.Carrier → selection.Carrier}
    {limit radius : selection.Carrier} (radiusPositive : lt zero radius)
    (closer : ∀ displacement : selection.Carrier, displacement ≠ zero →
      lt (abs displacement) radius →
        le (abs (sub (function displacement) limit))
          (abs (sub (other displacement) limit)))
    (approaches : Approaches other limit) : Approaches function limit := by
  intro epsilon positive
  rcases approaches epsilon positive with ⟨inner, innerPositive, close⟩
  rcases small_positive radiusPositive innerPositive with
    ⟨chosen, chosenPositive, belowRadius, belowInner⟩
  exact ⟨chosen, chosenPositive, fun displacement nonzero small =>
    lt_of_le_of_lt (closer displacement nonzero (lt_of_lt_of_le small belowRadius))
      (close displacement nonzero (lt_of_lt_of_le small belowInner))⟩

/-- Subtraction on the right preserves order. -/
private theorem sub_le_sub_right {left right : selection.Carrier} (shift : selection.Carrier)
    (included : le left right) : le (sub left shift) (sub right shift) := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact add_le_add_right_iff.mpr included

/-- A value between two others is no farther from the first than the second
is. -/
public theorem abs_sub_le_of_between {value lower upper : selection.Carrier}
    (between : (le lower value ∧ le value upper) ∨ (le upper value ∧ le value lower)) :
    le (abs (sub value lower)) (abs (sub upper lower)) := by
  rcases between with ⟨above, below⟩ | ⟨above, below⟩
  · have valueGap : le zero (sub value lower) := by
      have shifted := sub_le_sub_right lower above
      rwa [sub_self] at shifted
    rw [abs_of_nonnegative valueGap, abs_of_nonnegative (le_trans valueGap
      (sub_le_sub_right lower below))]
    exact sub_le_sub_right lower below
  · have valueGap : le (sub value lower) zero := by
      have shifted := sub_le_sub_right lower below
      rwa [sub_self] at shifted
    rw [abs_of_nonpositive valueGap, abs_of_nonpositive (le_trans
      (sub_le_sub_right lower above) valueGap)]
    exact neg_le_neg_iff.mpr (sub_le_sub_right lower above)

/-! ### The chain rule -/

/-- The chain rule on the real carrier. -/
public theorem hasDerivative_comp {outer inner : selection.Carrier → selection.Carrier}
    {point outerDerivative innerDerivative : selection.Carrier}
    (outerDifferentiable : HasDerivative outer (inner point) outerDerivative)
    (innerDifferentiable : HasDerivative inner point innerDerivative) :
    HasDerivative (fun value => outer (inner value)) point
      (mul outerDerivative innerDerivative) := by
  classical
  let slope : selection.Carrier → selection.Carrier := fun step =>
    if step = zero then outerDerivative else secant outer (inner point) step
  have slopeScales : ∀ step : selection.Carrier,
      sub (outer (add (inner point) step)) (outer (inner point)) =
        mul (slope step) step := by
    intro step
    by_cases vanished : step = zero
    · rw [vanished, add_zero, sub_self, mul_zero]
    · show _ = mul (if step = zero then outerDerivative
          else secant outer (inner point) step) step
      rw [if_neg vanished, secant, div_mul_cancel _ vanished]
  let increment : selection.Carrier → selection.Carrier := fun displacement =>
    sub (inner (add point displacement)) (inner point)
  have incrementApproaches : Approaches increment zero := by
    have shifted := approaches_sub (hasDerivative_continuous innerDifferentiable)
      (approaches_const (inner point))
    rwa [sub_self] at shifted
  have slopeApproaches :
      Approaches (fun displacement => slope (increment displacement)) outerDerivative := by
    intro epsilon positive
    rcases outerDifferentiable epsilon positive with
      ⟨outerRadius, outerPositive, outerBound⟩
    rcases incrementApproaches outerRadius outerPositive with
      ⟨radius, radiusPositive, small⟩
    refine ⟨radius, radiusPositive, fun displacement nonzero inside => ?_⟩
    show lt (abs (sub (if increment displacement = zero then outerDerivative
      else secant outer (inner point) (increment displacement)) outerDerivative)) epsilon
    by_cases vanished : increment displacement = zero
    · rw [if_pos vanished, sub_self, abs_zero]
      exact positive
    · rw [if_neg vanished]
      have close := small displacement nonzero inside
      rw [sub_zero] at close
      exact outerBound (increment displacement) vanished close
  have product := approaches_mul slopeApproaches innerDifferentiable
  refine approaches_congr_near one_positive (fun displacement _ _ => ?_) product
  have landed : inner (add point displacement) =
      add (inner point) (increment displacement) :=
    (add_sub_cancel (inner (add point displacement)) (inner point)).symm
  have numerator : sub (outer (inner (add point displacement))) (outer (inner point)) =
      mul (slope (increment displacement)) (increment displacement) := by
    rw [landed]
    exact slopeScales (increment displacement)
  show mul (slope (increment displacement)) (div (increment displacement) displacement) =
    div (sub (outer (inner (add point displacement))) (outer (inner point))) displacement
  rw [numerator, mul_div_assoc]

/-! ### The inverse-function rule -/

/-- The inverse-function rule on the real carrier. A function that is a right
inverse of `forward` near `point`, and continuous there, has as derivative the
reciprocal of `forward`'s nonzero derivative at its value. -/
public theorem hasDerivative_of_right_inverse
    {forward backward : selection.Carrier → selection.Carrier}
    {point derivative radius : selection.Carrier} (radiusPositive : lt zero radius)
    (rightInverse : ∀ displacement : selection.Carrier, lt (abs displacement) radius →
      forward (backward (add point displacement)) = add point displacement)
    (continuous : Approaches (fun displacement => backward (add point displacement))
      (backward point))
    (differentiable : HasDerivative forward (backward point) derivative)
    (derivativeNonzero : derivative ≠ zero) :
    HasDerivative backward point (inverse derivative) := by
  let increment : selection.Carrier → selection.Carrier := fun displacement =>
    sub (backward (add point displacement)) (backward point)
  have atPoint : forward (backward point) = point := by
    have atZero := rightInverse zero (by rw [abs_zero]; exact radiusPositive)
    rwa [add_zero] at atZero
  have landed : ∀ displacement : selection.Carrier,
      backward (add point displacement) = add (backward point) (increment displacement) :=
    fun displacement => (add_sub_cancel (backward (add point displacement)) (backward point)).symm
  have incrementNonzero : ∀ displacement : selection.Carrier, displacement ≠ zero →
      lt (abs displacement) radius → increment displacement ≠ zero := by
    intro displacement nonzero inside vanished
    have same := landed displacement
    rw [vanished, add_zero] at same
    have returned := rightInverse displacement inside
    rw [same, atPoint] at returned
    apply nonzero
    have shifted := congrArg (fun value => sub value point) returned
    simp only [sub_self, add_sub_self] at shifted
    exact shifted.symm
  have incrementApproaches : Approaches increment zero := by
    have shifted := approaches_sub continuous (approaches_const (backward point))
    rwa [sub_self] at shifted
  have forwardSecant := approaches_comp differentiable incrementApproaches
    radiusPositive incrementNonzero
  have inverted := approaches_inverse forwardSecant derivativeNonzero
  refine approaches_congr_near radiusPositive (fun displacement nonzero inside => ?_) inverted
  have forwardValue : sub (forward (add (backward point) (increment displacement)))
      (forward (backward point)) = displacement := by
    rw [← landed, rightInverse displacement inside, atPoint, add_sub_self]
  show inverse (div (sub (forward (add (backward point) (increment displacement)))
      (forward (backward point))) (increment displacement)) =
    div (increment displacement) displacement
  rw [forwardValue, div_eq_mul_inverse,
    inverse_mul nonzero (inverse_nonzero (incrementNonzero displacement nonzero inside)),
    inverse_inverse, div_eq_mul_inverse, mul_comm]

end

end Problib.Analysis.Real
