module

public import Problib.Analysis.Real.Composition
import Problib.Real.Grind

/-! Limits and derivatives at one side of a point.

A derivative estimator can read each sample only to the right of zero: a
kink, as in `max(x, 0)` at a tie, has a right derivative and no two-sided
one. A `Side` names where the step may go, both ways or to the right only.
`Side.along` reparametrizes a punctured neighborhood of zero onto the side's
steps. It is the identity for `two` and the absolute value for `right`, so a
limit at a side is an ordinary punctured limit of the reparametrized function.
Every limit rule of `Problib.Analysis.Real.Limit` then holds at a side
unchanged, and the calculus below repeats `Calculus` and `Composition` with
the step read through `along`.

At `two` every definition unfolds to the two-sided one: `NearZeroOn .two` is
`NearZero`, and `HasDerivativeOn .two` is `HasDerivative`. The chain rule
takes a two-sided outer function and an inner function at a side, which is
the shape a smooth operation applied to a one-sided curve has. -/

set_option autoImplicit false

open scoped Problib.Real.AC

namespace Problib.Analysis.Real

open Problib.Real.Construction.Dedekind

noncomputable section

/-- Where a step may go: both ways, or to the right only. -/
public inductive Side where
  | two
  | right
  deriving DecidableEq

namespace Side

/-- The step a punctured displacement reaches at a side. -/
@[expose] public def along : Side → selection.Carrier → selection.Carrier
  | two, displacement => displacement
  | right, displacement => abs displacement

public theorem along_zero : (side : Side) → side.along zero = zero
  | two => rfl
  | right => abs_zero

public theorem abs_along : (side : Side) → (displacement : selection.Carrier) →
    abs (side.along displacement) = abs displacement
  | two, _ => rfl
  | right, displacement => abs_of_nonnegative (abs_nonnegative displacement)

public theorem along_nonzero (side : Side) {displacement : selection.Carrier}
    (nonzero : displacement ≠ zero) : side.along displacement ≠ zero := fun vanished =>
  nonzero (abs_eq_zero_iff.mp (by rw [← side.abs_along, vanished, abs_zero]))

/-- The reached step falls to zero with the displacement. -/
public theorem approaches_along (side : Side) :
    Approaches (fun displacement => side.along displacement) zero := by
  intro epsilon positive
  refine ⟨epsilon, positive, fun displacement _ small => ?_⟩
  rw [sub_zero, side.abs_along]
  exact small

/-- A reached step is at the side: nonnegative at `right`. -/
public theorem along_nonnegative (displacement : selection.Carrier) :
    le zero (right.along displacement) :=
  abs_nonnegative displacement

end Side

/-- A property of the steps near zero at a side. -/
@[expose] public def NearZeroOn (side : Side) (property : selection.Carrier → Prop) : Prop :=
  NearZero fun displacement => property (side.along displacement)

/-- The function's limit at `limit` as the step falls to zero at a side. -/
@[expose] public def ApproachesOn (side : Side) (function : selection.Carrier → selection.Carrier)
    (limit : selection.Carrier) : Prop :=
  Approaches (fun displacement => function (side.along displacement)) limit

/-- A derivative at a side: the limit of the difference quotient over steps at
that side. -/
@[expose] public def HasDerivativeOn (side : Side)
    (function : selection.Carrier → selection.Carrier)
    (point derivative : selection.Carrier) : Prop :=
  ApproachesOn side (secant function point) derivative

namespace NearZeroOn

variable {side : Side} {first second : selection.Carrier → Prop}

public theorem of_forall (holds : ∀ step, first step) : NearZeroOn side first :=
  NearZero.of_forall fun _ => holds _

public theorem of_nearZero (near : NearZero first) : NearZeroOn side first :=
  let ⟨radius, positive, holds⟩ := near
  ⟨radius, positive, fun displacement small =>
    holds _ (by rw [side.abs_along]; exact small)⟩

public theorem at_zero (near : NearZeroOn side first) : first zero := by
  have atZero := NearZero.at_zero near
  rwa [side.along_zero] at atZero

public theorem mono (near : NearZeroOn side first)
    (implies : ∀ step, first step → second step) :
    NearZeroOn side second :=
  NearZero.mono near fun _ holds => implies _ holds

public theorem and (left : NearZeroOn side first) (right : NearZeroOn side second) :
    NearZeroOn side fun step => first step ∧ second step :=
  NearZero.and left right

end NearZeroOn

/-- At `two`, a derivative at the side is the two-sided derivative. -/
public theorem hasDerivativeOn_two_iff {function : selection.Carrier → selection.Carrier}
    {point derivative : selection.Carrier} :
    HasDerivativeOn .two function point derivative ↔ HasDerivative function point derivative :=
  Iff.rfl

/-- A two-sided derivative is a derivative at every side. -/
public theorem HasDerivative.atSide {function : selection.Carrier → selection.Carrier}
    {point derivative : selection.Carrier} (side : Side)
    (differentiable : HasDerivative function point derivative) :
    HasDerivativeOn side function point derivative :=
  approaches_comp differentiable side.approaches_along one_positive
    fun _ nonzero _ => side.along_nonzero nonzero

/-- Reflecting the step negates the reflected secant. -/
public theorem secant_reflect_zero (function : selection.Carrier → selection.Carrier)
    (step : selection.Carrier) :
    secant (fun displacement => function (neg displacement)) zero step =
      neg (secant function zero (neg step)) := by
  simp only [secant, zero_add, neg_zero, div_eq_mul_inverse, inverse_neg, mul_neg,
    neg_neg]

/-- Opposite right slopes join into a two-sided derivative exactly when their
signs agree after reflection. This is a line statement, without any additivity
assumption across directions. -/
public theorem hasDerivative_of_opposite_right
    {function : selection.Carrier → selection.Carrier} {slope : selection.Carrier}
    (right : HasDerivativeOn .right function zero slope)
    (opposite : HasDerivativeOn .right (fun step => function (neg step)) zero (neg slope)) :
    HasDerivative function zero slope := by
  classical
  intro epsilon positive
  obtain ⟨rightRadius, rightPositive, rightClose⟩ := right epsilon positive
  obtain ⟨leftRadius, leftPositive, leftClose⟩ := opposite epsilon positive
  obtain ⟨radius, radiusPositive, belowRight, belowLeft⟩ :=
    small_positive rightPositive leftPositive
  refine ⟨radius, radiusPositive, fun displacement nonzero small => ?_⟩
  by_cases nonnegative : le zero displacement
  · have close := rightClose displacement nonzero (lt_of_lt_of_le small belowRight)
    simpa only [Side.along, abs_of_nonnegative nonnegative] using close
  · have nonpositive : le displacement zero := le_of_lt (lt_of_not_le nonnegative)
    have close := leftClose displacement nonzero (lt_of_lt_of_le small belowLeft)
    have reflected : neg (abs displacement) = displacement := by
      rw [abs_of_nonpositive nonpositive, neg_neg]
    change lt (abs (sub (secant (fun step => function (neg step)) zero
      (abs displacement)) (neg slope))) epsilon at close
    rw [secant_reflect_zero, reflected, ← neg_sub_distrib, abs_neg] at close
    exact close

namespace HasDerivativeOn

variable {side : Side}

/-- Differentiability at a side is continuity at that side. -/
public theorem continuous {function : selection.Carrier → selection.Carrier}
    {point derivative : selection.Carrier}
    (differentiable : HasDerivativeOn side function point derivative) :
    Approaches (fun displacement => function (add point (side.along displacement)))
      (function point) := by
  have product := approaches_mul side.approaches_along differentiable
  have shifted := approaches_add product (approaches_const (function point))
  rw [zero_mul, add_comm zero (function point), add_zero] at shifted
  refine approaches_congr_near one_positive ?_ shifted
  intro displacement nonzero _
  show add (mul (side.along displacement) (secant function point (side.along displacement)))
    (function point) = _
  rw [secant, mul_div_cancel _ (side.along_nonzero nonzero), sub_add_cancel]

/-- Equality at the steps near zero at a side transports a derivative at
zero. -/
public theorem congr_near_zero {function other : selection.Carrier → selection.Carrier}
    {derivative : selection.Carrier}
    (agree : NearZeroOn side fun step => function step = other step)
    (differentiable : HasDerivativeOn side function zero derivative) :
    HasDerivativeOn side other zero derivative := by
  obtain ⟨radius, radiusPositive, equal⟩ := agree
  have atZero : function zero = other zero :=
    NearZeroOn.at_zero (side := side) (first := fun step => function step = other step)
      ⟨radius, radiusPositive, equal⟩
  refine approaches_congr_near radiusPositive ?_ differentiable
  intro displacement _ small
  have atStep := equal displacement small
  show secant function zero (side.along displacement) = secant other zero (side.along displacement)
  simp only [secant, zero_add, atZero, atStep]

end HasDerivativeOn

variable {side : Side}

/-- A derivative is at most any bound on the increments per unit step near
zero. -/
public theorem derivative_le_of_increment {curve : selection.Carrier → selection.Carrier}
    {derivative bound : selection.Carrier} (differentiable : HasDerivativeOn side curve zero derivative)
    (increments : NearZeroOn side fun step =>
      le (abs (sub (curve step) (curve zero))) (mul (abs step) bound)) :
    le (abs derivative) bound := by
  classical
  by_cases below : le (abs derivative) bound
  · exact below
  have gap : lt zero (sub (abs derivative) bound) := by
    rcases le_total (abs derivative) bound with smaller | larger
    · exact absurd smaller below
    · have strict : lt bound (abs derivative) := ⟨larger, below⟩
      real_grind
  obtain ⟨radius, radiusPositive, close⟩ := differentiable _ gap
  have closeNear : NearZero fun displacement : selection.Carrier => displacement ≠ zero →
      lt (abs (sub (secant curve zero (side.along displacement)) derivative))
        (sub (abs derivative) bound) :=
    ⟨radius, radiusPositive, fun displacement small nonzero => close displacement nonzero small⟩
  obtain ⟨common, commonPositive, both⟩ := closeNear.and increments
  have halfPositive : lt zero (div common (selection.ofRat 2)) :=
    div_positive commonPositive ofRat_two_positive
  have halfSmall : lt (abs (div common (selection.ofRat 2))) common := by
    rw [abs_of_nonnegative (le_of_lt halfPositive)]
    real_grind
  have halfNonzero : div common (selection.ofRat 2) ≠ zero := fun vanished =>
    halfPositive.right (by rw [vanished]; exact le_refl zero)
  obtain ⟨secantClose, increment⟩ := both _ halfSmall
  have secantBound := secant_le_of_increment (side.along_nonzero halfNonzero) increment
  have triangle := abs_add_le
    (sub derivative (secant curve zero (side.along (div common (selection.ofRat 2)))))
    (secant curve zero (side.along (div common (selection.ofRat 2))))
  rw [show add (sub derivative (secant curve zero (side.along (div common (selection.ofRat 2)))))
      (secant curve zero (side.along (div common (selection.ofRat 2)))) = derivative by
    real_grind, abs_sub_comm] at triangle
  have strict := secantClose halfNonzero
  exact absurd (by real_grind : le (abs derivative) bound) below

public theorem hasDerivativeOn_const (value point : selection.Carrier) :
    HasDerivativeOn side (fun _ => value) point zero :=
  (hasDerivative_const value point).atSide side

public theorem hasDerivativeOn_identity (point : selection.Carrier) :
    HasDerivativeOn side (fun value => value) point one :=
  (hasDerivative_identity point).atSide side

public theorem hasDerivativeOn_add {first second : selection.Carrier → selection.Carrier}
    {point firstDerivative secondDerivative : selection.Carrier}
    (firstDifferentiable : HasDerivativeOn side first point firstDerivative)
    (secondDifferentiable : HasDerivativeOn side second point secondDerivative) :
    HasDerivativeOn side (fun value => add (first value) (second value)) point
      (add firstDerivative secondDerivative) := by
  refine approaches_congr_near one_positive ?_
    (approaches_add firstDifferentiable secondDifferentiable)
  intro displacement _ _
  simp only [secant]
  rw [← add_div]
  congr 1
  simp only [sub_eq_add_neg, neg_add]
  ac_rfl

public theorem hasDerivativeOn_neg {function : selection.Carrier → selection.Carrier}
    {point derivative : selection.Carrier}
    (differentiable : HasDerivativeOn side function point derivative) :
    HasDerivativeOn side (fun value => neg (function value)) point (neg derivative) := by
  refine approaches_congr_near one_positive ?_ (approaches_neg differentiable)
  intro displacement _ _
  simp only [secant]
  rw [← neg_div]
  congr 1
  exact neg_sub_distrib _ _

public theorem hasDerivativeOn_sub {first second : selection.Carrier → selection.Carrier}
    {point firstDerivative secondDerivative : selection.Carrier}
    (firstDifferentiable : HasDerivativeOn side first point firstDerivative)
    (secondDifferentiable : HasDerivativeOn side second point secondDerivative) :
    HasDerivativeOn side (fun value => sub (first value) (second value)) point
      (sub firstDerivative secondDerivative) := by
  have combined :=
    hasDerivativeOn_add firstDifferentiable (hasDerivativeOn_neg secondDifferentiable)
  simpa only [sub_eq_add_neg] using combined

public theorem hasDerivativeOn_smul {function : selection.Carrier → selection.Carrier}
    {point derivative : selection.Carrier} (scalar : selection.Carrier)
    (differentiable : HasDerivativeOn side function point derivative) :
    HasDerivativeOn side (fun value => mul scalar (function value)) point
      (mul scalar derivative) := by
  refine approaches_congr_near one_positive ?_
    (approaches_mul (approaches_const scalar) differentiable)
  intro displacement _ _
  simp only [secant]
  rw [← mul_div_assoc]
  congr 1
  exact mul_sub scalar _ _

/-- The product rule at a side. -/
public theorem hasDerivativeOn_mul {first second : selection.Carrier → selection.Carrier}
    {point firstDerivative secondDerivative : selection.Carrier}
    (firstDifferentiable : HasDerivativeOn side first point firstDerivative)
    (secondDifferentiable : HasDerivativeOn side second point secondDerivative) :
    HasDerivativeOn side (fun value => mul (first value) (second value)) point
      (add (mul firstDerivative (second point))
        (mul (first point) secondDerivative)) := by
  have continuity := firstDifferentiable.continuous
  have shiftedPart := approaches_mul continuity secondDifferentiable
  have basePart := approaches_mul firstDifferentiable
    (approaches_const (second point))
  refine approaches_congr_near one_positive ?_ (approaches_add basePart shiftedPart)
  intro displacement _ _
  simp only [secant]
  rw [← div_mul_right, ← mul_div_assoc, ← add_div]
  congr 1
  rw [sub_mul, mul_sub, add_comm]
  exact sub_add_sub _ _ _

/-- The reciprocal rule at a side, where the function does not vanish. -/
public theorem hasDerivativeOn_inverse {function : selection.Carrier → selection.Carrier}
    {point derivative : selection.Carrier}
    (differentiable : HasDerivativeOn side function point derivative)
    (nonzero : function point ≠ zero) :
    HasDerivativeOn side (fun value => inverse (function value)) point
      (neg (div derivative (mul (function point) (function point)))) := by
  have continuity := differentiable.continuous
  rcases approaches_nonzero_near continuity nonzero with
    ⟨radius, radiusPositive, awayFromZero⟩
  have reciprocal := approaches_inverse continuity nonzero
  have product := approaches_mul differentiable
    (approaches_mul reciprocal (approaches_const (inverse (function point))))
  have negated := approaches_neg product
  have limitForm : neg (mul derivative
      (mul (inverse (function point)) (inverse (function point)))) =
      neg (div derivative (mul (function point) (function point))) := by
    rw [div_eq_mul_inverse, inverse_mul nonzero nonzero]
  rw [limitForm] at negated
  refine approaches_congr_near radiusPositive ?_ negated
  intro displacement displacementNonzero small
  have shiftedNonzero := awayFromZero displacement displacementNonzero small
  simp only [secant]
  rw [← div_mul_right, ← neg_div]
  congr 1
  rw [sub_mul, ← mul_assoc (function (add point (side.along displacement))),
    mul_inverse_cancel shiftedNonzero, one_mul,
    mul_comm (inverse (function (add point (side.along displacement))))
      (inverse (function point)),
    ← mul_assoc (function point), mul_inverse_cancel nonzero, one_mul]
  exact neg_sub _ _

/-- The quotient rule at a side, where the denominator does not vanish. -/
public theorem hasDerivativeOn_div {first second : selection.Carrier → selection.Carrier}
    {point firstDerivative secondDerivative : selection.Carrier}
    (firstDifferentiable : HasDerivativeOn side first point firstDerivative)
    (secondDifferentiable : HasDerivativeOn side second point secondDerivative)
    (nonzero : second point ≠ zero) :
    HasDerivativeOn side (fun value => div (first value) (second value)) point
      (div (sub (mul firstDerivative (second point)) (mul (first point) secondDerivative))
        (mul (second point) (second point))) := by
  have squareNonzero : mul (second point) (second point) ≠ zero := by
    intro vanished
    rcases mul_eq_zero_iff.mp vanished with left | right
    · exact nonzero left
    · exact nonzero right
  have composed := hasDerivativeOn_mul firstDifferentiable
    (hasDerivativeOn_inverse secondDifferentiable nonzero)
  have limitForm :
      add (mul firstDerivative (inverse (second point)))
          (mul (first point) (neg (div secondDerivative (mul (second point) (second point))))) =
        div (sub (mul firstDerivative (second point)) (mul (first point) secondDerivative))
          (mul (second point) (second point)) := by
    apply mul_right_cancel_of_nonzero squareNonzero
    rw [div_mul_cancel _ squareNonzero, add_mul, sub_eq_add_neg]
    congr 1
    · calc mul (mul firstDerivative (inverse (second point))) (mul (second point) (second point))
          = mul firstDerivative
              (mul (mul (inverse (second point)) (second point)) (second point)) := by
            ac_rfl
        _ = mul firstDerivative (second point) := by
            rw [inverse_mul_cancel nonzero, one_mul]
    · calc mul (mul (first point) (neg (div secondDerivative (mul (second point) (second point)))))
            (mul (second point) (second point))
          = neg (mul (first point)
              (mul (div secondDerivative (mul (second point) (second point)))
                (mul (second point) (second point)))) := by
            rw [mul_neg, neg_mul, mul_assoc]
        _ = neg (mul (first point) secondDerivative) := by
            rw [div_mul_cancel _ squareNonzero]
  rw [limitForm] at composed
  exact composed

/-- The chain rule at a side: a two-sided outer function after an inner
function differentiable at the side. -/
public theorem hasDerivativeOn_comp {outer inner : selection.Carrier → selection.Carrier}
    {point outerDerivative innerDerivative : selection.Carrier}
    (outerDifferentiable : HasDerivative outer (inner point) outerDerivative)
    (innerDifferentiable : HasDerivativeOn side inner point innerDerivative) :
    HasDerivativeOn side (fun value => outer (inner value)) point
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
      rw [ite_eq_right vanished, secant, div_mul_cancel _ vanished]
  let increment : selection.Carrier → selection.Carrier := fun displacement =>
    sub (inner (add point (side.along displacement))) (inner point)
  have incrementApproaches : Approaches increment zero := by
    have shifted := approaches_sub innerDifferentiable.continuous
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
    · rw [ite_eq_left vanished, sub_self, abs_zero]
      exact positive
    · rw [ite_eq_right vanished]
      have close := small displacement nonzero inside
      rw [sub_zero] at close
      exact outerBound (increment displacement) vanished close
  have product := approaches_mul slopeApproaches innerDifferentiable
  refine approaches_congr_near one_positive (fun displacement nonzero _ => ?_) product
  have landed : inner (add point (side.along displacement)) =
      add (inner point) (increment displacement) :=
    (add_sub_cancel (inner (add point (side.along displacement))) (inner point)).symm
  have numerator : sub (outer (inner (add point (side.along displacement))))
      (outer (inner point)) =
      mul (slope (increment displacement)) (increment displacement) := by
    rw [landed]
    exact slopeScales (increment displacement)
  show mul (slope (increment displacement))
      (div (increment displacement) (side.along displacement)) =
    div (sub (outer (inner (add point (side.along displacement))))
      (outer (inner point))) (side.along displacement)
  rw [numerator, mul_div_assoc]

end

end Problib.Analysis.Real
