module

public import Problib.Analysis.Real.Limit

/-! The derivative on the sealed real carrier.

`Problib.Analysis.Rational.HasDerivative` states the same two-sided
epsilon-delta condition over rational displacements and tolerances. This module
states it over the real carrier clause for clause: a tolerance, a radius, a
nonzero displacement inside the radius, and a difference quotient inside the
tolerance of the claimed derivative. The absolute values are the real-carrier
ones from `Problib.Analysis.Real.Absolute`, and the limit is the punctured
limit of `Problib.Analysis.Real.Limit`, so uniqueness, local transport, and
the secant-bound entailment are all read off that layer.
-/

set_option autoImplicit false

namespace Problib.Analysis.Real

open Problib.Real.Construction.Dedekind

noncomputable section

/-- The difference quotient of `function` at `point` over a displacement. -/
@[expose] public def secant
    (function : selection.Carrier → selection.Carrier)
    (point displacement : selection.Carrier) : selection.Carrier :=
  div (sub (function (add point displacement)) (function point)) displacement

/-- A two-sided epsilon-delta derivative on the real scalar carrier. -/
@[expose] public def HasDerivative
    (function : selection.Carrier → selection.Carrier)
    (point derivative : selection.Carrier) : Prop :=
  ∀ epsilon : selection.Carrier, lt zero epsilon →
    ∃ radius : selection.Carrier, lt zero radius ∧
      ∀ displacement : selection.Carrier, displacement ≠ zero →
        lt (abs displacement) radius →
          lt (abs (sub (secant function point displacement) derivative)) epsilon

/-- The derivative is the punctured limit of the difference quotient. -/
public theorem hasDerivative_iff_approaches
    {function : selection.Carrier → selection.Carrier}
    {point derivative : selection.Carrier} :
    HasDerivative function point derivative ↔
      Approaches (secant function point) derivative :=
  Iff.rfl

/-- A point has at most one derivative. -/
public theorem HasDerivative.unique
    {function : selection.Carrier → selection.Carrier}
    {point first second : selection.Carrier}
    (firstDerivative : HasDerivative function point first)
    (secondDerivative : HasDerivative function point second) : first = second :=
  approaches_unique firstDerivative secondDerivative

/-! ### Neighborhoods

A derivative reads the function on a whole punctured ball, so the domain it is
taken over has to contain one. A property holds near zero when it holds at
every displacement inside some ball around zero, the form the limit and the
derivative read. A neighborhood of a point is that statement about the
displacements from the point. -/

/-- A property of the steps near zero. -/
@[expose] public def NearZero (property : selection.Carrier → Prop) : Prop :=
  ∃ radius : selection.Carrier, lt zero radius ∧
    ∀ step : selection.Carrier, lt (abs step) radius → property step

/-- A property that holds at every step holds near zero. -/
public theorem NearZero.of_forall {property : selection.Carrier → Prop}
    (holds : ∀ step, property step) : NearZero property :=
  ⟨one, one_positive, fun step _ => holds step⟩

/-- A property near zero holds at zero. -/
public theorem NearZero.at_zero {property : selection.Carrier → Prop} (near : NearZero property) :
    property zero :=
  let ⟨_, positive, holds⟩ := near
  holds zero (by rw [abs_zero]; exact positive)

/-- Two properties near zero hold together near zero. -/
public theorem NearZero.and {first second : selection.Carrier → Prop} (left : NearZero first)
    (right : NearZero second) : NearZero fun step => first step ∧ second step := by
  obtain ⟨leftRadius, leftPositive, leftHolds⟩ := left
  obtain ⟨rightRadius, rightPositive, rightHolds⟩ := right
  rcases le_total leftRadius rightRadius with smaller | larger
  · exact ⟨leftRadius, leftPositive, fun step small =>
      ⟨leftHolds step small, rightHolds step (lt_of_lt_of_le small smaller)⟩⟩
  · exact ⟨rightRadius, rightPositive, fun step small =>
      ⟨leftHolds step (lt_of_lt_of_le small larger), rightHolds step small⟩⟩

/-- What a property near zero entails at each step holds near zero. -/
public theorem NearZero.mono {first second : selection.Carrier → Prop} (near : NearZero first)
    (entails : ∀ step, first step → second step) : NearZero second :=
  let ⟨radius, positive, holds⟩ := near
  ⟨radius, positive, fun step small => entails step (holds step small)⟩

/-- A domain includes a full ball around the point. -/
@[expose] public def IsNeighborhood
    (domain : selection.Carrier → Prop) (point : selection.Carrier) : Prop :=
  NearZero fun displacement => domain (add point displacement)

/-- A single point is not a neighborhood of itself. -/
public theorem isolated_not_neighborhood (point : selection.Carrier) :
    ¬IsNeighborhood (fun value => value = point) point := by
  rintro ⟨radius, radiusPositive, included⟩
  rcases exists_nonzero_within radiusPositive with ⟨witness, nonzero, small⟩
  have member : add point witness = point := included witness small
  apply nonzero
  have shifted : sub (add point witness) point = sub point point :=
    congrArg (fun value => sub value point) member
  rwa [add_sub_self, sub_self] at shifted

/-- Local equality transports derivatives; one equal value is insufficient. -/
public theorem HasDerivative.congr_near
    {function other : selection.Carrier → selection.Carrier}
    {point derivative : selection.Carrier}
    (agree : IsNeighborhood (fun value => function value = other value) point)
    (differentiable : HasDerivative function point derivative) :
    HasDerivative other point derivative := by
  obtain ⟨radius, radiusPositive, equal⟩ := agree
  refine approaches_congr_near radiusPositive ?_ differentiable
  intro displacement _ small
  have atPoint : function point = other point := by
    have atZero : function (add point zero) = other (add point zero) :=
      equal zero (by rw [abs_zero]; exact radiusPositive)
    rwa [add_zero] at atZero
  have atShift : function (add point displacement) = other (add point displacement) :=
    equal displacement small
  simp only [secant, atPoint, atShift]

/-- Equality near zero transports a derivative at zero. -/
public theorem HasDerivative.congr_near_zero
    {function other : selection.Carrier → selection.Carrier} {derivative : selection.Carrier}
    (agree : NearZero fun step => function step = other step)
    (differentiable : HasDerivative function zero derivative) :
    HasDerivative other zero derivative :=
  differentiable.congr_near (agree.mono fun step equal => by
    show function (add zero step) = other (add zero step)
    rw [zero_add]
    exact equal)

/-- A linear error bound on difference quotients entails the derivative.
The bound is local and applies to every nonzero sufficiently small
displacement. -/
public theorem derivative_of_secant_bound
    (function : selection.Carrier → selection.Carrier)
    (point derivative radius constant : selection.Carrier)
    (radiusPositive : lt zero radius) (constantNonnegative : le zero constant)
    (bound : ∀ displacement : selection.Carrier, displacement ≠ zero →
      lt (abs displacement) radius →
        le (abs (sub (secant function point displacement) derivative))
          (mul constant (abs displacement))) :
    HasDerivative function point derivative := by
  intro epsilon positive
  have divisorPositive : lt zero (add constant one) :=
    lt_of_le_of_lt constantNonnegative
      (by
        have shifted := add_lt_add_left constant one_positive
        rwa [add_zero] at shifted)
  have divisorNonzero : add constant one ≠ zero := by
    intro vanished
    have copy := divisorPositive
    rw [vanished] at copy
    exact lt_irrefl zero copy
  have tolerancePositive : lt zero (div epsilon (add constant one)) :=
    div_positive positive divisorPositive
  rcases small_positive radiusPositive tolerancePositive with
    ⟨chosen, chosenPositive, belowRadius, belowTolerance⟩
  refine ⟨chosen, chosenPositive, ?_⟩
  intro displacement nonzero small
  have inside := lt_of_lt_of_le small belowRadius
  have scaled : lt (mul (add constant one) (abs displacement)) epsilon := by
    have step := mul_lt_mul_positive_left (lt_of_lt_of_le small belowTolerance)
      divisorPositive
    rwa [mul_div_cancel epsilon divisorNonzero] at step
  have widened : le (mul constant (abs displacement))
      (mul (add constant one) (abs displacement)) := by
    refine mul_le_mul_nonnegative_right ?_ (abs_nonnegative displacement)
    have shifted := add_le_add_left_iff (left := zero) (right := one)
      (shift := constant)
    rw [add_zero] at shifted
    exact shifted.mpr one_nonnegative
  exact lt_of_le_of_lt (le_trans (bound displacement nonzero inside) widened) scaled

/-- Differentiability at a point implies continuity there, as the punctured
limit of the shifted function. -/
public theorem hasDerivative_continuous
    {function : selection.Carrier → selection.Carrier}
    {point derivative : selection.Carrier}
    (differentiable : HasDerivative function point derivative) :
    Approaches (fun displacement => function (add point displacement))
      (function point) := by
  have product := approaches_mul approaches_displacement
    (hasDerivative_iff_approaches.mp differentiable)
  have shifted := approaches_add product (approaches_const (function point))
  rw [zero_mul, add_comm zero (function point), add_zero] at shifted
  refine approaches_congr_near one_positive ?_ shifted
  intro displacement nonzero _
  rw [secant, mul_div_cancel _ nonzero, sub_add_cancel]

end

end Problib.Analysis.Real
