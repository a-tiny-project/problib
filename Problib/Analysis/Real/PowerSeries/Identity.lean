module

public import Problib.Analysis.Real.PowerSeries.Continuity
public import Problib.Analysis.Real.Connected
public import Problib.Analysis.Real.Calculus

/-! The identity theorem for analytic functions of one coordinate.

A function analytic on an open interval whose derivatives of every order vanish
at one point vanishes on the whole interval. The flat points, where every
derivative vanishes, form an open set because their Taylor coefficients are
zero, and a relatively closed one because each derivative is continuous.
Connectedness of the interval finishes the argument. A zero at which some
derivative is nonzero is isolated among the zeros of the last vanishing
derivative, which is how the zero set of a nonzero function is shown small.
-/

set_option autoImplicit false

namespace Problib.Analysis.Real.PowerSeries

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real

noncomputable section

/-- The one-coordinate vector with the given value. -/
@[expose] public def linePoint (value : selection.Carrier) :
    FiniteVector.carrier 1 :=
  fun _ => value

public theorem fin_one_eq_zero (coordinate : Fin 1) : coordinate = 0 :=
  Fin.ext (Nat.lt_one_iff.mp coordinate.isLt)

public theorem line_ball_iff {center radius value : selection.Carrier} :
    FiniteVector.ball (linePoint center) radius (linePoint value) ↔
      lt (abs (sub value center)) radius := by
  constructor
  · intro inside
    exact inside 0
  · intro inside coordinate
    exact inside

/-- A coordinate slice of a one-coordinate function moves along the line. -/
public theorem line_slice (function : FiniteVector.carrier 1 → selection.Carrier)
    (value step : selection.Carrier) :
    coordinateSliceAt function (linePoint value) 0 step =
      function (linePoint (add value step)) := by
  unfold coordinateSliceAt
  congr 1
  funext coordinate
  rw [fin_one_eq_zero coordinate]
  simp [FiniteVector.addVector, replaceCoordinate, linePoint]

/-- Repeated coordinate derivatives append on the right. -/
public theorem iteratedPartialFunction_append_single {dimension : Nat}
    (function : FiniteVector.carrier dimension → selection.Carrier)
    (steps : List (Fin dimension)) (selected : Fin dimension) :
    iteratedPartialFunction function (steps ++ [selected]) =
      fun point => partialDerivativeAt
        (iteratedPartialFunction function steps) point selected := by
  induction steps generalizing function with
  | nil => rfl
  | cons first rest induction =>
      exact induction (fun point => partialDerivativeAt function point first)

/-- Every repeated coordinate derivative of an analytic function is
analytic on the same open domain. -/
public theorem analytic_on_iteratedPartialFunction {dimension : Nat}
    {region : FiniteVector.carrier dimension → Prop}
    {function : FiniteVector.carrier dimension → selection.Carrier}
    (analytic : AnalyticOn region function)
    (steps : List (Fin dimension)) :
    AnalyticOn region (iteratedPartialFunction function steps) := by
  induction steps generalizing function with
  | nil => exact analytic
  | cons first rest induction =>
      exact induction (analytic_on_partial_derivative analytic first)

/-- An analytic function has its coordinate derivative at every point of
its domain. -/
public theorem analytic_has_partialDerivativeAt {dimension : Nat}
    {region : FiniteVector.carrier dimension → Prop}
    {function : FiniteVector.carrier dimension → selection.Carrier}
    (analytic : AnalyticOn region function)
    {point : FiniteVector.carrier dimension} (member : region point)
    (selected : Fin dimension) :
    HasDerivative (coordinateSliceAt function point selected) zero
      (partialDerivativeAt function point selected) := by
  rcases analytic_on_coordinate_derivative_at_center analytic point member
    selected with ⟨series, differentiable⟩
  rw [partialDerivativeAt_eq function point selected _ differentiable]
  exact differentiable

/-- The derivative of the given order along the single coordinate. -/
@[expose] public noncomputable def lineDerivative
    (function : FiniteVector.carrier 1 → selection.Carrier) (count : Nat) :
    FiniteVector.carrier 1 → selection.Carrier :=
  iteratedPartialFunction function (List.replicate count 0)

public theorem lineDerivative_succ
    (function : FiniteVector.carrier 1 → selection.Carrier) (count : Nat) :
    lineDerivative function (count + 1) =
      fun point => partialDerivativeAt (lineDerivative function count) point 0 := by
  unfold lineDerivative
  rw [List.replicate_succ']
  exact iteratedPartialFunction_append_single function _ 0

public theorem analytic_on_lineDerivative
    {region : FiniteVector.carrier 1 → Prop}
    {function : FiniteVector.carrier 1 → selection.Carrier}
    (analytic : AnalyticOn region function) (count : Nat) :
    AnalyticOn region (lineDerivative function count) :=
  analytic_on_iteratedPartialFunction analytic _

/-- Each derivative is the derivative of the one before it, along the line. -/
public theorem lineDerivative_has_derivative
    {region : FiniteVector.carrier 1 → Prop}
    {function : FiniteVector.carrier 1 → selection.Carrier}
    (analytic : AnalyticOn region function) (count : Nat)
    {value : selection.Carrier} (member : region (linePoint value)) :
    HasDerivative
      (fun step => lineDerivative function count (linePoint (add value step)))
      zero (lineDerivative function (count + 1) (linePoint value)) := by
  have differentiable := analytic_has_partialDerivativeAt
    (analytic_on_lineDerivative analytic count) member 0
  rw [lineDerivative_succ]
  refine HasDerivative.congr_near ?_ differentiable
  refine NearZero.of_forall fun step => ?_
  exact line_slice _ _ _

private theorem list_fin_one_replicate (steps : List (Fin 1)) :
    steps = List.replicate steps.length 0 := by
  induction steps with
  | nil => rfl
  | cons first rest induction =>
      rw [List.length_cons, List.replicate_succ, fin_one_eq_zero first,
        ← induction]

/-- Every repeated derivative of a one-coordinate function is a line
derivative. -/
public theorem iteratedPartialFunction_line
    (function : FiniteVector.carrier 1 → selection.Carrier)
    (steps : List (Fin 1)) :
    iteratedPartialFunction function steps =
      lineDerivative function steps.length := by
  unfold lineDerivative
  conv => lhs; rw [list_fin_one_replicate steps]

private theorem partialSum_zeros (count : Nat) :
    SignedSeries.partialSum (fun _ : Nat => (zero : selection.Carrier)) count =
      zero := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [SignedSeries.partialSum_succ, induction, add_zero]

/-- A series whose coefficients all vanish has the value zero. -/
public theorem value_eq_zero_of_coefficients {dimension : Nat}
    (series : Convergent dimension)
    (vanish : ∀ index, series.coefficients index = zero)
    (displacement : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball (FiniteVector.zeroVector dimension)
      series.radius displacement) :
    value series displacement inside = zero := by
  unfold value
  have tails : tailTerms series.coefficients displacement =
      fun _ => zero := by
    funext degreeValue
    exact shellTerm_zero_of_coefficients displacement
      (fun index _ => vanish index)
  rw [vanish, zero_add]
  have converges : Problib.Analysis.Real.ConvergesTo
      (SignedSeries.partialSum (tailTerms series.coefficients displacement))
      zero := by
    rw [tails]
    have equal : SignedSeries.partialSum (fun _ : Nat => (zero : selection.Carrier)) =
        fun _ => zero := funext partialSum_zeros
    rw [equal]
    exact SignedSeries.converges_to_const zero
  exact SignedSeries.sum_eq_of_converges _ _ converges

/-- Every derivative of a one-coordinate function vanishes at the point. -/
@[expose] public def FlatAt (function : FiniteVector.carrier 1 → selection.Carrier)
    (point : FiniteVector.carrier 1) : Prop :=
  ∀ count, lineDerivative function count point = zero

/-- A function vanishing on an open region has all derivatives vanishing
there. -/
public theorem lineDerivative_zero_on_open
    {region : FiniteVector.carrier 1 → Prop}
    {function : FiniteVector.carrier 1 → selection.Carrier}
    (openRegion : FiniteVector.IsOpen region)
    (vanish : ∀ point, region point → function point = zero) :
    ∀ count point, region point → lineDerivative function count point = zero := by
  intro count
  induction count with
  | zero => exact vanish
  | succ count induction =>
      intro point member
      rw [lineDerivative_succ]
      rcases openRegion point member with ⟨radius, positive, inside⟩
      have zeroDerivative : HasDerivative
          (coordinateSliceAt (lineDerivative function count) point 0) zero
          zero := by
        refine HasDerivative.congr_near ?_ (hasDerivative_const zero zero)
        refine ⟨radius, positive, fun step small => ?_⟩
        show zero = coordinateSliceAt _ point 0 (add zero step)
        rw [zero_add]
        refine (induction _ (inside _ ?_)).symm
        intro coordinate
        rw [fin_one_eq_zero coordinate]
        change lt (abs (sub (add (point 0)
          (replaceCoordinate (FiniteVector.zeroVector 1) 0 step 0))
          (point 0))) radius
        rw [show replaceCoordinate (FiniteVector.zeroVector 1) 0 step 0 = step
          from ite_eq_left rfl, add_sub_self]
        exact small
      exact partialDerivativeAt_eq _ point 0 zero zeroDerivative

/-- A flat point of an analytic function has a ball on which the function
and all of its derivatives vanish. -/
public theorem flat_ball {region : FiniteVector.carrier 1 → Prop}
    {function : FiniteVector.carrier 1 → selection.Carrier}
    (analytic : AnalyticOn region function)
    {point : FiniteVector.carrier 1} (member : region point)
    (flat : FlatAt function point) :
    ∃ radius, lt zero radius ∧
      ∀ other, FiniteVector.ball point radius other →
        region other ∧ FlatAt function other := by
  rcases (analytic_on_iff_taylor_analytic_on.mp analytic).right point member with
    ⟨series, within, agrees, coefficients⟩
  have vanish : ∀ index, series.coefficients index = zero := by
    intro index
    rw [coefficients index, iteratedPartialFunction_line, flat, zero_div]
  have zeroOnBall : ∀ other, FiniteVector.ball point series.radius other →
      function other = zero := by
    intro other inside
    rw [agrees other inside]
    exact value_eq_zero_of_coefficients series vanish _ _
  refine ⟨series.radius, series.radiusPositive, fun other inside => ?_⟩
  exact ⟨within other inside, fun count =>
    lineDerivative_zero_on_open
      (FiniteVector.ball_is_open point series.radiusPositive)
      zeroOnBall count other inside⟩

private theorem nonzero_near {region : FiniteVector.carrier 1 → Prop}
    {function : FiniteVector.carrier 1 → selection.Carrier}
    (analytic : AnalyticOn region function)
    {point : FiniteVector.carrier 1} (member : region point)
    (nonzero : function point ≠ zero) :
    ∃ radius, lt zero radius ∧
      ∀ other, FiniteVector.ball point radius other → function other ≠ zero := by
  have size := abs_positive_of_nonzero nonzero
  rcases analytic_on_continuous_at analytic point member _ size with
    ⟨radius, positive, close⟩
  refine ⟨radius, positive, fun other inside vanished => ?_⟩
  have bound := close other inside
  rw [vanished, zero_sub, abs_neg] at bound
  exact not_le_of_lt bound (le_refl _)

/-- The identity theorem: an analytic function on an open interval that is
flat at one interval point vanishes on the whole interval. -/
public theorem line_identity {center radius : selection.Carrier}
    {function : FiniteVector.carrier 1 → selection.Carrier}
    (analytic : AnalyticOn (FiniteVector.ball (linePoint center) radius)
      function)
    {start : selection.Carrier}
    (startInside : lt (abs (sub start center)) radius)
    (flat : FlatAt function (linePoint start))
    {target : selection.Carrier}
    (targetInside : lt (abs (sub target center)) radius) :
    FlatAt function (linePoint target) := by
  let flatSet : selection.Carrier → Prop := fun value =>
    lt (abs (sub value center)) radius ∧ FlatAt function (linePoint value)
  have inInterval : ∀ value, lt (sub center radius) value →
      lt value (add center radius) → lt (abs (sub value center)) radius := by
    intro value lower upper
    apply abs_lt.mpr
    constructor
    · have shifted := add_lt_add_right (neg center) lower
      have shift : add (sub center radius) (neg center) = neg radius := by
        rw [← sub_eq_add_neg, sub_eq_add_neg center radius, add_sub_self]
      rwa [shift, ← sub_eq_add_neg] at shifted
    · have shifted := add_lt_add_right (neg center) upper
      rwa [← sub_eq_add_neg, ← sub_eq_add_neg, add_sub_self] at shifted
  have fromInterval : ∀ value, lt (abs (sub value center)) radius →
      lt (sub center radius) value ∧ lt value (add center radius) := by
    intro value inside
    rcases abs_lt.mp inside with ⟨lower, upper⟩
    constructor
    · have shifted := add_lt_add_right center lower
      rwa [sub_add_cancel, add_comm, ← sub_eq_add_neg] at shifted
    · have shifted := add_lt_add_right center upper
      rwa [sub_add_cancel, add_comm] at shifted
  have openFlat : IntervalOpen (sub center radius) (add center radius)
      flatSet := by
    intro value member
    rcases flat_ball analytic ((line_ball_iff).mpr member.1) member.2 with
      ⟨ballRadius, positive, near⟩
    refine ⟨ballRadius, positive, fun other close lower upper => ?_⟩
    have result := near (linePoint other) ((line_ball_iff).mpr close)
    exact ⟨inInterval other lower upper, result.2⟩
  have closedFlat : IntervalClosed (sub center radius) (add center radius)
      flatSet := by
    intro value lower upper approximated
    have inside := inInterval value lower upper
    refine ⟨inside, fun count => ?_⟩
    apply Classical.byContradiction
    intro nonzero
    rcases nonzero_near (analytic_on_lineDerivative analytic count)
      ((line_ball_iff).mpr inside) nonzero with ⟨nearRadius, positive, near⟩
    rcases approximated nearRadius positive with ⟨other, member, close⟩
    exact near (linePoint other) ((line_ball_iff).mpr close) (member.2 count)
  have startBounds := fromInterval start startInside
  have targetBounds := fromInterval target targetInside
  exact (interval_connected openFlat closedFlat ⟨startInside, flat⟩
    startBounds.1 startBounds.2 targetBounds.1 targetBounds.2).2

/-- A zero with a nonzero derivative is isolated. -/
public theorem isolated_zero_of_derivative
    {function : selection.Carrier → selection.Carrier}
    {derivative : selection.Carrier}
    (differentiable : HasDerivative function zero derivative)
    (nonzero : derivative ≠ zero) (vanished : function zero = zero) :
    ∃ radius, lt zero radius ∧
      ∀ step, step ≠ zero → lt (abs step) radius → function step ≠ zero := by
  rcases differentiable (abs derivative) (abs_positive_of_nonzero nonzero) with
    ⟨radius, positive, close⟩
  refine ⟨radius, positive, fun step stepNonzero small stepVanished => ?_⟩
  have bound := close step stepNonzero small
  rw [secant, zero_add, stepVanished, vanished, sub_self, zero_div, zero_sub,
    abs_neg] at bound
  exact not_le_of_lt bound (le_refl _)

/-- Points where the given derivative vanishes and the next does not. At each
of them the vanishing derivative is locally nonzero off the point. -/
public theorem lineDerivative_isolated {center radius : selection.Carrier}
    {function : FiniteVector.carrier 1 → selection.Carrier}
    (analytic : AnalyticOn (FiniteVector.ball (linePoint center) radius)
      function)
    (count : Nat) {value : selection.Carrier}
    (inside : lt (abs (sub value center)) radius)
    (vanished : lineDerivative function count (linePoint value) = zero)
    (nonzero : lineDerivative function (count + 1) (linePoint value) ≠ zero) :
    ∃ isolation, lt zero isolation ∧
      ∀ other, lt (abs (sub other value)) isolation →
        lineDerivative function count (linePoint other) = zero → other = value := by
  have differentiable := lineDerivative_has_derivative analytic count
    ((line_ball_iff).mpr inside)
  rcases isolated_zero_of_derivative differentiable nonzero
    (by rw [add_zero]; exact vanished) with ⟨isolation, positive, apart⟩
  refine ⟨isolation, positive, fun other close otherVanished => ?_⟩
  apply Classical.byContradiction
  intro distinct
  have stepNonzero : sub other value ≠ zero := by
    intro equal
    apply distinct
    have restored := sub_add_cancel other value
    rw [equal, zero_add] at restored
    exact restored.symm
  apply apart (sub other value) stepNonzero close
  change lineDerivative function count (linePoint (add value (sub other value))) = zero
  rw [add_sub_cancel]
  exact otherVanished

end

end Problib.Analysis.Real.PowerSeries
