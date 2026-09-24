module

public import Problib.Analysis.Real.Absolute
public import Problib.Real.Approximation

/-! Punctured limits at zero on the sealed real carrier.

Every derivative in this directory is the limit of a difference quotient as a
nonzero displacement approaches zero. Stating that limit once, and closing it
under the field operations once, keeps each calculus rule an algebraic identity
between difference quotients rather than its own epsilon-delta argument. The
limit is punctured because a difference quotient is undefined at zero, and
every rule below therefore only ever reads nonzero displacements.
-/

set_option autoImplicit false

namespace Problib.Analysis.Real

open Problib.Real.Construction.Dedekind

noncomputable section

private instance : Std.Associative (α := selection.Carrier) mul :=
  ⟨fun left middle right => mul_assoc left middle right⟩
private instance : Std.Commutative (α := selection.Carrier) mul := ⟨mul_comm⟩
private instance : Std.Associative (α := selection.Carrier) add :=
  ⟨fun left middle right => add_assoc left middle right⟩
private instance : Std.Commutative (α := selection.Carrier) add := ⟨add_comm⟩

/-! ### Halving

Splitting a tolerance in two is the one arithmetic step every closure argument
below performs, so it is named once. -/

/-- Two on the real carrier. -/
@[expose] public def two : selection.Carrier := selection.ofRat 2

/-- Half of a value. -/
@[expose] public def half (value : selection.Carrier) : selection.Carrier :=
  div value two

/-- Doubling is multiplication by two. -/
public theorem add_self (value : selection.Carrier) :
    add value value = mul value two := by
  have expand : two = add one one := by
    have rational : ((2 : Rat)) = 1 + 1 := by decide +kernel
    rw [two, rational, ofRat_add, ofRat_one]
  rw [expand, mul_add, mul_one]

/-- Two halves recover the value. -/
public theorem add_half (value : selection.Carrier) :
    add (half value) (half value) = value := by
  rw [half, add_self, div_mul_cancel value (show two ≠ zero from ofRat_two_nonzero)]

/-- Half a positive value is positive. -/
public theorem half_positive {value : selection.Carrier} (positive : lt zero value) :
    lt zero (half value) :=
  div_positive positive ofRat_two_positive

/-- A value cancelled on the right of one summand and the left of the next. -/
private theorem cancel_middle (left cross right : selection.Carrier) :
    add (add left (neg cross)) (add cross right) = add left right := by
  calc add (add left (neg cross)) (add cross right)
      = add (add left right) (add (neg cross) cross) := by ac_rfl
    _ = add (add left right) zero := by rw [add_comm (neg cross) cross, add_neg]
    _ = add left right := add_zero _

/-! ### Nonzero displacements exist arbitrarily close to zero

Uniqueness of a limit needs a witness inside every radius, and the carrier
supplies one through its Archimedean reciprocal bound. -/

/-- Every positive radius admits a nonzero displacement strictly inside it. -/
public theorem exists_nonzero_within {radius : selection.Carrier}
    (positive : lt zero radius) :
    ∃ displacement : selection.Carrier,
      displacement ≠ zero ∧ lt (abs displacement) radius := by
  rcases exists_positive_inverse_below positive with ⟨index, indexPositive, small⟩
  have reciprocalPositive := inverse_of_positive_positive indexPositive
  refine ⟨inverse (selection.ofRat (index : Rat)), ?_, ?_⟩
  · intro vanished
    have positiveCopy := reciprocalPositive
    rw [vanished] at positiveCopy
    exact lt_irrefl zero positiveCopy
  · rwa [abs_of_nonnegative reciprocalPositive.left]

/-! ### The limit -/

/-- `Approaches function limit` holds when the values of `function` at nonzero
displacements converge to `limit` as the displacement approaches zero. -/
@[expose] public def Approaches
    (function : selection.Carrier → selection.Carrier)
    (limit : selection.Carrier) : Prop :=
  ∀ epsilon : selection.Carrier, lt zero epsilon →
    ∃ radius : selection.Carrier, lt zero radius ∧
      ∀ displacement : selection.Carrier, displacement ≠ zero →
        lt (abs displacement) radius →
          lt (abs (sub (function displacement) limit)) epsilon

/-- A constant function approaches its value. -/
public theorem approaches_const (value : selection.Carrier) :
    Approaches (fun _ => value) value := by
  intro epsilon positive
  refine ⟨one, one_positive, ?_⟩
  intro displacement _ _
  rwa [sub_self, abs_zero]

/-- The displacement itself approaches zero. -/
public theorem approaches_displacement : Approaches (fun value => value) zero := by
  intro epsilon positive
  refine ⟨epsilon, positive, ?_⟩
  intro displacement _ small
  rwa [sub_zero]

/-- Limits transport across functions that agree on a punctured neighborhood. -/
public theorem approaches_congr_near
    {function other : selection.Carrier → selection.Carrier}
    {limit radius : selection.Carrier} (radiusPositive : lt zero radius)
    (agree : ∀ displacement : selection.Carrier, displacement ≠ zero →
      lt (abs displacement) radius → function displacement = other displacement)
    (limitOf : Approaches function limit) : Approaches other limit := by
  intro epsilon positive
  rcases limitOf epsilon positive with ⟨inner, innerPositive, bound⟩
  rcases small_positive radiusPositive innerPositive with
    ⟨chosen, chosenPositive, belowRadius, belowInner⟩
  refine ⟨chosen, chosenPositive, ?_⟩
  intro displacement nonzero small
  rw [← agree displacement nonzero (lt_of_lt_of_le small belowRadius)]
  exact bound displacement nonzero (lt_of_lt_of_le small belowInner)

/-- Limits are unique. -/
public theorem approaches_unique {function : selection.Carrier → selection.Carrier}
    {first second : selection.Carrier}
    (firstLimit : Approaches function first)
    (secondLimit : Approaches function second) : first = second := by
  classical
  apply Classical.byContradiction
  intro distinct
  have gapPositive : lt zero (abs (sub first second)) :=
    abs_positive_of_nonzero (fun vanished => distinct (by
      have shifted : add second (sub first second) = add second zero :=
        congrArg (fun value => add second value) vanished
      rwa [add_sub_cancel, add_zero] at shifted))
  have tolerancePositive := half_positive gapPositive
  rcases firstLimit _ tolerancePositive with ⟨firstRadius, firstPositive, firstBound⟩
  rcases secondLimit _ tolerancePositive with ⟨secondRadius, secondPositive, secondBound⟩
  rcases small_positive firstPositive secondPositive with
    ⟨chosen, chosenPositive, belowFirst, belowSecond⟩
  rcases exists_nonzero_within chosenPositive with ⟨witness, nonzero, small⟩
  have firstClose := firstBound witness nonzero (lt_of_lt_of_le small belowFirst)
  have secondClose := secondBound witness nonzero (lt_of_lt_of_le small belowSecond)
  have triangle :=
    abs_add_le (sub first (function witness)) (sub (function witness) second)
  rw [sub_add_sub] at triangle
  rw [abs_sub_comm first (function witness)] at triangle
  have strict := add_lt_add firstClose secondClose
  rw [add_half] at strict
  exact lt_irrefl _ (lt_of_le_of_lt triangle strict)

/-- Limits add. -/
public theorem approaches_add
    {first second : selection.Carrier → selection.Carrier}
    {firstLimit secondLimit : selection.Carrier}
    (firstApproaches : Approaches first firstLimit)
    (secondApproaches : Approaches second secondLimit) :
    Approaches (fun value => add (first value) (second value))
      (add firstLimit secondLimit) := by
  intro epsilon positive
  have tolerancePositive := half_positive positive
  rcases firstApproaches _ tolerancePositive with ⟨firstRadius, firstPositive, firstBound⟩
  rcases secondApproaches _ tolerancePositive with
    ⟨secondRadius, secondPositive, secondBound⟩
  rcases small_positive firstPositive secondPositive with
    ⟨chosen, chosenPositive, belowFirst, belowSecond⟩
  refine ⟨chosen, chosenPositive, ?_⟩
  intro displacement nonzero small
  have split : sub (add (first displacement) (second displacement))
      (add firstLimit secondLimit) =
      add (sub (first displacement) firstLimit)
        (sub (second displacement) secondLimit) := by
    simp only [sub_eq_add_neg, neg_add]
    ac_rfl
  rw [split]
  have triangle := abs_add_le (sub (first displacement) firstLimit)
    (sub (second displacement) secondLimit)
  have strict := add_lt_add (firstBound displacement nonzero (lt_of_lt_of_le small belowFirst))
    (secondBound displacement nonzero (lt_of_lt_of_le small belowSecond))
  rw [add_half] at strict
  exact lt_of_le_of_lt triangle strict

/-- Limits negate. -/
public theorem approaches_neg {function : selection.Carrier → selection.Carrier}
    {limit : selection.Carrier} (approaches : Approaches function limit) :
    Approaches (fun value => neg (function value)) (neg limit) := by
  intro epsilon positive
  rcases approaches epsilon positive with ⟨radius, radiusPositive, bound⟩
  refine ⟨radius, radiusPositive, ?_⟩
  intro displacement nonzero small
  have split : sub (neg (function displacement)) (neg limit) =
      neg (sub (function displacement) limit) := by
    rw [sub_eq_add_neg, sub_eq_add_neg, neg_add, neg_neg]
  rw [split, abs_neg]
  exact bound displacement nonzero small

/-- Limits subtract. -/
public theorem approaches_sub
    {first second : selection.Carrier → selection.Carrier}
    {firstLimit secondLimit : selection.Carrier}
    (firstApproaches : Approaches first firstLimit)
    (secondApproaches : Approaches second secondLimit) :
    Approaches (fun value => sub (first value) (second value))
      (sub firstLimit secondLimit) := by
  have combined := approaches_add firstApproaches (approaches_neg secondApproaches)
  simpa only [sub_eq_add_neg] using combined

/-- A convergent function is bounded on a punctured neighborhood. -/
public theorem approaches_bounded
    {function : selection.Carrier → selection.Carrier}
    {limit : selection.Carrier} (approaches : Approaches function limit) :
    ∃ radius : selection.Carrier, lt zero radius ∧
      ∀ displacement : selection.Carrier, displacement ≠ zero →
        lt (abs displacement) radius →
          le (abs (function displacement)) (add (abs limit) one) := by
  rcases approaches one one_positive with ⟨radius, radiusPositive, bound⟩
  refine ⟨radius, radiusPositive, ?_⟩
  intro displacement nonzero small
  have triangle := abs_add_le limit (sub (function displacement) limit)
  rw [add_sub_cancel] at triangle
  refine le_trans triangle (le_of_lt ?_)
  exact add_lt_add_left (abs limit) (bound displacement nonzero small)

/-- Limits multiply. -/
public theorem approaches_mul
    {first second : selection.Carrier → selection.Carrier}
    {firstLimit secondLimit : selection.Carrier}
    (firstApproaches : Approaches first firstLimit)
    (secondApproaches : Approaches second secondLimit) :
    Approaches (fun value => mul (first value) (second value))
      (mul firstLimit secondLimit) := by
  intro epsilon positive
  rcases approaches_bounded firstApproaches with
    ⟨boundRadius, boundPositive, bounded⟩
  have firstBoundPositive : lt zero (add (abs firstLimit) one) :=
    lt_of_le_of_lt (abs_nonnegative firstLimit)
      (by
        have shifted := add_lt_add_left (abs firstLimit) one_positive
        rwa [add_zero] at shifted)
  have secondBoundPositive : lt zero (add (abs secondLimit) one) :=
    lt_of_le_of_lt (abs_nonnegative secondLimit)
      (by
        have shifted := add_lt_add_left (abs secondLimit) one_positive
        rwa [add_zero] at shifted)
  have firstBoundNonzero : add (abs firstLimit) one ≠ zero := by
    intro vanished
    have copy := firstBoundPositive
    rw [vanished] at copy
    exact lt_irrefl zero copy
  have secondBoundNonzero : add (abs secondLimit) one ≠ zero := by
    intro vanished
    have copy := secondBoundPositive
    rw [vanished] at copy
    exact lt_irrefl zero copy
  have secondTolerance : lt zero (div (half epsilon) (add (abs firstLimit) one)) :=
    div_positive (half_positive positive) firstBoundPositive
  have firstTolerance : lt zero (div (half epsilon) (add (abs secondLimit) one)) :=
    div_positive (half_positive positive) secondBoundPositive
  rcases firstApproaches _ firstTolerance with ⟨firstRadius, firstPositive, firstBound⟩
  rcases secondApproaches _ secondTolerance with
    ⟨secondRadius, secondPositive, secondBound⟩
  rcases small_positive firstPositive secondPositive with
    ⟨inner, innerPositive, belowFirst, belowSecond⟩
  rcases small_positive innerPositive boundPositive with
    ⟨chosen, chosenPositive, belowInner, belowBound⟩
  refine ⟨chosen, chosenPositive, ?_⟩
  intro displacement nonzero small
  have smallInner := lt_of_lt_of_le small belowInner
  have split : sub (mul (first displacement) (second displacement))
      (mul firstLimit secondLimit) =
      add (mul (first displacement) (sub (second displacement) secondLimit))
        (mul secondLimit (sub (first displacement) firstLimit)) := by
    calc sub (mul (first displacement) (second displacement))
          (mul firstLimit secondLimit)
        = add (mul (first displacement) (second displacement))
            (neg (mul firstLimit secondLimit)) := sub_eq_add_neg _ _
      _ = add (add (mul (first displacement) (second displacement))
              (neg (mul (first displacement) secondLimit)))
            (add (mul (first displacement) secondLimit)
              (neg (mul firstLimit secondLimit))) := (cancel_middle _ _ _).symm
      _ = add (mul (first displacement) (sub (second displacement) secondLimit))
            (mul secondLimit (sub (first displacement) firstLimit)) := by
          rw [mul_sub, mul_sub, sub_eq_add_neg, sub_eq_add_neg,
            mul_comm secondLimit (first displacement),
            mul_comm secondLimit firstLimit]
  rw [split]
  refine lt_of_le_of_lt (abs_add_le _ _) ?_
  have leftPiece :
      lt (abs (mul (first displacement) (sub (second displacement) secondLimit)))
        (half epsilon) := by
    rw [abs_mul]
    refine lt_of_le_of_lt
      (mul_le_mul_nonnegative_right
        (bounded displacement nonzero (lt_of_lt_of_le small belowBound))
        (abs_nonnegative (sub (second displacement) secondLimit))) ?_
    have scaled := mul_lt_mul_positive_left
      (secondBound displacement nonzero (lt_of_lt_of_le smallInner belowSecond))
      firstBoundPositive
    rwa [mul_div_cancel (half epsilon) firstBoundNonzero] at scaled
  have rightPiece :
      lt (abs (mul secondLimit (sub (first displacement) firstLimit)))
        (half epsilon) := by
    rw [abs_mul]
    refine lt_of_le_of_lt
      (mul_le_mul_nonnegative_right
        (le_of_lt (lt_of_le_of_lt (le_refl (abs secondLimit))
          (by
            have shifted := add_lt_add_left (abs secondLimit) one_positive
            rwa [add_zero] at shifted)))
        (abs_nonnegative (sub (first displacement) firstLimit))) ?_
    have scaled := mul_lt_mul_positive_left
      (firstBound displacement nonzero (lt_of_lt_of_le smallInner belowFirst))
      secondBoundPositive
    rwa [mul_div_cancel (half epsilon) secondBoundNonzero] at scaled
  have combined := add_lt_add leftPiece rightPiece
  rwa [add_half] at combined

/-- A function with a nonzero limit stays away from zero near the puncture.
The explicit floor is half the size of the limit, which is what every estimate
against a reciprocal needs. -/
public theorem approaches_away_from_zero
    {function : selection.Carrier → selection.Carrier}
    {limit : selection.Carrier} (approaches : Approaches function limit)
    (limitNonzero : limit ≠ zero) :
    ∃ radius : selection.Carrier, lt zero radius ∧
      ∀ displacement : selection.Carrier, displacement ≠ zero →
        lt (abs displacement) radius →
          lt (half (abs limit)) (abs (function displacement)) := by
  have sizePositive : lt zero (abs limit) := abs_positive_of_nonzero limitNonzero
  rcases approaches _ (half_positive sizePositive) with ⟨radius, radiusPositive, bound⟩
  refine ⟨radius, radiusPositive, ?_⟩
  intro displacement nonzero small
  have near := bound displacement nonzero small
  have triangle := abs_add_le (function displacement) (sub limit (function displacement))
  rw [add_sub_cancel] at triangle
  rw [abs_sub_comm limit (function displacement)] at triangle
  have shifted := lt_of_le_of_lt triangle
    (add_lt_add_left (abs (function displacement)) near)
  have expanded : lt (add (half (abs limit)) (half (abs limit)))
      (add (abs (function displacement)) (half (abs limit))) := by
    rw [add_half]
    exact shifted
  exact add_lt_add_right_iff.mp expanded

/-- A function with a nonzero limit is itself nonzero near the puncture. -/
public theorem approaches_nonzero_near
    {function : selection.Carrier → selection.Carrier}
    {limit : selection.Carrier} (approaches : Approaches function limit)
    (limitNonzero : limit ≠ zero) :
    ∃ radius : selection.Carrier, lt zero radius ∧
      ∀ displacement : selection.Carrier, displacement ≠ zero →
        lt (abs displacement) radius → function displacement ≠ zero := by
  rcases approaches_away_from_zero approaches limitNonzero with
    ⟨radius, radiusPositive, floor⟩
  refine ⟨radius, radiusPositive, ?_⟩
  intro displacement nonzero small vanished
  have below := floor displacement nonzero small
  rw [vanished, abs_zero] at below
  exact lt_irrefl zero
    (lt_trans (half_positive (abs_positive_of_nonzero limitNonzero)) below)

/-- Limits invert away from zero. -/
public theorem approaches_inverse {function : selection.Carrier → selection.Carrier}
    {limit : selection.Carrier} (approaches : Approaches function limit)
    (limitNonzero : limit ≠ zero) :
    Approaches (fun value => inverse (function value)) (inverse limit) := by
  have sizePositive : lt zero (abs limit) := abs_positive_of_nonzero limitNonzero
  have halfSizePositive := half_positive sizePositive
  rcases approaches _ halfSizePositive with ⟨sizeRadius, sizePositiveRadius, sizeBound⟩
  have floorPositive : lt zero (mul (half (abs limit)) (abs limit)) :=
    mul_positive halfSizePositive sizePositive
  have floorNonzero : mul (half (abs limit)) (abs limit) ≠ zero := by
    intro vanished
    have copy := floorPositive
    rw [vanished] at copy
    exact lt_irrefl zero copy
  intro epsilon positive
  have tolerancePositive :
      lt zero (mul epsilon (mul (half (abs limit)) (abs limit))) :=
    mul_positive positive floorPositive
  rcases approaches _ tolerancePositive with ⟨closeRadius, closePositive, closeBound⟩
  rcases small_positive sizePositiveRadius closePositive with
    ⟨chosen, chosenPositive, belowSize, belowClose⟩
  refine ⟨chosen, chosenPositive, ?_⟩
  intro displacement nonzero small
  have nearSize := sizeBound displacement nonzero (lt_of_lt_of_le small belowSize)
  have nearClose := closeBound displacement nonzero (lt_of_lt_of_le small belowClose)
  have floorBelow : lt (half (abs limit)) (abs (function displacement)) := by
    have triangle := abs_add_le (function displacement)
      (sub limit (function displacement))
    rw [add_sub_cancel] at triangle
    rw [abs_sub_comm limit (function displacement)] at triangle
    have shifted := lt_of_le_of_lt triangle
      (add_lt_add_left (abs (function displacement)) nearSize)
    have expanded : lt (add (half (abs limit)) (half (abs limit)))
        (add (abs (function displacement)) (half (abs limit))) := by
      rw [add_half]
      exact shifted
    exact add_lt_add_right_iff.mp expanded
  have valueNonzero : function displacement ≠ zero := by
    intro vanished
    have copy := floorBelow
    rw [vanished, abs_zero] at copy
    exact lt_irrefl zero (lt_trans halfSizePositive copy)
  have identity : sub (inverse (function displacement)) (inverse limit) =
      div (sub limit (function displacement)) (mul (function displacement) limit) := by
    have productNonzero : mul (function displacement) limit ≠ zero := by
      intro vanished
      rcases mul_eq_zero_iff.mp vanished with left | right
      · exact valueNonzero left
      · exact limitNonzero right
    apply mul_right_cancel_of_nonzero productNonzero
    rw [div_mul_cancel _ productNonzero, sub_mul]
    rw [← mul_assoc, inverse_mul_cancel valueNonzero, one_mul,
      mul_comm (function displacement) limit, ← mul_assoc,
      inverse_mul_cancel limitNonzero, one_mul]
  rw [identity, abs_div, abs_mul]
  have numeratorSmall :
      lt (abs (sub limit (function displacement)))
        (mul epsilon (mul (half (abs limit)) (abs limit))) := by
    rwa [abs_sub_comm limit (function displacement)]
  have denominatorLarge :
      le (mul (half (abs limit)) (abs limit))
        (mul (abs (function displacement)) (abs limit)) :=
    mul_le_mul_nonnegative_right (le_of_lt floorBelow) (abs_nonnegative limit)
  refine lt_of_le_of_lt
    (div_le_div_of_positive (abs_nonnegative (sub limit (function displacement)))
      floorPositive denominatorLarge) ?_
  rw [div_eq_mul_inverse]
  have scaled := mul_lt_mul_positive_right numeratorSmall
    (inverse_of_positive_positive floorPositive)
  rwa [mul_assoc, mul_inverse_cancel floorNonzero, mul_one] at scaled

/-! ### Continuity of a two-argument function at a point

A ratio of two estimates reads two values that move independently, so a limit
in one displacement does not describe it. This premise states the square
neighborhood once. -/

/-- `JointlyContinuousAt function first second` holds when `function` stays
within every positive tolerance of its value at `(first, second)` on some
square around that point. -/
@[expose] public def JointlyContinuousAt
    (function : selection.Carrier → selection.Carrier → selection.Carrier)
    (first second : selection.Carrier) : Prop :=
  ∀ epsilon : selection.Carrier, lt zero epsilon →
    ∃ radius : selection.Carrier, lt zero radius ∧
      ∀ left right : selection.Carrier,
        lt (abs (sub left first)) radius → lt (abs (sub right second)) radius →
          lt (abs (sub (function left right) (function first second))) epsilon

/-- One plus the size of a value is positive. -/
private theorem size_succ_positive (value : selection.Carrier) :
    lt zero (add (abs value) one) :=
  lt_of_le_of_lt (abs_nonnegative value)
    (by
      have shifted := add_lt_add_left (abs value) one_positive
      rwa [add_zero] at shifted)

/-- Multiplication is continuous at every point, in both arguments at once. -/
public theorem jointlyContinuousAt_mul (first second : selection.Carrier) :
    JointlyContinuousAt mul first second := by
  intro epsilon positive
  have firstBoundPositive := size_succ_positive first
  have secondBoundPositive := size_succ_positive second
  have secondTolerance : lt zero (div (half epsilon) (add (abs first) one)) :=
    div_positive (half_positive positive) firstBoundPositive
  have firstTolerance : lt zero (div (half epsilon) (add (abs second) one)) :=
    div_positive (half_positive positive) secondBoundPositive
  rcases small_positive firstTolerance secondTolerance with
    ⟨inner, innerPositive, belowFirst, belowSecond⟩
  rcases small_positive innerPositive one_positive with
    ⟨chosen, chosenPositive, belowInner, belowOne⟩
  refine ⟨chosen, chosenPositive, ?_⟩
  intro left right leftClose rightClose
  have leftBounded : le (abs left) (add (abs first) one) := by
    have triangle := abs_add_le first (sub left first)
    rw [add_sub_cancel] at triangle
    exact le_trans triangle (le_of_lt
      (add_lt_add_left (abs first) (lt_of_lt_of_le leftClose belowOne)))
  have split : sub (mul left right) (mul first second) =
      add (mul left (sub right second)) (mul second (sub left first)) := by
    calc sub (mul left right) (mul first second)
        = add (mul left right) (neg (mul first second)) := sub_eq_add_neg _ _
      _ = add (add (mul left right) (neg (mul left second)))
            (add (mul left second) (neg (mul first second))) := (cancel_middle _ _ _).symm
      _ = add (mul left (sub right second)) (mul second (sub left first)) := by
          rw [mul_sub, mul_sub, sub_eq_add_neg, sub_eq_add_neg,
            mul_comm second left, mul_comm second first]
  rw [split]
  refine lt_of_le_of_lt (abs_add_le _ _) ?_
  have leftPiece : lt (abs (mul left (sub right second))) (half epsilon) := by
    rw [abs_mul]
    refine lt_of_le_of_lt
      (mul_le_mul_nonnegative_right leftBounded (abs_nonnegative (sub right second))) ?_
    have scaled := mul_lt_mul_positive_left
      (lt_of_lt_of_le (lt_of_lt_of_le rightClose belowInner) belowSecond) firstBoundPositive
    rwa [mul_div_cancel (half epsilon) (nonzero_of_positive firstBoundPositive)] at scaled
  have rightPiece : lt (abs (mul second (sub left first))) (half epsilon) := by
    rw [abs_mul]
    refine lt_of_le_of_lt
      (mul_le_mul_nonnegative_right
        (le_of_lt (by
          have shifted := add_lt_add_left (abs second) one_positive
          rwa [add_zero] at shifted))
        (abs_nonnegative (sub left first))) ?_
    have scaled := mul_lt_mul_positive_left
      (lt_of_lt_of_le (lt_of_lt_of_le leftClose belowInner) belowFirst) secondBoundPositive
    rwa [mul_div_cancel (half epsilon) (nonzero_of_positive secondBoundPositive)] at scaled
  have combined := add_lt_add leftPiece rightPiece
  rwa [add_half] at combined

/-- The inverse is continuous at a nonzero point, on a whole neighborhood and
not only a punctured one: the point itself differs from its inverse by zero. -/
public theorem inverse_close {point : selection.Carrier} (nonzero : point ≠ zero) :
    ∀ epsilon : selection.Carrier, lt zero epsilon →
      ∃ radius : selection.Carrier, lt zero radius ∧
        ∀ value : selection.Carrier, lt (abs (sub value point)) radius →
          lt (abs (sub (inverse value) (inverse point))) epsilon := by
  have shifted : Approaches (fun displacement => add point displacement) point := by
    have sum := approaches_add (approaches_const point) approaches_displacement
    rwa [add_zero] at sum
  intro epsilon positive
  rcases approaches_inverse shifted nonzero epsilon positive with
    ⟨radius, radiusPositive, bound⟩
  refine ⟨radius, radiusPositive, ?_⟩
  intro value close
  by_cases same : sub value point = zero
  · have equal : value = point := by
      have restored := add_sub_cancel value point
      rw [same, add_zero] at restored
      exact restored.symm
    rw [equal, sub_self, abs_zero]
    exact positive
  · have near := bound (sub value point) same close
    dsimp only at near
    rwa [add_sub_cancel] at near

/-- Division is continuous at every point whose denominator is nonzero, in both
arguments at once. -/
public theorem jointlyContinuousAt_div {first second : selection.Carrier}
    (secondNonzero : second ≠ zero) :
    JointlyContinuousAt div first second := by
  intro epsilon positive
  rcases jointlyContinuousAt_mul first (inverse second) epsilon positive with
    ⟨productRadius, productPositive, product⟩
  rcases inverse_close secondNonzero productRadius productPositive with
    ⟨inverseRadius, inversePositive, inverseBound⟩
  rcases small_positive productPositive inversePositive with
    ⟨chosen, chosenPositive, belowProduct, belowInverse⟩
  refine ⟨chosen, chosenPositive, ?_⟩
  intro left right leftClose rightClose
  rw [div_eq_mul_inverse, div_eq_mul_inverse]
  exact product left (inverse right) (lt_of_lt_of_le leftClose belowProduct)
    (inverseBound right (lt_of_lt_of_le rightClose belowInverse))

/-- Limits divide away from zero. -/
public theorem approaches_div
    {first second : selection.Carrier → selection.Carrier}
    {firstLimit secondLimit : selection.Carrier}
    (firstApproaches : Approaches first firstLimit)
    (secondApproaches : Approaches second secondLimit)
    (secondNonzero : secondLimit ≠ zero) :
    Approaches (fun value => div (first value) (second value))
      (div firstLimit secondLimit) :=
  approaches_mul firstApproaches (approaches_inverse secondApproaches secondNonzero)

end

end Problib.Analysis.Real
