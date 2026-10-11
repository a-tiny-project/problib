module

public import Problib.Analysis.Real.Composition
public import Problib.Analysis.Real.MeanValue
public import Problib.Measure.Real.Arithmetic
public import Problib.Measure.Real.IntervalIntegral
public import Problib.Measure.Real.Uniqueness
public import Problib.Measure.Integral.Density.Change
public import Problib.Measure.Additive.Continuity
public import Problib.Measure.Integral.Lebesgue.Transport

/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot, Sébastien Gouëzel

The adjacent-interval argument of `segment_add` adapts
integral_add_adjacent_intervals in
Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35, as `Logarithm.interval_add` does for
the reciprocal. No Mathlib import is used.
-/

/-! The fundamental theorem of calculus on the sealed real carrier.

A function continuous on an open interval is bounded on each closed interval
inside it: the endpoints reached from the left with a bound form an open,
relatively closed set, and `interval_connected` carries it across.

The primitive of a continuous nonnegative function differentiates back to it
(`primitive_hasDerivative`). On a short segment the function stays near its
value at the point, so the segment's integral stays near that value times the
width, and the primitive's secant near the value. A function with that
derivative therefore differs from the primitive by a constant
(`eq_of_hasDerivative_zero_on`), so its increment is the integral of its
derivative (`primitive_eq`). Integrals are the nonnegative lower integrals of
`Problib.Measure`, read as reals once they are bounded.
-/

set_option autoImplicit false

namespace Problib.Analysis.Real

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

/-! ### Boundedness on closed intervals -/

private theorem sub_le_sub_of_le {left right : Carrier} (shift : Carrier)
    (included : le left right) : le (sub left shift) (sub right shift) := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact add_le_add_right_iff.mpr included

/-- A point between `point` and a nearby point above it is as near. -/
private theorem abs_sub_lt_of_above {point middle other radius : Carrier}
    (pointMiddle : le point middle) (middleOther : le middle other)
    (close : lt (abs (sub other point)) radius) : lt (abs (sub middle point)) radius := by
  rw [abs_of_nonnegative (sub_nonnegative pointMiddle)]
  exact lt_of_le_of_lt (le_trans (sub_le_sub_of_le point middleOther) (le_abs _)) close

/-- A point between `point` and a nearby point below it is as near. -/
private theorem abs_sub_lt_of_below {point middle other radius : Carrier}
    (otherMiddle : le other middle) (middlePoint : le middle point)
    (close : lt (abs (sub other point)) radius) : lt (abs (sub middle point)) radius := by
  rw [abs_sub_comm] at close ⊢
  rw [abs_of_nonnegative (sub_nonnegative middlePoint)]
  have shrink : le (sub point middle) (sub point other) := by
    rw [sub_eq_add_neg, sub_eq_add_neg]
    exact add_le_add_left_iff.mpr (neg_le_neg_iff.mpr otherMiddle)
  exact lt_of_le_of_lt (le_trans shrink (le_abs _)) close

/-- Continuity at `point`, read at nearby points rather than displacements. -/
private theorem near_of_continuous {function : Carrier → Carrier} {point tolerance : Carrier}
    (continuous : Approaches (fun displacement => function (add point displacement))
      (function point)) (positive : lt zero tolerance) :
    ∃ radius, lt zero radius ∧ ∀ other, lt (abs (sub other point)) radius →
      le (abs (sub (function other) (function point))) tolerance := by
  rcases continuous tolerance positive with ⟨radius, radiusPositive, close⟩
  refine ⟨radius, radiusPositive, fun other near => ?_⟩
  by_cases same : sub other point = zero
  · have shifted := add_sub_cancel other point
    rw [same, add_zero] at shifted
    rw [← shifted, sub_self, abs_zero]
    exact le_of_lt positive
  · have moved : lt (abs (sub (function (add point (sub other point))) (function point)))
        tolerance := close _ same near
    rw [add_sub_cancel] at moved
    exact le_of_lt moved

/-- Continuity at a point bounds the function near it by one more than its
value there. -/
private theorem near_bound {function : Carrier → Carrier} {point : Carrier}
    (continuous : Approaches (fun displacement => function (add point displacement))
      (function point)) :
    ∃ radius, lt zero radius ∧ ∀ other, lt (abs (sub other point)) radius →
      le (abs (function other)) (add (abs (function point)) one) := by
  rcases near_of_continuous continuous one_positive with ⟨radius, radiusPositive, close⟩
  refine ⟨radius, radiusPositive, fun other near => ?_⟩
  have split := abs_add_le (sub (function other) (function point)) (function point)
  rw [sub_add_cancel] at split
  have bounded := add_le_add (close other near) (le_refl (abs (function point)))
  rw [add_comm one] at bounded
  exact le_trans split bounded

/-- A function continuous at every point of an open interval is bounded on
each closed interval inside it. The endpoints reached from `left` with a bound
form an open, relatively closed set, so `interval_connected` carries the bound
to `right`. -/
public theorem bounded_of_continuous {function : Carrier → Carrier} {lower upper : Carrier}
    (continuous : ∀ point, lt lower point → lt point upper →
      Approaches (fun displacement => function (add point displacement)) (function point))
    {left right : Carrier} (lowerLeft : lt lower left) (rightUpper : lt right upper) :
    ∃ bound, ∀ point, le left point → le point right → le (abs (function point)) bound := by
  let reached : Carrier → Prop := fun endpoint =>
    ∃ bound, ∀ point, le left point → le point endpoint → le (abs (function point)) bound
  have below : ∀ endpoint, lt endpoint left → reached endpoint := fun endpoint before =>
    ⟨zero, fun _ leftPoint pointEnd =>
      absurd (lt_of_le_of_lt leftPoint (lt_of_le_of_lt pointEnd before)) (lt_irrefl left)⟩
  -- A bound up to `endpoint` and one near `center` past it bound up to `target`.
  have extend : ∀ endpoint target bound center,
      (∀ point, le left point → le point endpoint → le (abs (function point)) bound) →
      (∀ point, lt endpoint point → le point target →
        le (abs (function point)) (add (abs (function center)) one)) → reached target :=
    fun endpoint _ bound center inside outside =>
      ⟨add (abs bound) (add (abs (function center)) one), fun point leftPoint pointTarget => by
        by_cases early : le point endpoint
        · have widened := add_le_add (le_refl (abs bound))
            (add_nonnegative (abs_nonnegative (function center)) one_nonnegative)
          rw [add_zero] at widened
          exact le_trans (inside point leftPoint early) (le_trans (le_abs bound) widened)
        · have widened := add_le_add (abs_nonnegative bound)
            (le_refl (add (abs (function center)) one))
          rw [zero_add] at widened
          exact le_trans (outside point (lt_of_not_le early) pointTarget) widened⟩
  have openSet : IntervalOpen lower upper reached := by
    rintro endpoint ⟨bound, inside⟩
    by_cases late : le left endpoint
    · by_cases beyond : le upper endpoint
      · refine ⟨one, one_positive, fun other _ _ otherUpper => ⟨bound, ?_⟩⟩
        exact fun point leftPoint pointOther => inside point leftPoint
          (le_trans pointOther (le_trans (le_of_lt otherUpper) beyond))
      · rcases near_bound (continuous endpoint (lt_of_lt_of_le lowerLeft late)
          (lt_of_not_le beyond)) with ⟨radius, radiusPositive, nearby⟩
        exact ⟨radius, radiusPositive, fun other near _ _ =>
          extend endpoint other bound endpoint inside (fun point endPoint pointOther =>
            nearby point (abs_sub_lt_of_above (le_of_lt endPoint) pointOther near))⟩
    · have early := lt_of_not_le late
      refine ⟨sub left endpoint, sub_positive_iff.mpr early, fun other near _ _ => ?_⟩
      apply below other
      have shifted := lt_of_le_of_lt (le_abs _) near
      rw [sub_eq_add_neg, sub_eq_add_neg] at shifted
      exact add_lt_add_right_iff.mp shifted
  have closedSet : IntervalClosed lower upper reached := by
    intro point lowerPoint pointUpper approximated
    by_cases late : le left point
    · rcases near_bound (continuous point lowerPoint pointUpper) with
        ⟨radius, radiusPositive, nearby⟩
      rcases approximated radius radiusPositive with ⟨other, ⟨bound, inside⟩, near⟩
      by_cases after : le point other
      · exact ⟨bound, fun value leftValue valuePoint =>
          inside value leftValue (le_trans valuePoint after)⟩
      · exact extend other point bound point inside (fun value otherValue valuePoint =>
          nearby value (abs_sub_lt_of_below (le_of_lt otherValue) valuePoint near))
    · exact below point (lt_of_not_le late)
  by_cases ordered : le left right
  · have start : reached left := ⟨abs (function left), fun point leftPoint pointLeft => by
      rw [le_antisymm pointLeft leftPoint]
      exact le_refl _⟩
    exact interval_connected openSet closedSet start lowerLeft
      (lt_of_le_of_lt ordered rightUpper) (lt_of_lt_of_le lowerLeft ordered) rightUpper
  · exact below right (lt_of_not_le ordered)

/-! ### Integrals over half-open intervals -/

/-- The integral of a function's nonnegative part over `(left, right]`. -/
@[expose] public def segment (function : Carrier → Carrier) (left right : Carrier) : ENNReal :=
  lintegral (volume.restrict (Ioc left right)) (fun value => ENNReal.ofReal (function value))

/-- The primitive from `base`, read as a real number. -/
@[expose] public def primitive (function : Carrier → Carrier) (base point : Carrier) :
    Carrier :=
  ENNReal.toReal (segment function base point)

private theorem toReal_add_finite {left right : ENNReal} (leftFinite : ENNReal.Finite left)
    (rightFinite : ENNReal.Finite right) :
    ENNReal.toReal (ENNReal.add left right) =
      add (ENNReal.toReal left) (ENNReal.toReal right) := by
  rcases ENNReal.exists_finite_of_finite leftFinite with ⟨left, rfl⟩
  rcases ENNReal.exists_finite_of_finite rightFinite with ⟨right, rfl⟩
  rfl

private theorem ofReal_mul_ofReal {left right : Carrier} (leftNonnegative : le zero left)
    (rightNonnegative : le zero right) :
    ENNReal.mul (ENNReal.ofReal left) (ENNReal.ofReal right) =
      ENNReal.ofReal (mul left right) := by
  rw [ENNReal.ofReal_of_nonnegative leftNonnegative,
    ENNReal.ofReal_of_nonnegative rightNonnegative,
    ENNReal.ofReal_of_nonnegative (mul_nonnegative leftNonnegative rightNonnegative),
    ENNReal.finite_mul_finite]
  apply congrArg ENNReal.finite
  apply NNReal.ext
  rfl

private theorem segment_self (function : Carrier → Carrier) (point : Carrier) :
    segment function point point = ENNReal.zero := by
  have empty : Ioc point point = Set.empty := by
    apply Set.ext
    intro value
    exact ⟨fun member => member.1.2 member.2, False.elim⟩
  rw [segment, empty, Measure.restrict_empty, lintegral_zero_measure]

/-- Adjacent segments add. -/
public theorem segment_add {function : Carrier → Carrier}
    (measurable : MeasurableMap borel borel function) {left middle right : Carrier}
    (leftMiddle : le left middle) (middleRight : le middle right) :
    segment function left right =
      ENNReal.add (segment function left middle) (segment function middle right) := by
  classical
  let q := fun value => ENNReal.ofReal (function value)
  have qMeasurable : ENNRealMeasurable borel q := ofReal_measurable.comp measurable
  have split : ∀ t, ennrealIndicator (Ioc left right) q t =
      ENNReal.add (ennrealIndicator (Ioc left middle) q t)
        (ennrealIndicator (Ioc middle right) q t) := by
    intro t
    by_cases ht : Ioc left right t
    · by_cases htb : le t middle
      · have first : Ioc left middle t := ⟨ht.1, htb⟩
        have second : ¬Ioc middle right t := fun h => h.1.2 htb
        simp only [ennrealIndicator, ennrealPiecewise, ite_eq_left ht, ite_eq_left first,
          ite_eq_right second, ENNReal.add_zero]
      · have first : ¬Ioc left middle t := fun h => htb h.2
        have second : Ioc middle right t := ⟨lt_of_not_le htb, ht.2⟩
        simp only [ennrealIndicator, ennrealPiecewise, ite_eq_left ht, ite_eq_right first,
          ite_eq_left second, ENNReal.zero_add]
    · have first : ¬Ioc left middle t := fun h => ht ⟨h.1, le_trans h.2 middleRight⟩
      have second : ¬Ioc middle right t := by
        intro h
        exact ht ⟨⟨le_trans leftMiddle h.1.1,
          fun reverse => h.1.2 (le_trans reverse leftMiddle)⟩, h.2⟩
      simp only [ennrealIndicator, ennrealPiecewise, ite_eq_right ht, ite_eq_right first,
        ite_eq_right second, ENNReal.zero_add]
  calc
    segment function left right = lintegral volume (ennrealIndicator (Ioc left right) q) :=
      (lintegral_indicator volume _ (measurable_ioc left right) q).symm
    _ = lintegral volume (fun t => ENNReal.add
        (ennrealIndicator (Ioc left middle) q t) (ennrealIndicator (Ioc middle right) q t)) :=
      lintegral_congr volume split
    _ = ENNReal.add (segment function left middle) (segment function middle right) := by
      rw [lintegral_add volume
        (ENNRealMeasurable.indicator (measurable_ioc left middle) qMeasurable)
        (ENNRealMeasurable.indicator (measurable_ioc middle right) qMeasurable),
        lintegral_indicator volume _ (measurable_ioc left middle),
        lintegral_indicator volume _ (measurable_ioc middle right)]
      rfl

private theorem segment_le {function : Carrier → Carrier} {left right bound : Carrier}
    (bounded : ∀ value, Ioc left right value → le (function value) bound) :
    ENNReal.le (segment function left right)
      (ENNReal.mul (ENNReal.ofReal bound) (ENNReal.ofReal (sub right left))) := by
  have h := @lintegral_mono_ae _ borel (volume.restrict (Ioc left right))
    (fun value => ENNReal.ofReal (function value)) (fun _ => ENNReal.ofReal bound)
    ((volume.ae_restrict_mem (measurable_ioc left right)).mono (fun value inside =>
      ENNReal.ofReal_monotone (bounded value inside)))
  rw [lintegral_const, Measure.restrict_apply_univ, volume_ioc] at h
  exact h

private theorem segment_ge {function : Carrier → Carrier} {left right bound : Carrier}
    (bounded : ∀ value, Ioc left right value → le bound (function value)) :
    ENNReal.le (ENNReal.mul (ENNReal.ofReal bound) (ENNReal.ofReal (sub right left)))
      (segment function left right) := by
  have h := @lintegral_mono_ae _ borel (volume.restrict (Ioc left right))
    (fun _ => ENNReal.ofReal bound) (fun value => ENNReal.ofReal (function value))
    ((volume.ae_restrict_mem (measurable_ioc left right)).mono (fun value inside =>
      ENNReal.ofReal_monotone (bounded value inside)))
  rw [lintegral_const, Measure.restrict_apply_univ, volume_ioc] at h
  exact h

/-- A segment inside an interval of continuity has a finite integral. -/
public theorem segment_finite {function : Carrier → Carrier} {lower upper : Carrier}
    (continuous : ∀ point, lt lower point → lt point upper →
      Approaches (fun displacement => function (add point displacement)) (function point))
    {left right : Carrier} (lowerLeft : lt lower left) (rightUpper : lt right upper) :
    ENNReal.Finite (segment function left right) := by
  rcases bounded_of_continuous continuous lowerLeft rightUpper with ⟨bound, bounded⟩
  exact ENNReal.finite_of_le
    (segment_le (fun value inside =>
      le_trans (le_abs _) (bounded value (le_of_lt inside.1) inside.2)))
    (ENNReal.mul_finite (ENNReal.ofReal_finite _) (ENNReal.ofReal_finite _))

/-- On a segment where a nonnegative function stays within `tolerance` of
`center`, its integral stays within `tolerance` times the width of `center`
times the width. -/
private theorem segment_close {function : Carrier → Carrier}
    {left right center tolerance : Carrier} (ordered : le left right)
    (nonnegative : ∀ value, Ioc left right value → le zero (function value))
    (close : ∀ value, Ioc left right value →
      le (abs (sub (function value) center)) tolerance) :
    ENNReal.Finite (segment function left right) ∧
      le (abs (sub (ENNReal.toReal (segment function left right))
          (mul center (sub right left))))
        (mul tolerance (sub right left)) := by
  have width : le zero (sub right left) := sub_nonnegative ordered
  have above : ∀ value, Ioc left right value →
      le (function value) (add tolerance center) := by
    intro value member
    have h := add_le_add (abs_le.mp (close value member)).2 (le_refl center)
    rwa [sub_add_cancel] at h
  have below : ∀ value, Ioc left right value →
      le (add (neg tolerance) center) (function value) := by
    intro value member
    have h := add_le_add (abs_le.mp (close value member)).1 (le_refl center)
    rwa [sub_add_cancel] at h
  have upperBound := segment_le above
  have finite : ENNReal.Finite (segment function left right) :=
    ENNReal.finite_of_le upperBound
      (ENNReal.mul_finite (ENNReal.ofReal_finite _) (ENNReal.ofReal_finite _))
  refine ⟨finite, ?_⟩
  by_cases strict : lt left right
  · have highNonnegative : le zero (add tolerance center) :=
      le_trans (nonnegative right ⟨strict, le_refl right⟩) (above right ⟨strict, le_refl right⟩)
    rw [ofReal_mul_ofReal highNonnegative width] at upperBound
    have upperReal := (ENNReal.le_ofReal_iff_toReal_le finite
      (mul_nonnegative highNonnegative width)).mp upperBound
    have lowerReal : le (mul (add (neg tolerance) center) (sub right left))
        (ENNReal.toReal (segment function left right)) := by
      by_cases lowNonnegative : le zero (add (neg tolerance) center)
      · have lowerBound := segment_ge below
        rw [ofReal_mul_ofReal lowNonnegative width] at lowerBound
        exact (ENNReal.ofReal_le_iff_le_toReal finite).mp lowerBound
      · have h := mul_le_mul_nonnegative_right (le_of_lt (lt_of_not_le lowNonnegative)) width
        rw [zero_mul] at h
        exact le_trans h (ENNReal.toReal_nonnegative _)
    rw [add_mul] at upperReal lowerReal
    rw [neg_mul] at lowerReal
    apply abs_le.mpr
    constructor
    · have h := sub_le_sub_of_le (mul center (sub right left)) lowerReal
      rwa [sub_eq_add_neg (add _ _), add_assoc, add_neg, add_zero] at h
    · have h := sub_le_sub_of_le (mul center (sub right left)) upperReal
      rwa [sub_eq_add_neg (add _ _), add_assoc, add_neg, add_zero] at h
  · have back : le right left :=
      Classical.byContradiction fun reverse => strict ⟨ordered, reverse⟩
    have equal : right = left := le_antisymm back ordered
    subst equal
    rw [segment_self, ENNReal.toReal_zero, sub_self, mul_zero, mul_zero, sub_self, abs_zero]
    exact le_refl zero

/-- Between two points past `base` where a nonnegative function stays within
`tolerance` of `center`, the primitive increases by `center` times the width,
to within `tolerance` times the width. -/
private theorem increment_close {function : Carrier → Carrier}
    (measurable : MeasurableMap borel borel function)
    {lower upper base left right center tolerance : Carrier}
    (continuous : ∀ value, lt lower value → lt value upper →
      Approaches (fun displacement => function (add value displacement)) (function value))
    (lowerBase : lt lower base) (baseLeft : le base left) (ordered : le left right)
    (rightUpper : lt right upper)
    (nonnegative : ∀ value, Ioc left right value → le zero (function value))
    (close : ∀ value, Ioc left right value →
      le (abs (sub (function value) center)) tolerance) :
    le (abs (sub (sub (primitive function base right) (primitive function base left))
        (mul center (sub right left))))
      (mul tolerance (sub right left)) := by
  have estimate := segment_close ordered nonnegative close
  have split : primitive function base right =
      add (primitive function base left) (ENNReal.toReal (segment function left right)) := by
    unfold primitive
    rw [segment_add measurable baseLeft ordered, toReal_add_finite (segment_finite continuous
      lowerBase (lt_of_le_of_lt ordered rightUpper)) estimate.1]
  rw [split, add_sub_self]
  exact estimate.2

/-! ### The fundamental theorem -/

/-- The primitive of a continuous nonnegative function differentiates to the
function at each point past its base. -/
public theorem primitive_hasDerivative {function : Carrier → Carrier}
    (measurable : MeasurableMap borel borel function) {lower upper base point : Carrier}
    (continuous : ∀ value, lt lower value → lt value upper →
      Approaches (fun displacement => function (add value displacement)) (function value))
    (nonnegative : ∀ value, lt lower value → lt value upper → le zero (function value))
    (lowerBase : lt lower base) (basePoint : lt base point) (pointUpper : lt point upper) :
    HasDerivative (primitive function base) point (function point) := by
  intro epsilon positive
  rcases near_of_continuous (continuous point (lt_trans lowerBase basePoint) pointUpper)
    (half_positive positive) with ⟨near, nearPositive, closeAt⟩
  rcases small_positive nearPositive (sub_positive_iff.mpr basePoint) with
    ⟨inner, innerPositive, innerNear, innerBase⟩
  rcases small_positive innerPositive (sub_positive_iff.mpr pointUpper) with
    ⟨radius, radiusPositive, radiusInner, radiusUpper⟩
  refine ⟨radius, radiusPositive, fun displacement nonzero small => ?_⟩
  have nearSmall : lt (abs displacement) near :=
    lt_of_lt_of_le small (le_trans radiusInner innerNear)
  have baseSmall : lt (abs displacement) (sub point base) :=
    lt_of_lt_of_le small (le_trans radiusInner innerBase)
  have upperSmall : lt (abs displacement) (sub upper point) :=
    lt_of_lt_of_le small radiusUpper
  have increment : le (abs (sub (sub (primitive function base (add point displacement))
        (primitive function base point)) (mul (function point) displacement)))
      (mul (half epsilon) (abs displacement)) := by
    rcases lt_or_lt_of_ne nonzero with negative | positiveStep
    · have absEq : abs displacement = neg displacement :=
        abs_of_nonpositive (le_of_lt negative)
      rw [absEq] at nearSmall baseSmall ⊢
      have ordered : le (add point displacement) point := by
        have h := add_le_add_left_iff (shift := point) |>.mpr (le_of_lt negative)
        rwa [add_zero] at h
      have width : sub point (add point displacement) = neg displacement := by
        rw [sub_eq_add_neg, neg_add, ← add_assoc, add_neg, zero_add]
      have startBase : lt base (add point displacement) := by
        have h := sub_positive_iff.mpr baseSmall
        have identity : sub (sub point base) (neg displacement) =
            sub (add point displacement) base := by
          rw [sub_eq_add_neg (sub point base), neg_neg, sub_eq_add_neg point,
            sub_eq_add_neg (add point displacement), add_assoc, add_assoc,
            add_comm (neg base) displacement]
        rw [identity] at h
        exact sub_positive_iff.mp h
      have estimate := increment_close (center := function point) measurable continuous
        lowerBase (le_of_lt startBase) ordered pointUpper
        (fun value member => nonnegative value
          (lt_trans (lt_trans lowerBase startBase) member.1)
          (lt_of_le_of_lt member.2 pointUpper))
        (fun value member => closeAt value (abs_sub_lt_of_below (le_of_lt member.1) member.2
          (by rw [add_sub_self, absEq]; exact nearSmall)))
      rw [width] at estimate
      have flip : sub (sub (primitive function base (add point displacement))
            (primitive function base point)) (mul (function point) displacement) =
          neg (sub (sub (primitive function base point)
            (primitive function base (add point displacement)))
            (mul (function point) (neg displacement))) := by
        rw [mul_neg, neg_sub_distrib, neg_neg, neg_sub]
      rw [flip, abs_neg]
      exact estimate
    · have absEq : abs displacement = displacement :=
        abs_of_nonnegative (le_of_lt positiveStep)
      rw [absEq] at nearSmall upperSmall ⊢
      have ordered : le point (add point displacement) := by
        have h := add_le_add_left_iff (shift := point) |>.mpr (le_of_lt positiveStep)
        rwa [add_zero] at h
      have endUpper : lt (add point displacement) upper := by
        have h := add_lt_add_left point upperSmall
        rwa [add_sub_cancel] at h
      have estimate := increment_close (center := function point) measurable continuous
        lowerBase (le_of_lt basePoint) ordered endUpper
        (fun value member => nonnegative value
          (lt_trans (lt_trans lowerBase basePoint) member.1)
          (lt_of_le_of_lt member.2 endUpper))
        (fun value member => closeAt value (abs_sub_lt_of_above (le_of_lt member.1) member.2
          (by rw [add_sub_self, absEq]; exact nearSmall)))
      rwa [add_sub_self] at estimate
  have quotient := sub_div (sub (primitive function base (add point displacement))
    (primitive function base point)) (mul (function point) displacement) displacement
  rw [mul_div_assoc, div_self nonzero, mul_one] at quotient
  show lt (abs (sub (div (sub (primitive function base (add point displacement))
    (primitive function base point)) displacement) (function point))) epsilon
  rw [← quotient, abs_div]
  have absPositive := abs_positive_of_nonzero nonzero
  have bound := div_le_div_right absPositive increment
  rw [mul_div_assoc, div_self (nonzero_of_positive absPositive), mul_one] at bound
  have halfBelow : lt (half epsilon) epsilon := by
    have h := add_lt_add_left (half epsilon) (half_positive positive)
    rwa [add_zero, add_half] at h
  exact lt_of_le_of_lt bound halfBelow

/-- The fundamental theorem of calculus. A function whose derivative is
continuous and nonnegative on an open interval increases across each segment
inside it by the integral of its derivative there. -/
public theorem primitive_eq {function derivative : Carrier → Carrier}
    (measurable : MeasurableMap borel borel derivative) {lower upper : Carrier}
    (differentiable : ∀ value, lt lower value → lt value upper →
      HasDerivative function value (derivative value))
    (continuous : ∀ value, lt lower value → lt value upper →
      Approaches (fun displacement => derivative (add value displacement)) (derivative value))
    (nonnegative : ∀ value, lt lower value → lt value upper → le zero (derivative value))
    {first second : Carrier} (lowerFirst : lt lower first) (ordered : le first second)
    (secondUpper : lt second upper) :
    segment derivative first second = ENNReal.ofReal (sub (function second) (function first)) := by
  rcases exists_rational_between lowerFirst with ⟨rational, lowerBase, baseFirst⟩
  have flat : ∀ value, lt (selection.ofRat rational) value → lt value upper →
      HasDerivative (fun point => sub (function point)
        (primitive derivative (selection.ofRat rational) point)) value zero := by
    intro value baseValue valueUpper
    have h := hasDerivative_sub (differentiable value (lt_trans lowerBase baseValue) valueUpper)
      (primitive_hasDerivative measurable continuous nonnegative lowerBase baseValue valueUpper)
    rwa [sub_self] at h
  have firstUpper := lt_of_le_of_lt ordered secondUpper
  have same : sub (function first) (primitive derivative (selection.ofRat rational) first) =
      sub (function second) (primitive derivative (selection.ofRat rational) second) :=
    eq_of_hasDerivative_zero_on flat baseFirst firstUpper (lt_of_lt_of_le baseFirst ordered)
      secondUpper
  have finite := segment_finite continuous lowerFirst secondUpper
  have split : primitive derivative (selection.ofRat rational) second =
      add (primitive derivative (selection.ofRat rational) first)
        (ENNReal.toReal (segment derivative first second)) := by
    unfold primitive
    rw [segment_add measurable (le_of_lt baseFirst) ordered,
      toReal_add_finite (segment_finite continuous lowerBase firstUpper) finite]
  have real : ENNReal.toReal (segment derivative first second) =
      sub (function second) (function first) := by
    have rebuilt := add_sub_add_comm
      (sub (function second) (primitive derivative (selection.ofRat rational) second))
      (sub (function first) (primitive derivative (selection.ofRat rational) first))
      (primitive derivative (selection.ofRat rational) second)
      (primitive derivative (selection.ofRat rational) first)
    rw [sub_add_cancel, sub_add_cancel, ← same, sub_self, zero_add, split,
      add_sub_self] at rebuilt
    exact rebuilt.symm
  rw [← real, ENNReal.ofReal_toReal finite]

/-! ### Exhausted intervals -/

private theorem le_maximum (left right : Carrier) :
    le left (maximum left right) ∧ le right (maximum left right) := by
  classical
  unfold maximum
  by_cases included : le left right
  · rw [ite_eq_left included]
    exact ⟨included, le_refl right⟩
  · rw [ite_eq_right included]
    exact ⟨le_refl left, le_of_lt (lt_of_not_le included)⟩

private theorem ioc_empty {left right : Carrier} (reversed : le right left) :
    Ioc left right = Set.empty :=
  Set.ext fun _ => ⟨fun member => member.1.2 (le_trans member.2 reversed), False.elim⟩

private theorem ioc_inter (a b c d : Carrier) :
    Set.inter (Ioc a b) (Ioc c d) = Ioc (maximum a c) (minimum b d) := by
  apply Set.ext
  intro value
  change ((lt a value ∧ le value b) ∧ (lt c value ∧ le value d)) ↔
    lt (maximum a c) value ∧ le value (minimum b d)
  rw [maximum_lt_iff, le_minimum_iff]
  exact ⟨fun h => ⟨⟨h.1.1, h.2.1⟩, h.1.2, h.2.2⟩, fun h => ⟨⟨h.1.1, h.2.1⟩, h.1.2, h.2.2⟩⟩

/-- An interval of the line presented as the union of growing segments whose
ends lie in it. -/
public structure Exhaustion (region : Set Carrier) where
  measurable : borel.Measurable region
  convex : ∀ first middle second, region first → region second →
    le first middle → le middle second → region middle
  lowerEnd : Nat → Carrier
  upperEnd : Nat → Carrier
  lowerEndIn : ∀ index, region (lowerEnd index)
  upperEndIn : ∀ index, region (upperEnd index)
  lowerAntitone : ∀ first second, first ≤ second → le (lowerEnd second) (lowerEnd first)
  upperMonotone : ∀ first second, first ≤ second → le (upperEnd first) (upperEnd second)
  exhausts : ∀ value, region value →
    ∃ index, lt (lowerEnd index) value ∧ le value (upperEnd index)

namespace Exhaustion

/-- A measure that gives the complement of a region no mass measures each set
by its part in the region. -/
private theorem concentrated {region : Set Carrier} (measurable : borel.Measurable region)
    (measure : Measure borel) (null : measure (Set.complement region) = ENNReal.zero)
    {set : Set Carrier} (setMeasurable : borel.Measurable set) :
    measure set = measure (Set.inter set region) := by
  have split : (Measure.add (measure.restrict region)
      (measure.restrict (Set.complement region))) set = measure set := by
    rw [Measure.restrict_add_complement measure measurable]
  rw [Measure.add_apply_measurable _ _ setMeasurable, Measure.restrict_apply _ _ setMeasurable,
    Measure.restrict_apply _ _ setMeasurable] at split
  have outside := measure.mono (left := Set.inter set (Set.complement region))
    (right := Set.complement region) (fun _ member => member.2)
  rw [null, ENNReal.le_zero_iff] at outside
  rw [outside, ENNReal.add_zero] at split
  exact split.symm

/-- Two measures that give an exhausted interval's complement no mass are
equal when they agree on every half-open interval with ends in it. Each
half-open interval meets the region in the union of its growing clipped
segments, so continuity from below carries the agreement to it, and
`measure_ext_ioc` to every set. -/
public theorem measure_ext {region : Set Carrier} (exhaustion : Exhaustion region)
    {left right : Measure borel} (leftNull : left (Set.complement region) = ENNReal.zero)
    (rightNull : right (Set.complement region) = ENNReal.zero)
    (rightFinite : ∀ lower upper, ENNReal.Finite (right (Ioc lower upper)))
    (agree : ∀ lower upper, region lower → region upper → le lower upper →
      left (Ioc lower upper) = right (Ioc lower upper)) :
    left = right := by
  apply measure_ext_ioc rightFinite
  intro a b
  let pieces : Nat → Set Carrier := fun index =>
    Set.inter (Ioc a b) (Ioc (exhaustion.lowerEnd index) (exhaustion.upperEnd index))
  have piecesMeasurable : ∀ index, borel.Measurable (pieces index) :=
    fun _ => borel.inter (measurable_ioc _ _) (measurable_ioc _ _)
  have growing : Set.MonotoneFamily pieces := fun first second ordered _ member =>
    ⟨member.1, lt_of_le_of_lt (exhaustion.lowerAntitone first second ordered) member.2.1,
      le_trans member.2.2 (exhaustion.upperMonotone first second ordered)⟩
  have union : Set.inter (Ioc a b) region = Set.iUnion pieces := by
    apply Set.ext
    intro value
    constructor
    · rintro ⟨member, inside⟩
      rcases exhaustion.exhausts value inside with ⟨index, lowerValue, valueUpper⟩
      exact ⟨index, member, lowerValue, valueUpper⟩
    · rintro ⟨index, member, lowerValue, valueUpper⟩
      exact ⟨member, exhaustion.convex _ value _ (exhaustion.lowerEndIn index)
        (exhaustion.upperEndIn index) (le_of_lt lowerValue) valueUpper⟩
  have each : ∀ index, left (pieces index) = right (pieces index) := by
    intro index
    show left (Set.inter _ _) = right (Set.inter _ _)
    rw [ioc_inter]
    by_cases ordered : le (maximum a (exhaustion.lowerEnd index))
      (minimum b (exhaustion.upperEnd index))
    · have low := le_maximum a (exhaustion.lowerEnd index)
      have high := le_minimum_iff.mp (le_refl (minimum b (exhaustion.upperEnd index)))
      have inRegion := fun value (lowValue : le (exhaustion.lowerEnd index) value)
          (valueHigh : le value (exhaustion.upperEnd index)) =>
        exhaustion.convex _ value _ (exhaustion.lowerEndIn index)
          (exhaustion.upperEndIn index) lowValue valueHigh
      exact agree _ _ (inRegion _ low.2 (le_trans ordered high.2))
        (inRegion _ (le_trans low.2 ordered) high.2) ordered
    · rw [ioc_empty (le_of_lt (lt_of_not_le ordered)), left.empty_apply, right.empty_apply]
  rw [concentrated exhaustion.measurable left leftNull (measurable_ioc a b),
    concentrated exhaustion.measurable right rightNull (measurable_ioc a b), union,
    Measure.continuity_from_below left pieces piecesMeasurable growing,
    Measure.continuity_from_below right pieces piecesMeasurable growing]
  exact congrArg ENNReal.iSup (funext each)

private theorem ofRat_nat_le {first second : Nat} (ordered : first ≤ second) :
    le (selection.ofRat (first : Rat)) (selection.ofRat (second : Rat)) :=
  (ofRat_le_iff _ _).mpr (Rat.natCast_le_natCast.mpr ordered)

/-- The line, exhausted by `(-n, n]`. -/
public def line : Exhaustion Set.univ where
  measurable := borel.univ
  convex := fun _ _ _ _ _ _ _ => True.intro
  lowerEnd := fun index => neg (selection.ofRat (index : Rat))
  upperEnd := fun index => selection.ofRat (index : Rat)
  lowerEndIn := fun _ => True.intro
  upperEndIn := fun _ => True.intro
  lowerAntitone := fun _ _ ordered => neg_le_neg_iff.mpr (ofRat_nat_le ordered)
  upperMonotone := fun _ _ ordered => ofRat_nat_le ordered
  exhausts := fun value _ => by
    rcases exists_nat_strict_upper (neg value) with ⟨below, belowBound⟩
    rcases exists_nat_upper value with ⟨above, aboveBound⟩
    refine ⟨below + above, ?_, le_trans aboveBound (ofRat_nat_le (Nat.le_add_left _ _))⟩
    have reflected := neg_lt_neg_iff.mpr
      (lt_of_lt_of_le belowBound (ofRat_nat_le (Nat.le_add_right below above)))
    rwa [neg_neg] at reflected

/-- The positive ray, exhausted by `(1/(n+1), n+1]`. -/
public def positive : Exhaustion (Ioi zero) where
  measurable := measurable_ioi zero
  convex := fun _ _ _ firstIn _ firstMiddle _ => lt_of_lt_of_le firstIn firstMiddle
  lowerEnd := fun index => inverse (selection.ofRat ((index + 1 : Nat) : Rat))
  upperEnd := fun index => selection.ofRat ((index + 1 : Nat) : Rat)
  lowerEndIn := fun index => inverse_of_positive_positive (ofRat_succ_positive index)
  upperEndIn := fun index => ofRat_succ_positive index
  lowerAntitone := fun _ _ ordered => inverse_le_inverse_of_positive (ofRat_succ_positive _)
    (ofRat_nat_le (Nat.succ_le_succ ordered))
  upperMonotone := fun _ _ ordered => ofRat_nat_le (Nat.succ_le_succ ordered)
  exhausts := fun value valuePositive => by
    rcases exists_positive_inverse_below valuePositive with ⟨below, belowPositive, belowBound⟩
    rcases exists_nat_upper value with ⟨above, aboveBound⟩
    refine ⟨below + above, lt_of_le_of_lt (inverse_le_inverse_of_positive belowPositive
        (ofRat_nat_le (Nat.le_succ_of_le (Nat.le_add_right below above)))) belowBound,
      le_trans aboveBound (ofRat_nat_le (Nat.le_succ_of_le (Nat.le_add_left _ _)))⟩

end Exhaustion

/-! ### Change of variables -/

/-- An increasing bijection from an open interval onto an exhausted one, with a
continuous nonnegative derivative and an inverse on the range. -/
public structure IncreasingSubstitution (domain range : Set Carrier) where
  function : Carrier → Carrier
  derivative : Carrier → Carrier
  inverse : Carrier → Carrier
  functionMeasurable : MeasurableMap borel borel function
  derivativeMeasurable : MeasurableMap borel borel derivative
  domainConvex : ∀ first middle second, domain first → domain second →
    le first middle → le middle second → domain middle
  domainOpen : ∀ value, domain value →
    ∃ below above, domain below ∧ domain above ∧ lt below value ∧ lt value above
  rangeExhaustion : Exhaustion range
  maps : ∀ value, domain value → range (function value)
  inverseIn : ∀ value, range value → domain (inverse value)
  rightInverse : ∀ value, range value → function (inverse value) = value
  increasing : ∀ first second, domain first → domain second → lt first second →
    lt (function first) (function second)
  differentiable : ∀ value, domain value → HasDerivative function value (derivative value)
  continuous : ∀ value, domain value →
    Approaches (fun displacement => derivative (add value displacement)) (derivative value)
  nonnegative : ∀ value, domain value → le zero (derivative value)

namespace IncreasingSubstitution

variable {domain range : Set Carrier} (substitution : IncreasingSubstitution domain range)

private theorem monotone {first second : Carrier} (firstIn : domain first)
    (secondIn : domain second) (ordered : le first second) :
    le (substitution.function first) (substitution.function second) := by
  by_cases back : le second first
  · rw [le_antisymm ordered back]
    exact le_refl _
  · exact le_of_lt (substitution.increasing first second firstIn secondIn (lt_of_not_le back))

/-- Volume on the domain, weighted by the derivative and pushed through the
function, is volume on the range. The preimage of a half-open interval with
ends in the range is the segment between their inverses, where `primitive_eq`
measures the weight, and `Exhaustion.measure_ext` does the rest. -/
public theorem map_withDensity :
    ((volume.restrict domain).withDensity
        (fun value => ENNReal.ofReal (substitution.derivative value))).map
      substitution.function substitution.functionMeasurable = volume.restrict range := by
  have rangeMeasurable := substitution.rangeExhaustion.measurable
  -- The pushed measure of a set is the weight over the domain part of its preimage.
  have pushed : ∀ {set}, borel.Measurable set →
      ((volume.restrict domain).withDensity
          (fun value => ENNReal.ofReal (substitution.derivative value))).map
        substitution.function substitution.functionMeasurable set =
      lintegral (volume.restrict (Set.inter (Set.preimage substitution.function set) domain))
        (fun value => ENNReal.ofReal (substitution.derivative value)) := fun setMeasurable => by
    rw [Measure.map_apply _ _ _ setMeasurable,
      Measure.withDensity_apply _ _ (substitution.functionMeasurable setMeasurable),
      Measure.restrict_restrict _ _ (substitution.functionMeasurable setMeasurable)]
  apply substitution.rangeExhaustion.measure_ext
  · have empty : Set.inter (Set.preimage substitution.function (Set.complement range)) domain =
        Set.empty :=
      Set.ext fun value => ⟨fun member => member.1 (substitution.maps value member.2), False.elim⟩
    rw [pushed (borel.complement rangeMeasurable), empty, Measure.restrict_empty,
      lintegral_zero_measure]
  · have empty : Set.inter (Set.complement range) range = Set.empty :=
      Set.ext fun _ => ⟨fun member => member.1 member.2, False.elim⟩
    rw [Measure.restrict_apply _ _ (borel.complement rangeMeasurable), empty, volume.empty_apply]
  · intro lower upper
    rw [Measure.restrict_apply _ _ (measurable_ioc lower upper)]
    refine ENNReal.finite_of_le (volume.mono (fun _ member => member.1)) ?_
    rw [volume_ioc]
    exact ENNReal.ofReal_finite _
  intro lower upper lowerIn upperIn ordered
  have lowerInverse := substitution.inverseIn lower lowerIn
  have upperInverse := substitution.inverseIn upper upperIn
  have lowerRight := substitution.rightInverse lower lowerIn
  have upperRight := substitution.rightInverse upper upperIn
  have preimage : Set.inter (Set.preimage substitution.function (Ioc lower upper)) domain =
      Ioc (substitution.inverse lower) (substitution.inverse upper) := by
    apply Set.ext
    intro value
    change (lt lower (substitution.function value) ∧ le (substitution.function value) upper) ∧
      domain value ↔ lt (substitution.inverse lower) value ∧ le value (substitution.inverse upper)
    constructor
    · rintro ⟨⟨lowerValue, valueUpper⟩, valueIn⟩
      constructor
      · by_cases back : le value (substitution.inverse lower)
        · have below := substitution.monotone valueIn lowerInverse back
          rw [lowerRight] at below
          exact absurd below (not_le_of_lt lowerValue)
        · exact lt_of_not_le back
      · by_cases within : le value (substitution.inverse upper)
        · exact within
        · have above := substitution.increasing _ _ upperInverse valueIn (lt_of_not_le within)
          rw [upperRight] at above
          exact absurd valueUpper (not_le_of_lt above)
    · rintro ⟨lowerValue, valueUpper⟩
      have valueIn := substitution.domainConvex _ value _ lowerInverse upperInverse
        (le_of_lt lowerValue) valueUpper
      have above := substitution.increasing _ _ lowerInverse valueIn lowerValue
      have below := substitution.monotone valueIn upperInverse valueUpper
      rw [lowerRight] at above
      rw [upperRight] at below
      exact ⟨⟨above, below⟩, valueIn⟩
  have inside : Set.inter (Ioc lower upper) range = Ioc lower upper :=
    Set.ext fun value => ⟨fun member => member.1, fun member => ⟨member,
      substitution.rangeExhaustion.convex _ value _ lowerIn upperIn (le_of_lt member.1)
        member.2⟩⟩
  have inverseOrdered : le (substitution.inverse lower) (substitution.inverse upper) := by
    by_cases included : le (substitution.inverse lower) (substitution.inverse upper)
    · exact included
    · have reversed := substitution.increasing _ _ upperInverse lowerInverse
        (lt_of_not_le included)
      rw [lowerRight, upperRight] at reversed
      exact absurd ordered (not_le_of_lt reversed)
  obtain ⟨below, _, belowIn, _, belowLower, _⟩ :=
    substitution.domainOpen _ lowerInverse
  obtain ⟨_, above, _, aboveIn, _, upperAbove⟩ :=
    substitution.domainOpen _ upperInverse
  have within : ∀ value, lt below value → lt value above → domain value :=
    fun value belowValue valueAbove => substitution.domainConvex _ value _ belowIn aboveIn
      (le_of_lt belowValue) (le_of_lt valueAbove)
  have fundamental := primitive_eq substitution.derivativeMeasurable
    (fun value belowValue valueAbove =>
      substitution.differentiable value (within value belowValue valueAbove))
    (fun value belowValue valueAbove =>
      substitution.continuous value (within value belowValue valueAbove))
    (fun value belowValue valueAbove =>
      substitution.nonnegative value (within value belowValue valueAbove))
    belowLower inverseOrdered upperAbove
  rw [lowerRight, upperRight] at fundamental
  rw [pushed (measurable_ioc lower upper), preimage,
    Measure.restrict_apply _ _ (measurable_ioc lower upper), inside, volume_ioc]
  exact fundamental

/-- The change of variables as integrals: an integrand read through the
function and weighted by its derivative integrates over the domain to its
integral over the range. -/
public theorem lintegral_eq {integrand : Carrier → ENNReal}
    (measurable : ENNRealMeasurable borel integrand) :
    lintegral (volume.restrict domain)
        (fun value => ENNReal.mul (ENNReal.ofReal (substitution.derivative value))
          (integrand (substitution.function value))) =
      lintegral (volume.restrict range) integrand := by
  rw [← lintegral_withDensity _ (ofReal_measurable.comp substitution.derivativeMeasurable)
      (measurable.comp substitution.functionMeasurable),
    ← lintegral_map _ _ substitution.functionMeasurable measurable, substitution.map_withDensity]

end IncreasingSubstitution

end

end Problib.Analysis.Real
