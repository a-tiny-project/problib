module

public import Problib.Analysis.Pi
public import Problib.Analysis.Real.Composition
public import Problib.Analysis.Real.GeometricSeries
public import Problib.Analysis.Real.MeanValue
public import Problib.Analysis.RealPower.Integral
public import Problib.Analysis.Real.Dominated
public import Problib.Measure.Integral.Real.Nonnegative
import Problib.Measure.Real.IntervalIntegral
import Problib.Measure.Integral.Density.Basic
import Problib.Measure.Additive.Continuity
import Problib.Real.Grind

/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot, Sébastien Gouëzel

The ordered interval partition follows Logarithm/Interval.lean, which adapts
integral_add_adjacent_intervals from Mathlib/MeasureTheory/Integral/
IntervalIntegral/Basic.lean at commit 15fe1e4eb92a37c66db923a0fa96596d7b504a35.
No Mathlib import is used.
-/

/-! Rational geometric expansions for the arctangent integral.

Reciprocal rectangles give the derivative of the positive-ray arctangent
integral. The chain rule and the zero-derivative theorem show that reciprocal
arguments complement each other. Continuity from below then identifies the
half-line mass in the definition of pi with twice the unit-interval mass.

On the unit interval, `(1 - t*t) / 2` lies between zero and one half. The first
`count` terms of its geometric expansion approximate `1 / (1 + t*t)` with
uniform error at most `2^-count`. Horner coefficients stay rational, and the
power-integral theorem integrates each even monomial. The signed integral's
absolute bound transfers the pointwise remainder to the rational average.
All new definitions operate on rationals, lists and natural numbers.
-/

set_option autoImplicit false

namespace Problib.Analysis.Arctangent

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real

local notation "K(" t ")" => inverse (add one (mul t t))
local notation "J(" a "," b ")" =>
  lintegral (volume.restrict (Ioc a b)) (fun t => ENNReal.ofReal (K(t)))
local notation "A(" x ")" => ENNReal.toReal (J(zero, x))

private theorem denominator_positive (x : Carrier) : lt zero (add one (mul x x)) := by
  have square := mul_self_nonnegative x
  real_grind

public theorem kernel_positive (x : Carrier) : lt zero (K(x)) :=
  inverse_of_positive_positive (denominator_positive x)

public theorem kernel_le_one (x : Carrier) : le (K(x)) one := by
  have above : le one (add one (mul x x)) := by
    have square := mul_self_nonnegative x
    real_grind
  simpa only [inverse_one] using inverse_le_inverse_of_positive one_positive above

public theorem kernel_antitone {x y : Carrier} (nonnegative : le zero x)
    (ordered : le x y) : le (K(y)) (K(x)) := by
  have yNonnegative := le_trans nonnegative ordered
  have square := le_trans (mul_le_mul_nonnegative_right ordered nonnegative)
    (mul_le_mul_nonnegative_left ordered yNonnegative)
  exact inverse_le_inverse_of_positive (denominator_positive x)
    (add_le_add_left_iff.mpr square)

public theorem interval_upper (a b : Carrier) :
    ENNReal.le (J(a, b)) (ENNReal.ofReal (sub b a)) := by
  have bound := lintegral_mono (volume.restrict (Ioc a b))
    (fun x => ENNReal.ofReal_monotone (kernel_le_one x))
  rw [lintegral_const, Measure.restrict_apply_univ, volume_ioc,
    ENNReal.ofReal_one, ENNReal.one_mul] at bound
  exact bound

public theorem interval_finite (a b : Carrier) : ENNReal.Finite (J(a, b)) :=
  ENNReal.finite_of_le (interval_upper a b) (ENNReal.ofReal_finite _)

public theorem interval_reverse (a b : Carrier) (ordered : le b a) :
    J(a, b) = ENNReal.zero := by
  have empty : Ioc a b = Set.empty := by
    apply Set.ext
    intro t
    exact ⟨fun h => h.1.2 (le_trans h.2 ordered), False.elim⟩
  rw [empty, Measure.restrict_empty, lintegral_zero_measure]

public theorem interval_add (a b c : Carrier) (hab : le a b) (hbc : le b c) :
    J(a, c) = ENNReal.add (J(a, b)) (J(b, c)) := by
  classical
  let q := fun t => ENNReal.ofReal (inverse (add one (mul t t)))
  have split : ∀ t, ennrealIndicator (Ioc a c) q t =
      ENNReal.add (ennrealIndicator (Ioc a b) q t) (ennrealIndicator (Ioc b c) q t) := by
    intro t
    by_cases ht : Ioc a c t
    · by_cases htb : le t b
      · have first : Ioc a b t := ⟨ht.1, htb⟩
        have second : ¬Ioc b c t := fun h => h.1.2 htb
        simp only [ennrealIndicator, ennrealPiecewise, ite_eq_left ht, ite_eq_left first,
          ite_eq_right second, ENNReal.add_zero]
      · have first : ¬Ioc a b t := fun h => htb h.2
        have second : Ioc b c t := ⟨not_le_iff_lt.mp htb, ht.2⟩
        simp only [ennrealIndicator, ennrealPiecewise, ite_eq_left ht, ite_eq_right first,
          ite_eq_left second, ENNReal.zero_add]
    · have first : ¬Ioc a b t := fun h => ht ⟨h.1, le_trans h.2 hbc⟩
      have second : ¬Ioc b c t := by
        intro h
        exact ht ⟨⟨le_trans hab h.1.1, fun reverse => h.1.2 (le_trans reverse hab)⟩, h.2⟩
      simp only [ennrealIndicator, ennrealPiecewise, ite_eq_right ht, ite_eq_right first,
        ite_eq_right second, ENNReal.zero_add]
  calc
    J(a, c) = lintegral volume (ennrealIndicator (Ioc a c) q) :=
      (lintegral_indicator volume _ (measurable_ioc a c) q).symm
    _ = lintegral volume (fun t => ENNReal.add
        (ennrealIndicator (Ioc a b) q t) (ennrealIndicator (Ioc b c) q t)) :=
      lintegral_congr volume split
    _ = ENNReal.add (J(a, b)) (J(b, c)) := by
      rw [lintegral_add volume
        (ENNRealMeasurable.indicator (measurable_ioc a b) Gaussian.rational_measurable)
        (ENNRealMeasurable.indicator (measurable_ioc b c) Gaussian.rational_measurable),
        lintegral_indicator volume _ (measurable_ioc a b),
        lintegral_indicator volume _ (measurable_ioc b c)]


private theorem real_add {a b : ENNReal} (ha : ENNReal.Finite a) (hb : ENNReal.Finite b) :
    ENNReal.toReal (ENNReal.add a b) = add (ENNReal.toReal a) (ENNReal.toReal b) := by
  rcases ENNReal.exists_finite_of_finite ha with ⟨a, rfl⟩
  rcases ENNReal.exists_finite_of_finite hb with ⟨b, rfl⟩
  rfl

public theorem arctangent_difference {a b : Carrier} (nonnegative : le zero a)
    (ordered : le a b) : A(b) = add (A(a)) (ENNReal.toReal (J(a, b))) := by
  rw [interval_add zero a b nonnegative ordered,
    real_add (interval_finite zero a) (interval_finite a b)]

public theorem arctangent_zero : A(zero) = zero := by
  rw [interval_reverse zero zero (le_refl zero), ENNReal.toReal_zero]

public theorem arctangent_bounds {x : Carrier} (nonnegative : le zero x) :
    le zero (A(x)) ∧ le (A(x)) x := by
  refine ⟨ENNReal.toReal_nonnegative _, ?_⟩
  have upper := interval_upper zero x
  rw [sub_zero] at upper
  exact (ENNReal.le_ofReal_iff_toReal_le (interval_finite zero x) nonnegative).mp upper

public theorem increment_bounds {a b : Carrier} (nonnegative : le zero a)
    (ordered : le a b) :
    le (mul (sub b a) (K(b))) (sub (A(b)) (A(a))) ∧
      le (sub (A(b)) (A(a))) (mul (sub b a) (K(a))) := by
  have gap : le zero (sub b a) := additive.orderedGroup.sub_nonnegative_of_le ordered
  have lower := @lintegral_mono_ae _ borel (volume.restrict (Ioc a b))
    (fun _ => ENNReal.ofReal (K(b))) (fun t => ENNReal.ofReal (K(t)))
    ((volume.ae_restrict_mem (measurable_ioc a b)).mono (fun t ht =>
      ENNReal.ofReal_monotone (kernel_antitone (le_trans nonnegative ht.1.1) ht.2)))
  have upper := @lintegral_mono_ae _ borel (volume.restrict (Ioc a b))
    (fun t => ENNReal.ofReal (K(t))) (fun _ => ENNReal.ofReal (K(a)))
    ((volume.ae_restrict_mem (measurable_ioc a b)).mono (fun t ht =>
      ENNReal.ofReal_monotone (kernel_antitone nonnegative ht.1.1)))
  rw [lintegral_const, Measure.restrict_apply_univ, volume_ioc,
    ← ofReal_mul (kernel_positive b).1 gap, mul_comm (K(b))] at lower
  rw [lintegral_const, Measure.restrict_apply_univ, volume_ioc,
    ← ofReal_mul (kernel_positive a).1 gap, mul_comm (K(a))] at upper
  rw [arctangent_difference nonnegative ordered, add_sub_self]
  exact ⟨(ENNReal.ofReal_le_iff_le_toReal (interval_finite a b)).mp lower,
    (ENNReal.le_ofReal_iff_toReal_le (interval_finite a b)
      (mul_nonnegative gap (kernel_positive a).1)).mp upper⟩

public theorem hasDerivative_arctangent {point : Carrier} (positive : lt zero point) :
    HasDerivative (fun x => A(x)) point (K(point)) := by
  have shifted := approaches_add (approaches_const point) approaches_displacement
  rw [add_zero] at shifted
  have denominator := approaches_add (approaches_const one) (approaches_mul shifted shifted)
  have kernelLimit := approaches_inverse denominator
    (positive_iff_nonnegative_and_nonzero.mp (denominator_positive point)).2
  refine approaches_of_closer positive (fun displacement nonzero inside => ?_) kernelLimit
  apply abs_sub_le_of_between
  have shiftedPositive : lt zero (add point displacement) := by
    have below := (abs_lt.mp inside).left
    have shifted := add_lt_add_left point below
    rwa [add_neg] at shifted
  rcases lt_or_lt_of_ne nonzero with negative | positiveStep
  · left
    have ordered : le (add point displacement) point := by
      have shifted := add_le_add_left_iff (shift := point) |>.mpr (le_of_lt negative)
      rwa [add_zero] at shifted
    have bounds := increment_bounds shiftedPositive.1 ordered
    have width : sub point (add point displacement) = neg displacement := by
      real_grind
    rw [width] at bounds
    have flipped : lt zero (neg displacement) := neg_positive_iff.mpr negative
    have flippedNonzero := (positive_iff_nonnegative_and_nonzero.mp flipped).2
    have secantEqual : secant (fun x => A(x)) point displacement =
        div (sub (A(point)) (A(add point displacement))) (neg displacement) := by
      rw [secant, ← neg_sub, div_eq_mul_inverse, div_eq_mul_inverse, inverse_neg, mul_neg, neg_mul]
    rw [secantEqual]
    have lowerBound := div_le_div_right flipped bounds.left
    have upperBound := div_le_div_right flipped bounds.right
    have cancel : ∀ x, div (mul (neg displacement) x) (neg displacement) = x := by
      intro x
      rw [mul_comm, div_eq_mul_inverse, mul_assoc, mul_inverse_cancel flippedNonzero, mul_one]
    rw [cancel] at lowerBound upperBound
    exact ⟨lowerBound, upperBound⟩
  · right
    have ordered : le point (add point displacement) := by
      have shifted := add_le_add_left_iff (shift := point) |>.mpr (le_of_lt positiveStep)
      rwa [add_zero] at shifted
    have bounds := increment_bounds positive.1 ordered
    rw [add_sub_self] at bounds
    have lowerBound := div_le_div_right positiveStep bounds.left
    have upperBound := div_le_div_right positiveStep bounds.right
    have cancel : ∀ x, div (mul displacement x) displacement = x := by
      intro x
      rw [mul_comm, div_eq_mul_inverse, mul_assoc, mul_inverse_cancel nonzero, mul_one]
    rw [cancel] at lowerBound upperBound
    exact ⟨lowerBound, upperBound⟩

/-- Reciprocal arguments complement each other on the positive ray. -/
public theorem arctangent_reciprocal {x : Carrier} (positive : lt zero x) :
    add (A(x)) (A(inverse x)) = mul (selection.ofRat 2) (A(one)) := by
  have flat : ∀ t : Carrier, lt zero t →
      HasDerivative (fun y => add (A(y)) (A(inverse y))) t zero := by
    intro t tPositive
    have nonzero := (positive_iff_nonnegative_and_nonzero.mp tPositive).2
    have reciprocal := hasDerivative_inverse (hasDerivative_identity t) nonzero
    have composed := hasDerivative_comp
      (hasDerivative_arctangent (inverse_of_positive_positive tPositive)) reciprocal
    have derivative := hasDerivative_add (hasDerivative_arctangent tPositive) composed
    have cancels : add (K(t))
        (mul (K(inverse t)) (neg (div one (mul t t)))) = zero := by
      have denominatorNonzero :=
        (positive_iff_nonnegative_and_nonzero.mp (denominator_positive t)).2
      have inverseDenominatorNonzero :=
        (positive_iff_nonnegative_and_nonzero.mp (denominator_positive (inverse t))).2
      real_grind
    rw [cancels] at derivative
    exact derivative
  have same := eq_of_hasDerivative_zero_on
    (lower := zero) (upper := add x (selection.ofRat 2))
    (fun t h _ => flat t h)
    (first := x) (second := one) positive
    (by real_grind) one_positive (by real_grind)
  rw [inverse_one] at same
  calc
    add (A(x)) (A(inverse x)) = add (A(one)) (A(one)) := same
    _ = mul (selection.ofRat 2) (A(one)) := by real_grind

private theorem half_iSup : Gaussian.rationalHalf =
    ENNReal.iSup (fun n : Nat => J(zero, selection.ofRat (n : Rat))) := by
  let regions := fun n : Nat => Ioc zero (selection.ofRat (n : Rat))
  have union : Set.iUnion regions = Ioi zero := by
    apply Set.ext
    intro x
    constructor
    · rintro ⟨n, member⟩
      exact member.1
    · intro positive
      rcases exists_nat_strict_upper x with ⟨n, above⟩
      exact ⟨n, positive, above.1⟩
  have monotone : Set.MonotoneFamily regions := by
    intro n m ordered x member
    refine ⟨member.1, le_trans member.2 ?_⟩
    exact (ofRat_le_iff _ _).mpr (Rat.natCast_le_natCast.mpr ordered)
  have continuous := (volume.withDensity (fun t => ENNReal.ofReal (K(t)))).continuity_from_below
    regions (fun n => measurable_ioc zero (selection.ofRat (n : Rat))) monotone
  rw [union, Measure.withDensity_apply volume _ (measurable_ioi zero)] at continuous
  simpa only [Gaussian.rationalHalf, regions,
    Measure.withDensity_apply volume _ (measurable_ioc _ _)] using continuous

/-- The defining half-line mass is twice its unit-interval arctangent mass. -/
public theorem rationalHalf_eq_twice :
    ENNReal.toReal Gaussian.rationalHalf = mul (selection.ofRat 2) (A(one)) := by
  have nonnegative : le zero (mul (selection.ofRat 2) (A(one))) :=
    mul_nonnegative ofRat_two_positive.1 (arctangent_bounds one_positive.1).1
  apply le_antisymm
  · apply (ENNReal.le_ofReal_iff_toReal_le Gaussian.rational_finite nonnegative).mp
    rw [half_iSup]
    apply ENNReal.iSup_le
    intro n
    have below : le (A(selection.ofRat (n : Rat)))
        (mul (selection.ofRat 2) (A(one))) := by
      cases n with
      | zero =>
        rw [show ((0 : Nat) : Rat) = 0 from rfl, ofRat_zero, arctangent_zero]
        exact nonnegative
      | succ n =>
        have identity := arctangent_reciprocal (ofRat_succ_positive n)
        have other := ENNReal.toReal_nonnegative (J(zero, inverse (selection.ofRat ((n + 1 : Nat) : Rat))))
        real_grind
    have projected := ENNReal.ofReal_monotone below
    rw [ENNReal.ofReal_toReal (interval_finite zero (selection.ofRat (n : Rat)))] at projected
    exact projected
  · apply le_of_le_add_positive
    intro error errorPositive
    rcases exists_nat_strict_upper (inverse error) with ⟨n, above⟩
    have nPositive := lt_trans (inverse_of_positive_positive errorPositive) above
    have inverseSmall := inverse_lt_inverse_of_positive
      (inverse_of_positive_positive errorPositive) nPositive above
    rw [inverse_inverse] at inverseSmall
    have identity := arctangent_reciprocal nPositive
    have tiny := (arctangent_bounds (inverse_of_positive_positive nPositive).1).2
    have lower : le (A(selection.ofRat (n : Rat)))
        (ENNReal.toReal Gaussian.rationalHalf) := by
      apply (ENNReal.toReal_le_toReal_iff
        (interval_finite zero (selection.ofRat (n : Rat))) Gaussian.rational_finite).mpr
      rw [half_iSup]
      exact ENNReal.le_iSup (fun k => J(zero, selection.ofRat (k : Rat))) n
    real_grind

/-- The integral pi is four times the arctangent integral on the unit interval. -/
public theorem pi_eq_four : pi = mul (selection.ofRat 4) (A(one)) := by
  rw [pi, rationalHalf_eq_twice]
  real_grind

/-! ### Finite rational polynomials -/

/-- Multiply coefficients in ascending order by `(1 - z) / 2`.
The carry is the preceding coefficient, with zero at the first position. -/
@[expose] public def coefficientStep (previous : Rat) : List Rat → List Rat
  | [] => [-previous / 2]
  | coefficient :: rest => (coefficient - previous) / 2 :: coefficientStep coefficient rest

/-- Add a constant to an ascending coefficient list. -/
@[expose] public def addConstant (constant : Rat) : List Rat → List Rat
  | [] => [constant]
  | coefficient :: rest => (coefficient + constant) :: rest

/-- The first `count` terms of `1/2 ∑ ((1 - z)/2)^k`, in Horner form. -/
@[expose] public def unitPolynomial : Nat → List Rat
  | 0 => []
  | count + 1 => addConstant (1 / 2) (coefficientStep 0 (unitPolynomial count))

/-- Integrate the even monomials of a rational polynomial on `[0, 1]`. -/
@[expose] public def unitAverage (offset : Nat) : List Rat → Rat
  | [] => 0
  | coefficient :: rest => coefficient / ((2 * offset + 1 : Nat) : Rat) +
      unitAverage (offset + 1) rest

/-- A computable approximation to the arctangent at one. -/
@[expose] public def unitApproximation (count : Nat) : Rat :=
  unitAverage 0 (unitPolynomial count)

local notation "E(" coefficients "," t ")" =>
  List.foldr (fun coefficient total =>
    add (selection.ofRat coefficient) (mul (mul t t) total)) zero coefficients

private theorem evaluate_step (previous : Rat) (coefficients : List Rat) (t : Carrier) :
    E(coefficientStep previous coefficients, t) =
      div (sub (mul (sub one (mul t t)) (E(coefficients, t))) (selection.ofRat previous))
        (selection.ofRat 2) := by
  induction coefficients generalizing previous with
  | nil =>
      simp only [coefficientStep, List.foldr_cons, List.foldr_nil, ofRat_div, ofRat_neg]
      real_grind
  | cons coefficient rest induction =>
      simp only [coefficientStep, List.foldr_cons]
      rw [induction, ofRat_div, ofRat_sub]
      real_grind

private theorem evaluate_addConstant (constant : Rat) (coefficients : List Rat) (t : Carrier) :
    E(addConstant constant coefficients, t) = add (selection.ofRat constant) (E(coefficients, t)) := by
  cases coefficients with
  | nil => simp only [addConstant, List.foldr_cons, List.foldr_nil, mul_zero, add_zero]
  | cons coefficient rest =>
      simp only [addConstant, List.foldr_cons, ofRat_add]
      real_grind

private theorem evaluate_polynomial_succ (count : Nat) (t : Carrier) :
    E(unitPolynomial (count + 1), t) = add (selection.ofRat (1 / 2))
      (mul (div (sub one (mul t t)) (selection.ofRat 2)) (E(unitPolynomial count, t))) := by
  rw [unitPolynomial, evaluate_addConstant, evaluate_step, ofRat_zero, sub_zero]
  real_grind

private theorem unit_probability : Measure.IsProbability (volume.restrict (Ioc zero one)) := by
  constructor
  rw [Measure.restrict_apply_univ, volume_ioc, sub_zero, ENNReal.ofReal_one]

private theorem square_power (t : Carrier) (count : Nat) :
    SignedSeries.power (mul t t) count = SignedSeries.power t (2 * count) := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [Nat.mul_succ, SignedSeries.power_add, SignedSeries.power_succ, induction]
      simp only [SignedSeries.power_succ, SignedSeries.power_zero, mul_one]
      real_grind

private theorem power_measurable (count : Nat) :
    MeasurableMap borel borel (fun t => SignedSeries.power (mul t t) count) := by
  induction count with
  | zero => exact MeasurableMap.constant borel borel one
  | succ count induction =>
      exact measurable_mul
        (measurable_mul (MeasurableMap.identity borel) (MeasurableMap.identity borel)) induction

private theorem monomial_integral (count : Nat) :
    HasRealIntegral (volume.restrict (Ioc zero one))
      (fun t => SignedSeries.power (mul t t) count)
      (selection.ofRat (1 / ((2 * count + 1 : Nat) : Rat))) := by
  have exponentPositive : lt zero (selection.ofRat ((2 * count + 1 : Nat) : Rat)) :=
    ofRat_succ_positive (2 * count)
  have valueNonnegative : le zero (selection.ofRat (1 / ((2 * count + 1 : Nat) : Rat))) := by
    rw [ofRat_div, ofRat_one, div_eq_mul_inverse, one_mul]
    exact (inverse_of_positive_positive exponentPositive).1
  apply HasRealIntegral.of_lintegral_ofReal (power_measurable count)
    (fun t => SignedSeries.power_nonnegative (mul_self_nonnegative t) count) valueNonnegative
  have evaluated := rpow_unit_integral _ exponentPositive
  have exponent : sub (selection.ofRat ((2 * count + 1 : Nat) : Rat)) one =
      selection.ofRat ((2 * count : Nat) : Rat) := by
    rw [Rat.natCast_add, ofRat_add, show ((1 : Nat) : Rat) = 1 from rfl, ofRat_one]
    real_grind
  rw [exponent] at evaluated
  rw [ofRat_div, ofRat_one, div_eq_mul_inverse, one_mul]
  refine (lintegral_congr_ae ((volume.ae_restrict_mem (measurable_ioc zero one)).mono
    (fun t member => ?_))).trans evaluated
  rw [square_power, rpow_nat member.1.1]

private theorem polynomial_integral (coefficients : List Rat) (offset : Nat) :
    HasRealIntegral (volume.restrict (Ioc zero one))
      (fun t => mul (SignedSeries.power (mul t t) offset) (E(coefficients, t)))
      (selection.ofRat (unitAverage offset coefficients)) := by
  induction coefficients generalizing offset with
  | nil =>
      simpa only [unitAverage, ofRat_zero, List.foldr_nil, mul_zero] using
        HasRealIntegral.const unit_probability zero
  | cons coefficient rest induction =>
      have head := (monomial_integral offset).smul (selection.ofRat coefficient)
      have tail := induction (offset + 1)
      have combined := head.add tail
      have value : add
          (mul (selection.ofRat coefficient) (selection.ofRat (1 / ((2 * offset + 1 : Nat) : Rat))))
          (selection.ofRat (unitAverage (offset + 1) rest)) =
          selection.ofRat (unitAverage offset (coefficient :: rest)) := by
        rw [unitAverage, ofRat_add, ofRat_div, ofRat_div, ofRat_one]
        real_grind
      rw [value] at combined
      exact combined.congr (fun t => by
        simp only [List.foldr_cons, SignedSeries.power_succ]
        real_grind)

private theorem polynomial_remainder (count : Nat) (t : Carrier) :
    sub (K(t)) (E(unitPolynomial count, t)) =
      mul (K(t)) (SignedSeries.power (div (sub one (mul t t)) (selection.ofRat 2)) count) := by
  induction count with
  | zero => simp only [unitPolynomial, List.foldr_nil, sub_zero, SignedSeries.power_zero, mul_one]
  | succ count induction =>
      rw [evaluate_polynomial_succ, SignedSeries.power_succ]
      have denominatorNonzero :=
        (positive_iff_nonnegative_and_nonzero.mp (denominator_positive t)).2
      rw [ofRat_div, ofRat_one]
      real_grind

private theorem half_power (count : Nat) :
    SignedSeries.power (selection.ofRat (1 / 2)) count = selection.ofRat ((1 / 2 : Rat) ^ count) := by
  induction count with
  | zero => rw [Rat.pow_zero, ofRat_one]; rfl
  | succ count induction =>
      rw [SignedSeries.power_succ, induction, Rat.pow_succ, ofRat_mul, mul_comm]

public theorem polynomial_error (count : Nat) {t : Carrier} (nonnegative : le zero t)
    (bounded : le t one) :
    le (abs (sub (K(t)) (E(unitPolynomial count, t))))
      (selection.ofRat ((1 / 2 : Rat) ^ count)) := by
  have squareNonnegative := mul_self_nonnegative t
  have squareBound : le (mul t t) one := by
    have raised := mul_le_mul_nonnegative_right bounded nonnegative
    real_grind
  have ratioNonnegative : le zero (div (sub one (mul t t)) (selection.ofRat 2)) := by
    have numerator : le zero (sub one (mul t t)) := by real_grind
    exact div_nonnegative numerator ofRat_two_positive.1
  have ratioBound : le (div (sub one (mul t t)) (selection.ofRat 2))
      (selection.ofRat (1 / 2)) := by
    rw [ofRat_div, ofRat_one]
    exact div_le_div_right ofRat_two_positive (by real_grind)
  have powerBound : ∀ n, le
      (SignedSeries.power (div (sub one (mul t t)) (selection.ofRat 2)) n)
      (SignedSeries.power (selection.ofRat (1 / 2)) n) := by
    intro n
    induction n with
    | zero => exact le_refl one
    | succ n induction =>
        rw [SignedSeries.power_succ, SignedSeries.power_succ]
        exact le_trans
          (mul_le_mul_nonnegative_right ratioBound
            (SignedSeries.power_nonnegative ratioNonnegative n))
          (mul_le_mul_nonnegative_left induction (by
            rw [ofRat_div, ofRat_one, div_eq_mul_inverse, one_mul]
            exact (inverse_of_positive_positive ofRat_two_positive).1))
  rw [polynomial_remainder, abs_of_nonnegative
    (mul_nonnegative (kernel_positive t).1 (SignedSeries.power_nonnegative ratioNonnegative count))]
  have removeKernel := mul_le_mul_nonnegative_right (kernel_le_one t)
    (SignedSeries.power_nonnegative ratioNonnegative count)
  rw [one_mul] at removeKernel
  exact le_trans removeKernel (by simpa only [half_power] using powerBound count)

/-- The rational approximation is within `2^-count` of the unit arctangent mass. -/
public theorem unitApproximation_error (count : Nat) :
    le (abs (sub (A(one)) (selection.ofRat (unitApproximation count))))
      (selection.ofRat ((1 / 2 : Rat) ^ count)) := by
  have kernelIntegral : HasRealIntegral (volume.restrict (Ioc zero one)) (fun t => K(t)) (A(one)) :=
    HasRealIntegral.of_lintegral_ofReal
      (MeasurableMap.comp Real.inverse_measurable
        (measurable_add (MeasurableMap.constant borel borel one)
          (measurable_mul (MeasurableMap.identity borel) (MeasurableMap.identity borel))))
      (fun t => (kernel_positive t).1) (ENNReal.toReal_nonnegative _)
      (ENNReal.ofReal_toReal (interval_finite zero one)).symm
  have polynomialIntegral : HasRealIntegral (volume.restrict (Ioc zero one))
      (fun t => E(unitPolynomial count, t)) (selection.ofRat (unitApproximation count)) := by
    simpa only [SignedSeries.power_zero, one_mul, unitApproximation] using
      polynomial_integral (unitPolynomial count) 0
  have errorNonnegative : le zero (selection.ofRat ((1 / 2 : Rat) ^ count)) := by
    rw [← half_power]
    exact SignedSeries.power_nonnegative (by
      rw [ofRat_div, ofRat_one, div_eq_mul_inverse, one_mul]
      exact (inverse_of_positive_positive ofRat_two_positive).1) count
  exact (kernelIntegral.sub polynomialIntegral).abs_le_of_ae_bounded unit_probability
    errorNonnegative ((volume.ae_restrict_mem (measurable_ioc zero one)).mono
      (fun t member => polynomial_error count member.1.1 member.2))

end Problib.Analysis.Arctangent
