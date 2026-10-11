module

public import Problib.Analysis.Trigonometric.Derivative
public import Problib.Analysis.Arctangent
import Problib.Real.Grind

/-! The Gaussian π is the circle constant of sine and cosine.

Problib defines π through the Gaussian integral, and `pi_eq_four` writes it
as four times the arctangent integral `A(1) = ∫₀¹ 1 / (1 + t²) dt`. Along the
arctangent, `ψ(x) = sin (A x) - x · cos (A x)` satisfies `ψ' = K x ψ` with
`K = 1 / (1 + x²)`, so `ψ² · K` has zero derivative on the positive ray. It
tends to zero at zero, where `A x ≤ x` and sine is continuous, so `ψ` vanishes
and `sin (A 1) = cos (A 1)`. Pythagoras then gives `cos (π / 2) = 0` and
`sin (π / 2) = 1` with no sign argument, and the addition formulas give the
period `2π`.
-/

set_option autoImplicit false

namespace Problib.Analysis

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real
open Problib.Analysis.Real.SignedSeries

local notation "K(" t ")" => inverse (add one (mul t t))
local notation "A(" x ")" =>
  ENNReal.toReal (lintegral (volume.restrict (Ioc zero x)) (fun t => ENNReal.ofReal (K(t))))

noncomputable section

/-- The gap between sine and the tangent line along the arctangent. -/
private def tilt (point : Carrier) : Carrier :=
  sub (sin (A(point))) (mul point (cos (A(point))))

/-- The tilt's energy, `ψ² / (1 + x²)`. -/
private def tiltEnergy (point : Carrier) : Carrier :=
  mul (mul (tilt point) (tilt point)) (K(point))

private theorem denominator_positive (point : Carrier) :
    lt zero (add one (mul point point)) := by
  have square := mul_self_nonnegative point
  real_grind

private theorem denominator_nonzero (point : Carrier) : add one (mul point point) ≠ zero :=
  (positive_iff_nonnegative_and_nonzero.mp (denominator_positive point)).2

private theorem hasDerivative_tiltEnergy {point : Carrier} (positive : lt zero point) :
    HasDerivative tiltEnergy point zero := by
  have arctangent := Arctangent.hasDerivative_arctangent positive
  have sine := hasDerivative_comp (inner := fun value => A(value))
    (hasDerivative_sin (A(point))) arctangent
  have cosine := hasDerivative_comp (inner := fun value => A(value))
    (hasDerivative_cos (A(point))) arctangent
  have slope := hasDerivative_sub sine
    (hasDerivative_mul (hasDerivative_identity point) cosine)
  have denominator := hasDerivative_add (first := fun _ => one)
    (second := fun value => mul value value) (hasDerivative_const one point)
    (hasDerivative_mul (hasDerivative_identity point) (hasDerivative_identity point))
  have reciprocal := hasDerivative_inverse denominator (denominator_nonzero point)
  have energy := hasDerivative_mul (hasDerivative_mul slope slope) reciprocal
  have transport : ∀ derivative, HasDerivative tiltEnergy point derivative →
      derivative = zero → HasDerivative tiltEnergy point zero :=
    fun _ differentiable vanishes => vanishes ▸ differentiable
  refine transport _ energy ?_
  have nonzero := denominator_nonzero point
  generalize sin (A(point)) = sine at *
  generalize cos (A(point)) = cosine at *
  real_grind

private theorem tiltEnergy_eq {point : Carrier} (positive : lt zero point) :
    tiltEnergy point = tiltEnergy one :=
  eq_of_hasDerivative_zero_on (lower := zero) (upper := add (add point one) one)
    (fun _ inside _ => hasDerivative_tiltEnergy inside) positive (by real_grind)
    one_positive (by
      have nonnegative := positive.1
      real_grind)

private theorem tilt_small {tolerance : Carrier} (positive : lt zero tolerance) :
    ∃ point, lt zero point ∧ lt (abs (tilt point)) tolerance := by
  rcases sin_continuous zero (half tolerance) (half_positive positive) with
    ⟨radius, radiusPositive, close⟩
  rcases small_positive (half_positive radiusPositive) (half_positive (half_positive positive))
    with ⟨point, pointPositive, belowRadius, belowTolerance⟩
  refine ⟨point, pointPositive, ?_⟩
  have bounds := Arctangent.arctangent_bounds pointPositive.1
  have sineSmall : lt (abs (sin (A(point)))) (half tolerance) := by
    by_cases vanished : A(point) = zero
    · rw [vanished, sin_zero, abs_zero]
      exact half_positive positive
    · have halfRadius := half_positive radiusPositive
      have inside : lt (abs (A(point))) radius := by
        rw [abs_of_nonnegative bounds.1]
        have below := add_half radius
        unfold half at belowRadius halfRadius below
        real_grind
      have near := close (A(point)) vanished inside
      simpa only [zero_add, sin_zero, sub_zero] using near
  have cosineBound := mul_le_mul_nonnegative_left (abs_cos_le_one (A(point))) pointPositive.1
  have triangle := abs_add_le (sin (A(point))) (neg (mul point (cos (A(point)))))
  rw [abs_neg, abs_mul, abs_of_nonnegative pointPositive.1, ← sub_eq_add_neg] at triangle
  unfold tilt
  have halves := add_half tolerance
  have quarters := add_half (half tolerance)
  unfold half at sineSmall belowTolerance halves quarters
  have quarterPositive := half_positive (half_positive positive)
  unfold half at quarterPositive
  rw [mul_one] at cosineBound
  real_grind

private theorem tiltEnergy_one : tiltEnergy one = zero := by
  have kernelPositive : ∀ point : Carrier, lt zero (K(point)) := fun point =>
    inverse_of_positive_positive (denominator_positive point)
  have kernelBelow : ∀ point : Carrier, le (K(point)) one := by
    intro point
    have product : mul (K(point)) (add one (mul point point)) = one :=
      inverse_mul_cancel (denominator_nonzero point)
    have grown := mul_le_mul_nonnegative_left
      (show le one (add one (mul point point)) by
        have square := mul_self_nonnegative point
        real_grind) (kernelPositive point).1
    rw [mul_one, product] at grown
    exact grown
  apply le_antisymm
  · apply le_of_le_add_positive
    intro error errorPositive
    rcases small_positive errorPositive one_positive with
      ⟨tolerance, tolerancePositive, belowError, belowOne⟩
    rcases tilt_small tolerancePositive with ⟨point, pointPositive, small⟩
    rw [← tiltEnergy_eq pointPositive, zero_add]
    unfold tiltEnergy
    have square : mul (tilt point) (tilt point) = mul (abs (tilt point)) (abs (tilt point)) := by
      rw [← abs_mul, abs_of_nonnegative (mul_self_nonnegative _)]
    have shrunk := mul_le_mul_nonnegative_left (kernelBelow point)
      (mul_self_nonnegative (tilt point))
    have contracted := mul_le_mul_nonnegative_left
      (le_trans (le_of_lt small) belowOne) (abs_nonnegative (tilt point))
    rw [mul_one] at shrunk contracted
    rw [← square] at contracted
    exact le_trans shrunk (le_trans contracted (le_trans (le_of_lt small) belowError))
  · exact mul_nonnegative (mul_self_nonnegative _) (kernelPositive one).1

/-- Along the arctangent at one, sine and cosine agree. -/
private theorem sin_eq_cos_quarter : sin (A(one)) = cos (A(one)) := by
  have vanished := tiltEnergy_one
  unfold tiltEnergy at vanished
  have kernelNonzero : K(one) ≠ zero :=
    (positive_iff_nonnegative_and_nonzero.mp
      (inverse_of_positive_positive (denominator_positive one))).2
  have flat : mul (tilt one) (tilt one) = zero :=
    (mul_eq_zero_iff.mp vanished).elim id (fun other => False.elim (kernelNonzero other))
  have zeroTilt : tilt one = zero := (mul_eq_zero_iff.mp flat).elim id id
  unfold tilt at zeroTilt
  real_grind

private theorem half_pi_eq : half pi = add (A(one)) (A(one)) := by
  have scaled : ∀ value : Carrier,
      half (mul (selection.ofRat 4) value) = add value value := by
    intro value
    unfold half two
    real_grind
  rw [Arctangent.pi_eq_four]
  exact scaled _

/-- Cosine vanishes at a quarter turn. -/
public theorem cos_half_pi : cos (half pi) = zero := by
  rw [half_pi_eq, cos_add, sin_eq_cos_quarter, sub_self]

/-- Sine is one at a quarter turn. -/
public theorem sin_half_pi : sin (half pi) = one := by
  have identity := sin_sq_add_cos_sq (A(one))
  rw [half_pi_eq, sin_add]
  rw [sin_eq_cos_quarter] at identity ⊢
  real_grind

private theorem pi_eq_halves : pi = add (half pi) (half pi) := (add_half pi).symm

public theorem sin_pi : sin pi = zero := by
  rw [pi_eq_halves, sin_add, sin_half_pi, cos_half_pi]
  real_grind

public theorem cos_pi : cos pi = neg one := by
  rw [pi_eq_halves, cos_add, sin_half_pi, cos_half_pi]
  real_grind

private theorem two_pi_eq : mul two pi = add pi pi := by
  unfold two
  real_grind

private theorem sin_two_pi : sin (mul two pi) = zero := by
  rw [two_pi_eq, sin_add, sin_pi, cos_pi]
  real_grind

private theorem cos_two_pi : cos (mul two pi) = one := by
  rw [two_pi_eq, cos_add, sin_pi, cos_pi]
  real_grind

/-- Sine has period `2π`. -/
public theorem sin_add_two_pi (point : Carrier) :
    sin (add point (mul two pi)) = sin point := by
  rw [sin_add, sin_two_pi, cos_two_pi]
  real_grind

/-- Cosine has period `2π`. -/
public theorem cos_add_two_pi (point : Carrier) :
    cos (add point (mul two pi)) = cos point := by
  rw [cos_add, sin_two_pi, cos_two_pi]
  real_grind

private theorem turn_add_one (turns : Carrier) :
    mul (mul two pi) (add turns one) = add (mul (mul two pi) turns) (mul two pi) := by
  real_grind

/-- Sine of a whole turn `2πt` has period one in `t`. -/
public theorem sin_turn_add_one (turns : Carrier) :
    sin (mul (mul two pi) (add turns one)) = sin (mul (mul two pi) turns) := by
  rw [turn_add_one, sin_add_two_pi]

/-- Cosine of a whole turn `2πt` has period one in `t`. -/
public theorem cos_turn_add_one (turns : Carrier) :
    cos (mul (mul two pi) (add turns one)) = cos (mul (mul two pi) turns) := by
  rw [turn_add_one, cos_add_two_pi]

/-! ### The least positive zero

On `(0, 2]` the sine series is at least `s - s³/6`: after its first four
terms it adds blocks `s⁴ᵐ⁺⁵/(4m+5)! - s⁴ᵐ⁺⁷/(4m+7)!`, and each is nonnegative
because the factorial terms shrink once the index passes `s`. Since
`A(1) ≤ 1`, the quarter turn `π/2 = 2 A(1)` lies in that interval, and
`cos x = sin (π/2 - x)` is positive below it. -/

private theorem factorialTerm_step_le {base : Carrier} (nonnegative : le zero base)
    {index : Nat} (small : le base (selection.ofRat ((index + 1 : Nat) : Rat))) :
    le (factorialTerm base (index + 1)) (factorialTerm base index) := by
  have positive : lt zero (selection.ofRat ((index + 1 : Nat) : Rat)) := by
    have embedded := (ofRat_lt_iff 0 ((index + 1 : Nat) : Rat)).mpr
      (Rat.natCast_pos.mpr (Nat.succ_pos index))
    rwa [ofRat_zero] at embedded
  have nonzero := (positive_iff_nonnegative_and_nonzero.mp positive).2
  have scaled := div_le_div_right positive (mul_le_mul_nonnegative_right small
    (factorialTerm_nonnegative nonnegative index))
  have cancel : ∀ term scale : Carrier, scale ≠ zero → div (mul scale term) scale = term := by
    intro term scale scaleNonzero
    real_grind
  rw [cancel _ _ nonzero] at scaled
  rw [factorialTerm_succ]
  exact scaled

private theorem below_index {base : Carrier} (small : le base two) (index : Nat) :
    le base (selection.ofRat ((index + 2 : Nat) : Rat)) := by
  refine le_trans small ((ofRat_le_iff _ _).mpr ?_)
  have cast := Rat.natCast_le_natCast.mpr (show 2 ≤ index + 2 by omega)
  exact cast

private theorem sine_term_even {base : Carrier} {index : Nat}
    (even : index % 4 = 0 ∨ index % 4 = 2) :
    Trigonometric.terms sineWeight base index = zero := by
  change mul (sineValues index) _ = zero
  unfold sineValues
  rcases even with residue | residue <;> rw [residue] <;> exact zero_mul _

private theorem sine_term_one {base : Carrier} {index : Nat} (residue : index % 4 = 1) :
    Trigonometric.terms sineWeight base index = factorialTerm base index := by
  change mul (sineValues index) _ = _
  unfold sineValues
  rw [residue]
  exact one_mul _

private theorem sine_term_three {base : Carrier} {index : Nat} (residue : index % 4 = 3) :
    Trigonometric.terms sineWeight base index = neg (factorialTerm base index) := by
  change mul (sineValues index) _ = _
  unfold sineValues
  rw [residue]
  show mul (neg one) _ = _
  rw [neg_mul, one_mul]

private theorem sine_partial_lower {base : Carrier} (nonnegative : le zero base)
    (small : le base two) :
    ∀ index, 4 ≤ index →
      le (partialSum (Trigonometric.terms sineWeight base) 4)
        (partialSum (Trigonometric.terms sineWeight base) index) := by
  let partials := partialSum (Trigonometric.terms sineWeight base)
  have block : ∀ start, start % 4 = 0 →
      le (partials start) (partials (start + 1)) ∧
        le (partials start) (partials (start + 2)) ∧
        le (partials start) (partials (start + 3)) ∧
        le (partials start) (partials (start + 4)) := by
    intro start residue
    have first : partials (start + 1) = partials start := by
      change add (partials start) _ = _
      rw [sine_term_even (Or.inl residue), add_zero]
    have second : partials (start + 2) =
        add (partials start) (factorialTerm base (start + 1)) := by
      change add (partials (start + 1)) _ = _
      rw [first, sine_term_one (by omega)]
    have third : partials (start + 3) = partials (start + 2) := by
      change add (partials (start + 2)) _ = _
      rw [sine_term_even (Or.inr (by omega)), add_zero]
    have fourth : partials (start + 4) = add (partials start)
        (sub (factorialTerm base (start + 1)) (factorialTerm base (start + 3))) := by
      change add (partials (start + 3)) _ = _
      rw [third, second, sine_term_three (by omega)]
      real_grind
    have shrink : le (factorialTerm base (start + 3)) (factorialTerm base (start + 1)) :=
      le_trans (factorialTerm_step_le nonnegative (below_index small (start + 1)))
        (factorialTerm_step_le nonnegative (below_index small start))
    have termNonnegative := factorialTerm_nonnegative nonnegative (start + 1)
    refine ⟨by rw [first]; exact le_refl _, ?_, ?_, ?_⟩
    · rw [second]
      real_grind
    · rw [third, second]
      real_grind
    · rw [fourth]
      real_grind
  have blocks : ∀ count, le (partials 4) (partials (4 * count + 4)) := by
    intro count
    induction count with
    | zero => exact le_refl _
    | succ count previous =>
        have next := (block (4 * count + 4) (by omega)).2.2.2
        rw [show 4 * (count + 1) + 4 = 4 * count + 4 + 4 by omega]
        exact le_trans previous next
  intro index later
  obtain ⟨count, offset, offsetSmall, rfl⟩ :
      ∃ count offset, offset < 4 ∧ index = 4 * count + 4 + offset :=
    ⟨(index - 4) / 4, (index - 4) % 4, Nat.mod_lt _ (by omega), by omega⟩
  have within := block (4 * count + 4) (by omega)
  have start := blocks count
  rcases (by omega : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3) with
    rfl | rfl | rfl | rfl
  · exact start
  · exact le_trans start within.1
  · exact le_trans start within.2.1
  · exact le_trans start within.2.2.1

private theorem sin_positive_small {base : Carrier} (positive : lt zero base)
    (small : le base two) : lt zero (sin base) := by
  have lower : le (partialSum (Trigonometric.terms sineWeight base) 4) (sin base) := by
    have converges := converges_to_neg (partialSum_converges
      (Trigonometric.terms sineWeight base) (Trigonometric.terms_summable sineWeight base))
    have bounded := limit_le_of_eventually_le converges 4 (fun index later =>
      neg_le_neg_iff.mpr (sine_partial_lower positive.1 small index later))
    exact neg_le_neg_iff.mp bounded
  have opening : partialSum (Trigonometric.terms sineWeight base) 4 =
      sub base (div (mul base (mul base base)) (selection.ofRat 6)) := by
    rw [partialSum_succ, partialSum_succ, partialSum_succ, partialSum_succ, partialSum_zero,
      sine_term_even (index := 0) (Or.inl rfl), sine_term_one (index := 1) rfl,
      sine_term_even (index := 2) (Or.inr rfl), sine_term_three (index := 3) rfl]
    simp only [factorialTerm_succ, factorialTerm_zero, Nat.reduceAdd, Rat.natCast_ofNat]
    real_grind
  have square : le (mul base base) (selection.ofRat 4) := by
    have once := mul_le_mul_nonnegative_right small positive.1
    have twice := mul_le_mul_nonnegative_left small (show le zero two by
      unfold two; real_grind)
    unfold two at once twice
    real_grind
  have margin : lt zero (sub one (div (mul base base) (selection.ofRat 6))) := by
    real_grind
  have product := mul_positive positive margin
  refine lt_of_lt_of_le ?_ lower
  rw [opening]
  generalize mul base base = squared at product
  real_grind

private theorem half_pi_le_two : le (half pi) two := by
  have bounds := Arctangent.arctangent_bounds one_nonnegative
  rw [half_pi_eq]
  unfold two
  have upper := bounds.2
  real_grind

private theorem cos_eq_sin_complement (point : Carrier) :
    cos point = sin (sub (half pi) point) := by
  rw [sub_eq_add_neg, sin_add, sin_half_pi, cos_half_pi, cos_neg]
  real_grind

private theorem cos_positive_right {point : Carrier} (nonnegative : le zero point)
    (upper : lt point (half pi)) : lt zero (cos point) := by
  rw [cos_eq_sin_complement]
  apply sin_positive_small (sub_positive_iff.mpr upper)
  have below := half_pi_le_two
  real_grind

/-- Cosine is positive strictly inside a half turn around zero, so `π/2` is its
least positive zero. -/
public theorem cos_positive {point : Carrier} (lower : lt (neg (half pi)) point)
    (upper : lt point (half pi)) : lt zero (cos point) := by
  rcases le_total zero point with nonnegative | nonpositive
  · exact cos_positive_right nonnegative upper
  · rw [← cos_neg]
    apply cos_positive_right (neg_nonnegative_iff.mpr nonpositive)
    real_grind

/-- Sine is positive strictly inside the first half turn, so `π` is its least
positive zero. -/
public theorem sin_positive {point : Carrier} (lower : lt zero point)
    (upper : lt point pi) : lt zero (sin point) := by
  have shifted : sin point = cos (sub point (half pi)) := by
    rw [sub_eq_add_neg, cos_add, sin_neg, cos_neg, sin_half_pi, cos_half_pi]
    real_grind
  rw [shifted]
  have halves := add_half pi
  apply cos_positive <;> real_grind

end

end Problib.Analysis
