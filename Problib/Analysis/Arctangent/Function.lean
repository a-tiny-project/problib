module

public import Problib.Analysis.Arctangent
public import Problib.Measure.Real.Borel
import Problib.Real.Grind

/-! The arctangent as a function on the whole line.

`Arctangent.lean` integrates `K t = 1 / (1 + t²)` over `(0, x]`, which is zero
when `x ≤ 0`. Since `K` is even, the signed integral from zero to `x` is the
difference of the integrals over the two rays, `atan x = A x - A (-x)`, so the
arctangent is odd by construction and agrees with `A` on the closed positive
ray.

The derivative is `K x` at every point. Away from zero one ray vanishes near
`x` and the positive-ray derivative of `Arctangent.lean` applies, through a
reflection on the negative side. At zero the two rays meet, and the increment
bounds give `|atan d - d| ≤ |d|³` instead. The reciprocal identity
`atan x + atan (1/x) = π/2` for `x > 0` comes from the integral definition of
`π`, and with `atan (1/x) ≤ 1/x` it bounds the distance to `π/2`, so the range
is the open interval `(-π/2, π/2)` and the limits at `±∞` are `±π/2`.
-/

set_option autoImplicit false

namespace Problib.Analysis

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real
open Problib.Analysis.Arctangent

local notation "K(" t ")" => inverse (add one (mul t t))
local notation "A(" x ")" =>
  ENNReal.toReal (lintegral (volume.restrict (Ioc zero x)) (fun t => ENNReal.ofReal (K(t))))

noncomputable section

/-- The arctangent, the signed integral of `1 / (1 + t²)` from zero. -/
@[expose] public def atan (x : Carrier) : Carrier := sub (A(x)) (A(neg x))

private theorem ray_vanishes {x : Carrier} (nonpositive : le x zero) : A(x) = zero := by
  rw [interval_reverse zero x nonpositive, ENNReal.toReal_zero]

private theorem ray_strict {first second : Carrier} (nonnegative : le zero first)
    (ordered : lt first second) : lt (A(first)) (A(second)) := by
  have lower := (increment_bounds nonnegative (le_of_lt ordered)).1
  have gap : lt zero (mul (sub second first) (K(second))) :=
    mul_positive (sub_positive_iff.mpr ordered) (kernel_positive second)
  real_grind

private theorem ray_positive {x : Carrier} (positive : lt zero x) : lt zero (A(x)) := by
  have strict := ray_strict (le_refl zero) positive
  rwa [arctangent_zero] at strict

/-- Near zero the positive-ray integral is `x` to third order. -/
private theorem ray_cubic {x : Carrier} (nonnegative : le zero x) :
    le zero (sub x (A(x))) ∧ le (sub x (A(x))) (mul x (mul x x)) := by
  have upper := (arctangent_bounds nonnegative).2
  have lower := (increment_bounds (le_refl zero) nonnegative).1
  rw [arctangent_zero] at lower
  have denominator : add one (mul x x) ≠ zero := by
    have square := mul_self_nonnegative x
    apply nonzero_of_positive
    real_grind
  have cancel := congrArg (mul x) (mul_inverse_cancel denominator)
  have shrink := mul_le_mul_nonnegative_left (kernel_le_one x)
    (mul_nonnegative nonnegative (mul_self_nonnegative x))
  constructor <;> real_grind

/-- On the closed positive ray the arctangent is the integral over `(0, x]`. -/
public theorem atan_of_nonnegative {x : Carrier} (nonnegative : le zero x) : atan x = A(x) := by
  unfold atan
  rw [ray_vanishes (neg_nonpositive_iff.mp nonnegative)]
  real_grind

/-- On the closed negative ray the arctangent is minus the integral over `(0, -x]`. -/
public theorem atan_of_nonpositive {x : Carrier} (nonpositive : le x zero) :
    atan x = neg (A(neg x)) := by
  unfold atan
  rw [ray_vanishes nonpositive]
  real_grind

/-- The arctangent vanishes at zero. -/
public theorem atan_zero : atan zero = zero := by
  unfold atan
  rw [neg_zero, sub_self]

/-- The arctangent is odd. -/
public theorem atan_neg (x : Carrier) : atan (neg x) = neg (atan x) := by
  unfold atan
  rw [neg_neg]
  real_grind

/-- The arctangent is strictly increasing. -/
public theorem atan_strictMono {first second : Carrier} (ordered : lt first second) :
    lt (atan first) (atan second) := by
  rcases le_total zero first with firstNonnegative | firstNonpositive
  · rw [atan_of_nonnegative firstNonnegative,
      atan_of_nonnegative (le_trans firstNonnegative (le_of_lt ordered))]
    exact ray_strict firstNonnegative ordered
  · rcases le_total zero second with secondNonnegative | secondNonpositive
    · rw [atan_of_nonpositive firstNonpositive, atan_of_nonnegative secondNonnegative]
      have firstRay := ENNReal.toReal_nonnegative
        (lintegral (volume.restrict (Ioc zero (neg first))) (fun t => ENNReal.ofReal (K(t))))
      have secondRay := ENNReal.toReal_nonnegative
        (lintegral (volume.restrict (Ioc zero second)) (fun t => ENNReal.ofReal (K(t))))
      rcases lt_trichotomy first zero with negative | vanished | positive
      · have strict := ray_positive (neg_positive_iff.mpr negative)
        real_grind
      · subst first
        have strict := ray_positive ordered
        real_grind
      · exact absurd firstNonpositive (not_le_iff_lt.mpr positive)
    · rw [atan_of_nonpositive firstNonpositive, atan_of_nonpositive secondNonpositive]
      have strict := ray_strict (neg_nonnegative_iff.mpr secondNonpositive)
        (show lt (neg second) (neg first) by real_grind)
      real_grind

/-- The arctangent is monotone. -/
public theorem atan_monotone : Monotone atan := by
  intro first second ordered
  rcases lt_trichotomy first second with less | equal | greater
  · exact le_of_lt (atan_strictMono less)
  · rw [equal]
    exact le_refl _
  · exact absurd ordered (not_le_iff_lt.mpr greater)

/-- The arctangent is Borel measurable, because it is monotone. -/
public theorem atan_measurable : MeasurableMap borel borel atan :=
  monotone_measurable atan_monotone

/-- The arctangent is `x` to third order at zero. -/
public theorem atan_cubic (x : Carrier) :
    le (abs (sub (atan x) x)) (mul (abs x) (mul (abs x) (abs x))) := by
  rcases le_total zero x with nonnegative | nonpositive
  · have bounds := ray_cubic nonnegative
    rw [atan_of_nonnegative nonnegative, abs_of_nonnegative nonnegative,
      abs_of_nonpositive (by real_grind)]
    real_grind
  · have reflected := neg_nonnegative_iff.mpr nonpositive
    have bounds := ray_cubic reflected
    rw [atan_of_nonpositive nonpositive, abs_of_nonpositive nonpositive,
      abs_of_nonnegative (by real_grind)]
    real_grind

private theorem hasDerivative_atan_zero : HasDerivative atan zero (K(zero)) := by
  have flat : HasDerivative (fun value => sub (atan value) value) zero zero := by
    refine derivative_of_secant_bound _ zero zero one one one_positive one_nonnegative ?_
    intro displacement nonzero small
    rw [sub_zero]
    apply secant_le_of_increment nonzero
    show le (abs (sub (sub (atan displacement) displacement) (sub (atan zero) zero)))
      (mul (abs displacement) (mul one (abs displacement)))
    rw [atan_zero, sub_self, sub_zero]
    have size := abs_nonnegative displacement
    have cube := mul_le_mul_nonnegative_left (le_of_lt small)
      (mul_nonnegative size size)
    have bound := atan_cubic displacement
    real_grind
  have sum := hasDerivative_add flat (hasDerivative_identity zero)
  have value : K(zero) = add zero one := by
    rw [mul_zero, add_zero, inverse_one, zero_add]
  rw [value]
  refine HasDerivative.congr_near (NearZero.of_forall fun displacement => ?_) sum
  show add (sub (atan (add zero displacement)) (add zero displacement)) (add zero displacement) =
    atan (add zero displacement)
  real_grind

/-- The arctangent differentiates to `1 / (1 + x²)` at every point. -/
public theorem hasDerivative_atan (x : Carrier) : HasDerivative atan x (K(x)) := by
  rcases lt_trichotomy zero x with positive | vanished | negative
  · refine HasDerivative.congr_near ⟨x, positive, fun displacement small => ?_⟩
      (hasDerivative_arctangent positive)
    have inside := (abs_lt.mp small).1
    exact (atan_of_nonnegative (by real_grind)).symm
  · subst x
    exact hasDerivative_atan_zero
  · have reflected := hasDerivative_comp (inner := fun value => neg value)
      (hasDerivative_arctangent (neg_positive_iff.mpr negative))
      (hasDerivative_neg (hasDerivative_identity x))
    have negated := hasDerivative_neg reflected
    have square : mul (neg x) (neg x) = mul x x := by real_grind
    have value : neg (mul (K(neg x)) (neg one)) = K(x) := by
      rw [square]
      real_grind
    rw [value] at negated
    refine HasDerivative.congr_near ⟨neg x, neg_positive_iff.mpr negative,
      fun displacement small => ?_⟩ negated
    have inside := (abs_lt.mp small).2
    exact (atan_of_nonpositive (by real_grind)).symm

/-- The arctangent is continuous at every point. -/
public theorem atan_continuous (x : Carrier) :
    Approaches (fun displacement => atan (add x displacement)) (atan x) :=
  hasDerivative_continuous (hasDerivative_atan x)

/-- The arctangent of one is a quarter of the integral `π`. -/
public theorem atan_one : atan one = div pi (selection.ofRat 4) := by
  rw [atan_of_nonnegative one_positive.1, pi_eq_four]
  real_grind

/-- Reciprocal arguments on the positive ray complement each other to `π/2`. -/
public theorem atan_add_atan_inverse {x : Carrier} (positive : lt zero x) :
    add (atan x) (atan (inverse x)) = half pi := by
  rw [atan_of_nonnegative positive.1,
    atan_of_nonnegative (inverse_of_positive_positive positive).1,
    arctangent_reciprocal positive, pi_eq_four]
  unfold half two
  real_grind

/-- Reciprocal arguments on the negative ray complement each other to `-π/2`. -/
public theorem atan_add_atan_inverse_of_negative {x : Carrier} (negative : lt x zero) :
    add (atan x) (atan (inverse x)) = neg (half pi) := by
  have reflected := atan_add_atan_inverse (neg_positive_iff.mpr negative)
  rw [atan_neg, inverse_neg, atan_neg] at reflected
  real_grind

/-- Beyond zero, the arctangent falls short of `π/2` by at most the reciprocal. -/
public theorem half_pi_sub_atan_le {x : Carrier} (positive : lt zero x) :
    le (sub (half pi) (atan x)) (inverse x) := by
  have complement := atan_add_atan_inverse positive
  have reciprocalPositive := inverse_of_positive_positive positive
  have bound := (arctangent_bounds reciprocalPositive.1).2
  rw [← atan_of_nonnegative reciprocalPositive.1] at bound
  real_grind

/-- The arctangent stays below `π/2`. -/
public theorem atan_lt_half_pi (x : Carrier) : lt (atan x) (half pi) := by
  have halfPositive := half_positive pi_positive
  rcases le_total x zero with nonpositive | nonnegative
  · rw [atan_of_nonpositive nonpositive]
    have ray := ENNReal.toReal_nonnegative
      (lintegral (volume.restrict (Ioc zero (neg x))) (fun t => ENNReal.ofReal (K(t))))
    real_grind
  · rcases lt_trichotomy zero x with positive | vanished | negative
    · have complement := atan_add_atan_inverse positive
      have reciprocalPositive := inverse_of_positive_positive positive
      have remainder := ray_positive reciprocalPositive
      rw [← atan_of_nonnegative reciprocalPositive.1] at remainder
      real_grind
    · rw [← vanished, atan_zero]
      exact halfPositive
    · exact absurd nonnegative (not_le_iff_lt.mpr negative)

/-- The arctangent stays above `-π/2`. -/
public theorem neg_half_pi_lt_atan (x : Carrier) : lt (neg (half pi)) (atan x) := by
  have reflected := atan_lt_half_pi (neg x)
  rw [atan_neg] at reflected
  real_grind

/-- The arctangent tends to `π/2` at `+∞`. -/
public theorem atan_tendsto_half_pi {tolerance : Carrier} (positive : lt zero tolerance) :
    ∃ threshold, lt zero threshold ∧
      ∀ x, lt threshold x → lt (abs (sub (half pi) (atan x))) tolerance := by
  have thresholdPositive := inverse_of_positive_positive positive
  refine ⟨inverse tolerance, thresholdPositive, fun x beyond => ?_⟩
  have xPositive := lt_trans thresholdPositive beyond
  have shrunk := inverse_lt_inverse_of_positive thresholdPositive xPositive beyond
  rw [inverse_inverse] at shrunk
  have bound := half_pi_sub_atan_le xPositive
  have below := atan_lt_half_pi x
  rw [abs_of_nonnegative (by real_grind)]
  real_grind

/-- The arctangent tends to `-π/2` at `-∞`. -/
public theorem atan_tendsto_neg_half_pi {tolerance : Carrier} (positive : lt zero tolerance) :
    ∃ threshold, lt zero threshold ∧
      ∀ x, lt x (neg threshold) → lt (abs (sub (atan x) (neg (half pi)))) tolerance := by
  obtain ⟨threshold, thresholdPositive, close⟩ := atan_tendsto_half_pi positive
  refine ⟨threshold, thresholdPositive, fun x beyond => ?_⟩
  have reflected := close (neg x) (by real_grind)
  rw [atan_neg] at reflected
  have same : sub (atan x) (neg (half pi)) = sub (half pi) (neg (atan x)) := by real_grind
  rwa [same]

end

end Problib.Analysis
