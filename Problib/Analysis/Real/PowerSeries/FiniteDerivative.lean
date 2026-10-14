module

public import Problib.Analysis.Real.PowerSeries.Product
public import Problib.Analysis.Real.Calculus
import Problib.Real.Grind

/-! Finite power derivatives, before the uniform limit exchange. -/

set_option autoImplicit false

namespace Problib.Analysis.Real.PowerSeries

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real
open Problib.Analysis.Real.SignedSeries

noncomputable section

@[expose] public def naturalScale : Nat → selection.Carrier
  | 0 => zero
  | count + 1 => add one (naturalScale count)

public theorem naturalScale_nonnegative (count : Nat) :
    le zero (naturalScale count) := by
  induction count with
  | zero => exact le_refl zero
  | succ count induction =>
      change le zero (add one (naturalScale count))
      exact add_nonnegative one_nonnegative induction

/-- The degree factor loses at most a geometric-series constant after
shrinking the radius. -/
public theorem scaled_power_le_geometric
    {ratio : selection.Carrier}
    (nonnegative : le zero ratio) (atMostOne : le ratio one)
    (count : Nat) :
    le (mul (naturalScale (count + 1)) (power ratio count))
      (partialSum (power ratio) (count + 1)) := by
  induction count with
  | zero =>
      change le (mul (add one zero) one) (add zero one)
      real_grind
  | succ count induction =>
      rw [partialSum_succ, power_succ]
      change le
        (mul (add one (naturalScale (count + 1)))
          (mul ratio (power ratio count)))
        (add (partialSum (power ratio) (count + 1))
          (mul ratio (power ratio count)))
      have step := mul_le_mul_nonnegative_left induction nonnegative
      have scaling := mul_le_mul_nonnegative_right atMostOne
        (partialSum_nonnegative
          (fun index => power_nonnegative nonnegative index) (count + 1))
      have bound := le_trans step scaling
      real_grind

public theorem scaled_power_bounded
    {ratio : selection.Carrier}
    (nonnegative : le zero ratio) (belowOne : lt ratio one)
    (count : Nat) :
    le (mul (naturalScale (count + 1)) (power ratio count))
      (inverse (sub one ratio)) :=
  le_trans (scaled_power_le_geometric nonnegative (le_of_lt belowOne) count)
    (geometric_bounded nonnegative belowOne (count + 1))

public theorem power_mul (first second : selection.Carrier) (count : Nat) :
    power (mul first second) count =
      mul (power first count) (power second count) := by
  induction count with
  | zero => rw [power_zero, power_zero, power_zero, one_mul]
  | succ count induction =>
      rw [power_succ, power_succ, power_succ, induction]
      real_grind

/-- The algebraic derivative of a natural power, built by the product rule. -/
@[expose] public def powerDerivative (point : selection.Carrier) :
    Nat → selection.Carrier
  | 0 => zero
  | count + 1 =>
      add (power point count) (mul point (powerDerivative point count))

public theorem has_derivative_power (point : selection.Carrier)
    (count : Nat) :
    HasDerivative (fun argument => power argument count)
      point (powerDerivative point count) := by
  induction count with
  | zero =>
      simpa only [power_zero, powerDerivative] using
        (hasDerivative_const one point)
  | succ count induction =>
      have product := hasDerivative_mul
        (hasDerivative_identity point) induction
      simpa only [power_succ, powerDerivative, one_mul] using product

public theorem powerDerivative_add (point : selection.Carrier)
    (first second : Nat) :
    powerDerivative point (first + second) =
      add (mul (powerDerivative point first) (power point second))
        (mul (power point first) (powerDerivative point second)) := by
  have left := has_derivative_power point (first + second)
  have equal : (fun argument => power argument (first + second)) =
      (fun argument => mul (power argument first)
        (power argument second)) := by
    funext argument
    exact power_add argument first second
  rw [equal] at left
  have right := hasDerivative_mul
    (has_derivative_power point first)
    (has_derivative_power point second)
  exact HasDerivative.unique left right

/-- The recursive product rule has the familiar natural coefficient. -/
public theorem powerDerivative_succ (point : selection.Carrier)
    (count : Nat) :
    powerDerivative point (count + 1) =
      mul (naturalScale (count + 1)) (power point count) := by
  induction count with
  | zero =>
      simp only [powerDerivative, naturalScale, power_zero,
        mul_zero, add_zero, mul_one]
  | succ count induction =>
      rw [powerDerivative, induction, power_succ]
      change add (mul point (power point count))
          (mul point
            (mul (naturalScale (count + 1)) (power point count))) =
        mul (add one (naturalScale (count + 1)))
          (mul point (power point count))
      real_grind

/-- An intermediate geometric radius bounds each differentiated degree by
the undifferentiated degree at a larger radius. -/
public theorem powerDerivative_shrunk
    {ratio radius : selection.Carrier}
    (ratioNonnegative : le zero ratio) (ratioBelowOne : lt ratio one)
    (radiusPositive : lt zero radius) (count : Nat) :
    le (powerDerivative (mul ratio radius) (count + 1))
      (mul (mul (inverse (sub one ratio)) (inverse radius))
        (power radius (count + 1))) := by
  have radiusNonzero := nonzero_of_positive radiusPositive
  rw [powerDerivative_succ, power_mul, power_succ]
  have scaled := mul_le_mul_nonnegative_right
    (scaled_power_bounded ratioNonnegative ratioBelowOne count)
    (power_nonnegative radiusPositive.left count)
  have rightEqual : mul (mul (inverse (sub one ratio)) (inverse radius))
      (mul radius (power radius count)) =
      mul (inverse (sub one ratio)) (power radius count) := by real_grind
  rw [rightEqual]
  real_grind

public theorem powerDerivative_zero_at_zero :
    powerDerivative zero 0 = zero := rfl

public theorem powerDerivative_one_at_zero :
    powerDerivative zero 1 = one := by
  change add (power zero 0) (mul zero zero) = one
  rw [power_zero, zero_mul, add_zero]

public theorem powerDerivative_high_at_zero (count : Nat) :
    powerDerivative zero (count + 2) = zero := by
  rw [powerDerivative_succ]
  change mul (naturalScale (count + 2)) (power zero (count + 1)) = zero
  rw [power_succ, zero_mul, mul_zero]

public theorem powerDerivative_nonnegative
    {radius : selection.Carrier} (nonnegative : le zero radius)
    (count : Nat) :
    le zero (powerDerivative radius count) := by
  induction count with
  | zero => exact le_refl zero
  | succ count induction =>
      change le zero (add (power radius count)
        (mul radius (powerDerivative radius count)))
      exact add_nonnegative (power_nonnegative nonnegative count)
        (mul_nonnegative nonnegative induction)

/-- A power's finite difference has the algebraic derivative as a
nonnegative Lipschitz bound on a closed interval. -/
public theorem power_difference_bound
    {radius : selection.Carrier} (nonnegative : le zero radius)
    {first second : selection.Carrier}
    (firstBound : le (abs first) radius)
    (secondBound : le (abs second) radius)
    (count : Nat) :
    le (abs (sub (power second count) (power first count)))
      (mul (powerDerivative radius count) (abs (sub second first))) := by
  induction count with
  | zero =>
      rw [power_zero, power_zero, sub_self, abs_zero]
      change le zero (mul zero (abs (sub second first)))
      rw [zero_mul]
      exact le_refl zero
  | succ count induction =>
      have split :
          sub (power second (count + 1)) (power first (count + 1)) =
          add (mul second
            (sub (power second count) (power first count)))
            (mul (sub second first) (power first count)) := by
        rw [power_succ, power_succ]
        real_grind
      rw [split]
      have triangle := abs_add_le
        (mul second (sub (power second count) (power first count)))
        (mul (sub second first) (power first count))
      rw [abs_mul, abs_mul] at triangle
      have firstTerm :
          le (mul (abs second)
            (abs (sub (power second count) (power first count))))
            (mul radius
              (mul (powerDerivative radius count)
                (abs (sub second first)))) := by
        exact le_trans
          (mul_le_mul_nonnegative_left induction (abs_nonnegative second))
          (mul_le_mul_nonnegative_right secondBound
            (mul_nonnegative
              (powerDerivative_nonnegative nonnegative count)
              (abs_nonnegative _)))
      have powerTerm :
          le (abs (power first count)) (power radius count) := by
        rw [abs_power]
        exact MultiIndex.power_mono_base (abs_nonnegative first)
          firstBound count
      have secondTerm :
          le (mul (abs (sub second first))
            (abs (power first count)))
            (mul (abs (sub second first)) (power radius count)) :=
        mul_le_mul_nonnegative_left powerTerm (abs_nonnegative _)
      have combined := le_trans triangle
        (add_le_add firstTerm secondTerm)
      change le _
        (mul (add (power radius count)
          (mul radius (powerDerivative radius count)))
          (abs (sub second first)))
      real_grind

/-- Formal coordinate derivative: differentiating the coefficient at
`index + unitIndex selected` lowers that coordinate exponent by one. -/
@[expose] public def partialDerivativeCoefficients {dimension : Nat}
    (selected : Fin dimension)
    (coefficients : MultiIndex.carrier dimension → selection.Carrier) :
    MultiIndex.carrier dimension → selection.Carrier :=
  fun index => mul
    (naturalScale (index selected + 1))
    (coefficients (MultiIndex.addIndex index
      (MultiIndex.unitIndex selected)))

end

end Problib.Analysis.Real.PowerSeries
