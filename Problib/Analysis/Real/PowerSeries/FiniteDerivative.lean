module

public import Problib.Analysis.Real.PowerSeries.Product
public import Problib.Analysis.Real.Calculus

/-! Finite power derivatives, before the uniform limit exchange. -/

set_option autoImplicit false

namespace Problib.Analysis.Real.PowerSeries

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real
open Problib.Analysis.Real.SignedSeries

noncomputable section

private instance : Std.Associative (α := selection.Carrier) add :=
  ⟨fun left middle right => add_assoc left middle right⟩

private instance : Std.Commutative (α := selection.Carrier) add :=
  ⟨add_comm⟩

private instance : Std.Associative (α := selection.Carrier) mul :=
  ⟨fun left middle right => mul_assoc left middle right⟩

private instance : Std.Commutative (α := selection.Carrier) mul :=
  ⟨mul_comm⟩

@[expose] public def naturalScale : Nat → selection.Carrier
  | 0 => zero
  | count + 1 => add one (naturalScale count)

public theorem naturalScale_of_rat (count : Nat) :
    naturalScale count = selection.ofRat (count : Rat) := by
  induction count with
  | zero =>
      change zero = selection.ofRat 0
      exact ofRat_zero.symm
  | succ count induction =>
      change add one (naturalScale count) =
        selection.ofRat (((count + 1 : Nat) : Rat))
      rw [induction, Rat.natCast_add, ofRat_add,
        show ((1 : Nat) : Rat) = 1 from rfl, ofRat_one, add_comm]

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
      rw [add_zero, zero_add, mul_one]
      exact le_refl one
  | succ count induction =>
      rw [partial_sum_succ, power_succ]
      change le
        (mul (add one (naturalScale (count + 1)))
          (mul ratio (power ratio count)))
        (add (partialSum (power ratio) (count + 1))
          (mul ratio (power ratio count)))
      rw [add_mul, one_mul]
      have step := mul_le_mul_nonnegative_left induction nonnegative
      have scaling := mul_le_mul_nonnegative_right atMostOne
        (partial_sum_nonnegative
          (fun index => power_nonnegative nonnegative index) (count + 1))
      have bound := le_trans step scaling
      rw [one_mul] at bound
      have rearranged :
          mul (naturalScale (count + 1))
            (mul ratio (power ratio count)) =
          mul ratio
            (mul (naturalScale (count + 1)) (power ratio count)) := by
        ac_rfl
      rw [rearranged]
      have combined := add_le_add
        (le_refl (mul ratio (power ratio count))) bound
      rw [add_comm (mul ratio (power ratio count))
        (partialSum (power ratio) (count + 1))] at combined
      exact combined

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
      ac_rfl

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
      rw [add_mul, one_mul]
      ac_rfl

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
  rw [powerDerivative_succ, power_mul]
  have scaled := mul_le_mul_nonnegative_right
    (scaled_power_bounded ratioNonnegative ratioBelowOne count)
    (power_nonnegative radiusPositive.left count)
  have leftEqual :
      mul (naturalScale (count + 1))
        (mul (power ratio count) (power radius count)) =
      mul (mul (naturalScale (count + 1)) (power ratio count))
        (power radius count) := by
    rw [mul_assoc]
  rw [leftEqual]
  have rightEqual :
      mul (mul (inverse (sub one ratio)) (inverse radius))
        (power radius (count + 1)) =
      mul (inverse (sub one ratio)) (power radius count) := by
    rw [power_succ]
    calc
      mul (mul (inverse (sub one ratio)) (inverse radius))
          (mul radius (power radius count)) =
        mul (inverse (sub one ratio))
          (mul (mul (inverse radius) radius) (power radius count)) := by
        ac_rfl
      _ = mul (inverse (sub one ratio)) (power radius count) := by
        rw [inverse_mul_cancel radiusNonzero, one_mul]
  rw [rightEqual]
  exact scaled

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
        calc
          sub (mul second (power second count))
              (mul first (power first count)) =
            add (sub (mul second (power second count))
              (mul second (power first count)))
              (sub (mul second (power first count))
                (mul first (power first count))) :=
            (sub_add_sub _ _ _).symm
          _ = add (mul second
                (sub (power second count) (power first count)))
              (mul (sub second first) (power first count)) := by
            rw [mul_sub, sub_mul]
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
      rw [add_mul]
      have equal :
          add (mul radius
            (mul (powerDerivative radius count) (abs (sub second first))))
            (mul (abs (sub second first)) (power radius count)) =
          add (mul (power radius count) (abs (sub second first)))
            (mul (mul radius (powerDerivative radius count))
              (abs (sub second first))) := by
        ac_rfl
      rw [equal] at combined
      exact combined

@[expose] public def partialPolynomial
    (coefficients : Nat → selection.Carrier) (count : Nat)
    (point : selection.Carrier) : selection.Carrier :=
  partialSum (fun index => mul (coefficients index) (power point index)) count

@[expose] public def partialPolynomialDerivative
    (coefficients : Nat → selection.Carrier) (count : Nat)
    (point : selection.Carrier) : selection.Carrier :=
  partialSum
    (fun index => mul (coefficients index) (powerDerivative point index))
    count

public theorem has_derivative_partialPolynomial
    (coefficients : Nat → selection.Carrier) (count : Nat)
    (point : selection.Carrier) :
    HasDerivative (partialPolynomial coefficients count) point
      (partialPolynomialDerivative coefficients count point) := by
  induction count with
  | zero =>
      change HasDerivative (fun _ => zero) point zero
      exact hasDerivative_const zero point
  | succ count induction =>
      have added := hasDerivative_add induction
        (hasDerivative_smul (coefficients count)
          (has_derivative_power point count))
      have functionEqual : partialPolynomial coefficients (count + 1) =
          fun value => add (partialPolynomial coefficients count value)
            (mul (coefficients count) (power value count)) := by
        funext value
        unfold partialPolynomial
        rw [partial_sum_succ]
      have derivativeEqual :
          partialPolynomialDerivative coefficients (count + 1) point =
          add (partialPolynomialDerivative coefficients count point)
            (mul (coefficients count) (powerDerivative point count)) := by
        unfold partialPolynomialDerivative
        rw [partial_sum_succ]
      rw [functionEqual, derivativeEqual]
      exact added

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

public theorem partial_derivative_degree_source {dimension : Nat}
    (selected : Fin dimension)
    (index : MultiIndex.carrier dimension) :
    MultiIndex.degree dimension
      (MultiIndex.addIndex index (MultiIndex.unitIndex selected)) =
    MultiIndex.degree dimension index + 1 := by
  rw [MultiIndex.degree_addIndex,
    MultiIndex.degree_unitIndex]

end

end Problib.Analysis.Real.PowerSeries
