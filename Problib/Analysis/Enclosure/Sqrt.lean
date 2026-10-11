module

public import Problib.Analysis.Enclosure.Interval
public import Problib.Analysis.Sqrt

/-! Certified enclosures of the square root.

The real square root clamps its argument at zero, `(sqrt (NNReal.ofReal x)).val`,
so it is zero on negative arguments, as in λCh. For a rational `q ≥ 0` the
integer square root `s` of `⌊q 4^p⌋` satisfies `s² ≤ q 4^p < (s + 1)²`, so
`s / 2^p` and `(s + 1) / 2^p` bracket `√q` one grid step apart. A negative
rational has count zero, and its bracket `[0, 2^-p]` holds the clamped root.

An interval's enclosure refuses a negative lower endpoint. Otherwise it takes
the lower bound at the lower endpoint and the upper bound at the upper
endpoint, since the root increases. Its width is bounded without irrationals:
for every rational `r ≥ 0` with `width + 2 / 4^p ≤ r²`, the width is at most
`r + 2 / 2^p`.
-/

set_option autoImplicit false

namespace Problib.Analysis.Enclosure

open Problib.Real
open Problib.Real.Construction
open Problib.Real.Construction.Dedekind

/-! ### Integer roots -/

/-- The integer square root of the number of `4^-precision` steps in `value`,
zero when `value` is negative. -/
@[expose] public def sqrtCount (precision : Nat) (value : Rat) : Nat :=
  Nat.sqrt (value * scale precision * scale precision).floor.toNat

/-- A grid point at or below the clamped square root of `value`. -/
@[expose] public def sqrtLower (precision : Nat) (value : Rat) : Rat :=
  (sqrtCount precision value : Rat) / scale precision

/-- A grid point above the clamped square root of `value`. -/
@[expose] public def sqrtUpper (precision : Nat) (value : Rat) : Rat :=
  ((sqrtCount precision value : Rat) + 1) / scale precision

/-- A nonnegative value's step count lies within one of its scaled value. -/
private theorem count_bounds (precision : Nat) {value : Rat} (nonnegative : 0 ≤ value) :
    (((value * scale precision * scale precision).floor.toNat : Nat) : Rat) ≤
        value * scale precision * scale precision ∧
      value * scale precision * scale precision <
        (((value * scale precision * scale precision).floor.toNat : Nat) : Rat) + 1 := by
  have positive := scale_positive precision
  have scaledNonnegative : 0 ≤ value * scale precision * scale precision :=
    Rat.mul_nonneg (Rat.mul_nonneg nonnegative (Rat.le_of_lt positive)) (Rat.le_of_lt positive)
  have floorNonnegative : (0 : Int) ≤ (value * scale precision * scale precision).floor :=
    Rat.le_floor_iff.mpr (by simpa using scaledNonnegative)
  have cast : (((value * scale precision * scale precision).floor.toNat : Nat) : Rat) =
      ((value * scale precision * scale precision).floor : Rat) := by
    rw [← Rat.intCast_natCast, Int.toNat_of_nonneg floorNonnegative]
  rw [cast]
  constructor
  · exact Rat.floor_le _
  · have above := Rat.lt_floor_add_one (value * scale precision * scale precision)
    rwa [Rat.intCast_add, Rat.intCast_one] at above

/-- A negative value has no steps. -/
private theorem count_negative (precision : Nat) {value : Rat} (negative : value < 0) :
    (value * scale precision * scale precision).floor.toNat = 0 := by
  have positive := scale_positive precision
  have scaledNegative : value * scale precision * scale precision < 0 := by
    have := Rat.mul_lt_mul_of_pos_right (Rat.mul_lt_mul_of_pos_right negative positive) positive
    simpa using this
  have floorNegative := Rat.floor_lt_iff.mpr
    (show value * scale precision * scale precision < ((0 : Int) : Rat) by
      simpa using scaledNegative)
  exact Int.toNat_eq_zero.mpr (Int.le_of_lt floorNegative)

/-- The integer root of a nonnegative value's step count brackets its scaled
square root. -/
public theorem sqrtCount_bounds (precision : Nat) {value : Rat} (nonnegative : 0 ≤ value) :
    (sqrtCount precision value : Rat) * sqrtCount precision value ≤
        value * scale precision * scale precision ∧
      value * scale precision * scale precision <
        ((sqrtCount precision value : Rat) + 1) * ((sqrtCount precision value : Rat) + 1) := by
  obtain ⟨countBelow, countAbove⟩ := count_bounds precision nonnegative
  have rootBelow : sqrtCount precision value * sqrtCount precision value ≤
      (value * scale precision * scale precision).floor.toNat :=
    Nat.sqrt_le _
  have rootAbove : (value * scale precision * scale precision).floor.toNat + 1 ≤
      (sqrtCount precision value + 1) * (sqrtCount precision value + 1) :=
    Nat.lt_succ_sqrt _
  have rootBelowCast := Rat.natCast_le_natCast.mpr rootBelow
  have rootAboveCast := Rat.natCast_le_natCast.mpr rootAbove
  rw [Rat.natCast_mul] at rootBelowCast
  rw [Rat.natCast_mul, Rat.natCast_add, Rat.natCast_add] at rootAboveCast
  have one : ((1 : Nat) : Rat) = 1 := rfl
  rw [one] at rootAboveCast
  constructor
  · exact Rat.le_trans rootBelowCast countBelow
  · grind

/-- A negative value's integer root is zero. -/
public theorem sqrtCount_negative (precision : Nat) {value : Rat} (negative : value < 0) :
    sqrtCount precision value = 0 := by
  unfold sqrtCount
  rw [count_negative precision negative]
  rfl

/-- The integer root increases with the value. -/
public theorem sqrtCount_monotone (precision : Nat) {first second : Rat}
    (ordered : first ≤ second) : sqrtCount precision first ≤ sqrtCount precision second := by
  have positive := Rat.le_of_lt (scale_positive precision)
  have scaled : first * scale precision * scale precision ≤
      second * scale precision * scale precision :=
    Rat.mul_le_mul_of_nonneg_right (Rat.mul_le_mul_of_nonneg_right ordered positive) positive
  have counts := Int.toNat_le_toNat (Rat.floor_monotone scaled)
  have squares := Nat.lt_of_le_of_lt
    (Nat.le_trans (Nat.sqrt_le (first * scale precision * scale precision).floor.toNat) counts)
    (Nat.lt_succ_sqrt (second * scale precision * scale precision).floor.toNat)
  exact Nat.le_of_lt_succ (Nat.mul_self_lt_mul_self_iff.mp squares)

/-! ### Point bounds -/

public theorem sqrtLower_nonnegative (precision : Nat) (value : Rat) :
    0 ≤ sqrtLower precision value :=
  (le_div_iff_mul_le (scale_positive precision)).mpr (by
    rw [Rat.zero_mul]
    exact Rat.natCast_nonneg)

public theorem sqrtUpper_nonnegative (precision : Nat) (value : Rat) :
    0 ≤ sqrtUpper precision value :=
  (le_div_iff_mul_le (scale_positive precision)).mpr (by
    rw [Rat.zero_mul]
    have := Rat.natCast_nonneg (a := sqrtCount precision value)
    grind)

/-- The lower bound is one grid step below the upper bound. -/
public theorem sqrtUpper_sub_sqrtLower (precision : Nat) (value : Rat) :
    sqrtUpper precision value - sqrtLower precision value = 1 / scale precision := by
  unfold sqrtUpper sqrtLower
  rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.add_mul]
  grind

/-- The lower bound times the grid scale is the integer root. -/
public theorem sqrtLower_mul_scale (precision : Nat) (value : Rat) :
    sqrtLower precision value * scale precision = sqrtCount precision value :=
  Rat.div_mul_cancel (Rat.ne_of_gt (scale_positive precision))

/-- The upper bound times the grid scale is one more than the integer root. -/
public theorem sqrtUpper_mul_scale (precision : Nat) (value : Rat) :
    sqrtUpper precision value * scale precision = (sqrtCount precision value : Rat) + 1 :=
  Rat.div_mul_cancel (Rat.ne_of_gt (scale_positive precision))

/-- The lower bound squares to at most a nonnegative value. -/
public theorem sqrtLower_square_le (precision : Nat) {value : Rat} (nonnegative : 0 ≤ value) :
    sqrtLower precision value * sqrtLower precision value ≤ value := by
  have positive := scale_positive precision
  apply Rat.le_of_mul_le_mul_right (c := scale precision * scale precision) _
    (Rat.mul_pos positive positive)
  have expand : sqrtLower precision value * sqrtLower precision value *
      (scale precision * scale precision) =
      (sqrtLower precision value * scale precision) *
        (sqrtLower precision value * scale precision) := by
    grind
  rw [expand, sqrtLower_mul_scale]
  have := (sqrtCount_bounds precision nonnegative).1
  grind

/-- The upper bound squares to more than a nonnegative value. -/
public theorem lt_sqrtUpper_square (precision : Nat) {value : Rat} (nonnegative : 0 ≤ value) :
    value < sqrtUpper precision value * sqrtUpper precision value := by
  have positive := scale_positive precision
  apply Rat.lt_of_mul_lt_mul_right (c := scale precision * scale precision) _
    (Rat.le_of_lt (Rat.mul_pos positive positive))
  have expand : sqrtUpper precision value * sqrtUpper precision value *
      (scale precision * scale precision) =
      (sqrtUpper precision value * scale precision) *
        (sqrtUpper precision value * scale precision) := by
    grind
  rw [expand, sqrtUpper_mul_scale]
  have := (sqrtCount_bounds precision nonnegative).2
  grind

/-- The lower bound lies at or below the clamped root of `value`. -/
public theorem sqrtLower_le (precision : Nat) (value : Rat) :
    le (selection.ofRat (sqrtLower precision value))
      (Problib.Analysis.sqrt (NNReal.ofReal (selection.ofRat value))).val := by
  have lowerNonnegative := sqrtLower_nonnegative precision value
  by_cases nonnegative : 0 ≤ value
  · have squares : NNReal.le
        (NNReal.mul (NNReal.ofRat _ lowerNonnegative) (NNReal.ofRat _ lowerNonnegative))
        (NNReal.mul (Problib.Analysis.sqrt (NNReal.ofReal (selection.ofRat value)))
          (Problib.Analysis.sqrt (NNReal.ofReal (selection.ofRat value)))) := by
      rw [sqrt_square, ← NNReal.ofRat_mul, NNReal.ofReal_ofRat, dite_eq_left nonnegative]
      exact (NNReal.ofRat_le_iff _ _ _ _).mpr (sqrtLower_square_le precision nonnegative)
    exact (square_le_iff _ _).mp squares
  · have zeroLower : sqrtLower precision value = 0 := by
      unfold sqrtLower
      rw [sqrtCount_negative precision (Rat.not_le.mp nonnegative), Rat.div_def]
      exact Rat.zero_mul _
    rw [zeroLower, ofRat_zero]
    exact (Problib.Analysis.sqrt (NNReal.ofReal (selection.ofRat value))).property

/-- The clamped root of `value` lies at or below the upper bound. -/
public theorem le_sqrtUpper (precision : Nat) (value : Rat) :
    le (Problib.Analysis.sqrt (NNReal.ofReal (selection.ofRat value))).val
      (selection.ofRat (sqrtUpper precision value)) := by
  have upperNonnegative := sqrtUpper_nonnegative precision value
  have squares : NNReal.le
      (NNReal.mul (Problib.Analysis.sqrt (NNReal.ofReal (selection.ofRat value)))
        (Problib.Analysis.sqrt (NNReal.ofReal (selection.ofRat value))))
      (NNReal.mul (NNReal.ofRat _ upperNonnegative) (NNReal.ofRat _ upperNonnegative)) := by
    rw [sqrt_square, ← NNReal.ofRat_mul, NNReal.ofReal_ofRat]
    split
    · rename_i nonnegative
      exact (NNReal.ofRat_le_iff _ _ _ _).mpr
        (Rat.le_of_lt (lt_sqrtUpper_square precision nonnegative))
    · exact NNReal.zero_le _
  exact (square_le_iff _ _).mp squares

/-! ### Intervals -/

namespace Interval

/-- The enclosure of the square root over an interval with a nonnegative
lower endpoint, refused otherwise. The endpoints are integer roots on the
`2^-precision` grid. -/
@[expose] public def sqrt? (precision : Nat) (interval : Interval) : Option Interval :=
  if 0 ≤ interval.lo then
    some {
      lo := sqrtLower precision interval.lo
      hi := sqrtUpper precision interval.hi
      ordered := by
        have counts := Rat.natCast_le_natCast.mpr (sqrtCount_monotone precision interval.ordered)
        show (sqrtCount precision interval.lo : Rat) / scale precision ≤ _
        apply (div_le_iff_le_mul (scale_positive precision)).mpr
        rw [sqrtUpper_mul_scale]
        grind }
  else none

/-- The square root's enclosure exists exactly when the interval has a
nonnegative lower endpoint. -/
public theorem sqrt?_isSome_iff (precision : Nat) (interval : Interval) :
    (interval.sqrt? precision).isSome = true ↔ 0 ≤ interval.lo := by
  unfold sqrt?
  by_cases nonnegative : 0 ≤ interval.lo
  · simp [nonnegative]
  · simp [nonnegative]

/-- A successful enclosure contains the root of every real member. -/
public theorem Contains.sqrt {interval result : Interval} {value : selection.Carrier}
    {precision : Nat} (computed : interval.sqrt? precision = some result)
    (member : interval.Contains value) :
    result.Contains (Problib.Analysis.sqrt (NNReal.ofReal value)).val := by
  unfold sqrt? at computed
  split at computed
  · cases computed
    exact ⟨le_trans (sqrtLower_le precision interval.lo)
        (sqrt_monotone (NNReal.ofReal_monotone member.1)),
      le_trans (sqrt_monotone (NNReal.ofReal_monotone member.2))
        (le_sqrtUpper precision interval.hi)⟩
  · cases computed

/-- A computed enclosure inside a rational bracket places every member's
square root in that bracket. The check runs on rational endpoints. -/
public theorem Contains.sqrt_bracket {interval : Interval} {value : selection.Carrier}
    (member : interval.Contains value) {precision : Nat} {lower upper : Rat}
    (checked : (interval.sqrt? precision).any
      (fun result => decide (lower ≤ result.lo ∧ result.hi ≤ upper)) = true) :
    le (selection.ofRat lower) (Problib.Analysis.sqrt (NNReal.ofReal value)).val ∧
      le (Problib.Analysis.sqrt (NNReal.ofReal value)).val (selection.ofRat upper) := by
  cases computed : interval.sqrt? precision with
  | none =>
      rw [computed, Option.any_none] at checked
      cases checked
  | some result =>
      rw [computed, Option.any_some] at checked
      have bounds := of_decide_eq_true checked
      have enclosed := Contains.sqrt computed member
      exact ⟨le_trans ((ofRat_le_iff _ _).mpr bounds.1) enclosed.1,
        le_trans enclosed.2 ((ofRat_le_iff _ _).mpr bounds.2)⟩

/-- The root's enclosure is at most `r + 2 / 2^p` wide for every rational
`r ≥ 0` whose square covers `input.width + 2 / 4^p`, the square-root modulus
with the rounding allowance stated entirely in rationals. -/
public theorem width_sqrt_le {interval result : Interval} {precision : Nat}
    (computed : interval.sqrt? precision = some result) {bound : Rat}
    (boundNonnegative : 0 ≤ bound)
    (covered : interval.width + 2 / ((4 ^ precision : Nat) : Rat) ≤ bound * bound) :
    result.width ≤ bound + 2 / scale precision := by
  have powerPositive : 0 < ((4 ^ precision : Nat) : Rat) :=
    Rat.natCast_pos.mpr (Nat.pow_pos (by decide +kernel))
  have errorNonnegative : 0 ≤ 2 / ((4 ^ precision : Nat) : Rat) :=
    (le_div_iff_mul_le powerPositive).mpr (by rw [Rat.zero_mul]; decide +kernel)
  have inputCovered : interval.width ≤ bound * bound := by grind
  unfold sqrt? at computed
  split at computed
  · rename_i nonnegative
    cases computed
    have positive := scale_positive precision
    have lowCount := Rat.natCast_nonneg (a := sqrtCount precision interval.lo)
    have highCount := Rat.natCast_nonneg (a := sqrtCount precision interval.hi)
    -- The lower endpoint lies below the next integer square.
    have lowBelow := (sqrtCount_bounds precision nonnegative).2
    have highNonnegative : 0 ≤ interval.hi := Rat.le_trans nonnegative interval.ordered
    -- The counts differ by at most the scaled bound plus one.
    have counts : (sqrtCount precision interval.hi : Rat) -
        sqrtCount precision interval.lo - 1 ≤ bound * scale precision := by
      apply Rat.not_lt.mp
      intro far
      have boundScaled := Rat.mul_nonneg boundNonnegative (Rat.le_of_lt positive)
      have highAbove := (sqrtCount_bounds precision highNonnegative).1
      have spread : interval.hi - interval.lo ≤ bound * bound := inputCovered
      have spreadScaled := Rat.mul_le_mul_of_nonneg_right spread
        (Rat.le_of_lt (Rat.mul_pos positive positive))
      have gapPositive := Rat.mul_pos
        (show 0 < (sqrtCount precision interval.hi : Rat) - sqrtCount precision interval.lo - 1 by
          grind)
        (show 0 < (sqrtCount precision interval.hi : Rat) - sqrtCount precision interval.lo - 1 -
          bound * scale precision by grind)
      have gapBound := Rat.mul_nonneg boundScaled
        (show 0 ≤ (sqrtCount precision interval.hi : Rat) - sqrtCount precision interval.lo - 1 -
          bound * scale precision by grind)
      have gapSum := Rat.mul_nonneg
        (show 0 ≤ (sqrtCount precision interval.hi : Rat) - sqrtCount precision interval.lo - 1 by
          grind)
        (show 0 ≤ 2 * (sqrtCount precision interval.lo : Rat) + 2 by grind)
      grind
    apply Rat.le_of_mul_le_mul_right _ positive
    have stepCancel : 2 / scale precision * scale precision = 2 :=
      Rat.div_mul_cancel (Rat.ne_of_gt positive)
    have upper := sqrtUpper_mul_scale precision interval.hi
    have lower := sqrtLower_mul_scale precision interval.lo
    show (sqrtUpper precision interval.hi - sqrtLower precision interval.lo) * scale precision ≤
      (bound + 2 / scale precision) * scale precision
    grind
  · cases computed

end Interval

end Problib.Analysis.Enclosure
