module

public import Problib.Analysis.Enclosure.Interval
public import Problib.Analysis.Gaussian.Dominator
import Problib.Real.Grind

/-! Certified enclosures of the exponential.

The exponential lies above its tangent line, `1 + y ≤ exp y`, and below the
reciprocal of the reflected line, `exp y ≤ 1 / (1 - y)` for `y < 1`. At
`y = x / 2^k` the two bounds differ by about `y²` relative to their size, and
squaring both `k` times, rounding down below and up above, encloses
`exp x = (exp y)^(2^k)`. Each rounded squaring at most doubles the relative gap
and adds two grid steps, so for `x ≥ 0` with `k = p + 2 bits x + 3` halvings and
a grid of `p + k + 3` bits the relative gap ends below `2^-p`. A negative
argument inverts the enclosure of its reflection, which keeps the relative gap.

An interval's enclosure takes the lower bound at its lower endpoint and the
upper bound at its upper endpoint, since the exponential increases, and rounds
them outward to the grid `2^-p`. Its width is at most `exp hi` times the input
width plus `2^-p`, plus two grid steps.
-/

set_option autoImplicit false

namespace Problib.Analysis.Enclosure

open Problib.Real.Construction
open Problib.Real.Construction.Dedekind

/-! ### Dyadic facts -/

public theorem scale_add (first second : Nat) :
    scale (first + second) = scale first * scale second := by
  unfold scale
  rw [Nat.pow_add, Rat.natCast_mul]

public theorem scale_zero : scale 0 = 1 := rfl

public theorem scale_succ (precision : Nat) : scale (precision + 1) = scale precision * 2 := by
  unfold scale
  rw [Nat.pow_succ, Rat.natCast_mul]
  rfl

public theorem one_le_scale (precision : Nat) : 1 ≤ scale precision := by
  have cast := Rat.natCast_le_natCast.mpr (Nat.one_le_two_pow (n := precision))
  exact cast

private theorem scale_ne_zero (precision : Nat) : scale precision ≠ 0 :=
  Rat.ne_of_gt (scale_positive precision)

/-- One grid step is nonnegative. -/
public theorem step_nonnegative (precision : Nat) : 0 ≤ 1 / scale precision :=
  (le_div_iff_mul_le (scale_positive precision)).mpr (by rw [Rat.zero_mul]; decide)

/-- One grid step is at most one. -/
public theorem step_le_one (precision : Nat) : 1 / scale precision ≤ 1 :=
  (div_le_iff_le_mul (scale_positive precision)).mpr (by
    rw [Rat.one_mul]
    exact one_le_scale precision)

/-- The grid step at precision `n + 3` is at most an eighth. -/
public theorem step_le_eighth (precision : Nat) : 1 / scale (precision + 3) ≤ 1 / 8 := by
  apply (div_le_iff_le_mul (scale_positive _)).mpr
  rw [scale_add]
  have large := one_le_scale precision
  show (1 : Rat) ≤ 1 / 8 * (scale precision * 8)
  grind

/-- Rounding down keeps a value at or above one at or above one. -/
public theorem one_le_roundDown {precision : Nat} {value : Rat} (above : 1 ≤ value) :
    1 ≤ roundDown precision value := by
  have positive := scale_positive precision
  apply (le_div_iff_mul_le positive).mpr
  rw [Rat.one_mul]
  have scaled : scale precision ≤ value * scale precision := by
    have raised := Rat.mul_le_mul_of_nonneg_right above (Rat.le_of_lt positive)
    rwa [Rat.one_mul] at raised
  have floorAbove : ((2 ^ precision : Nat) : Int) ≤ (value * scale precision).floor :=
    Rat.le_floor_iff.mpr (by rw [Rat.intCast_natCast]; exact scaled)
  have cast := Rat.intCast_le_intCast.mpr floorAbove
  rw [Rat.intCast_natCast] at cast
  exact cast

public theorem one_le_roundUp {precision : Nat} {value : Rat} (above : 1 ≤ value) :
    1 ≤ roundUp precision value :=
  Rat.le_trans above (le_roundUp precision value)

private theorem one_le_mul_self {value : Rat} (above : 1 ≤ value) : 1 ≤ value * value := by
  have raised := Rat.mul_le_mul_of_nonneg_right above (Rat.le_trans (by decide) above)
  rw [Rat.one_mul] at raised
  exact Rat.le_trans above raised

/-- One more than the binary logarithm of a rational's rounded-up size, so
that `|value| < 2 ^ bits value`. -/
@[expose] public def bits (value : Rat) : Nat := Nat.log2 value.abs.ceil.toNat + 1

public theorem abs_lt_scale_bits (value : Rat) : value.abs < scale (bits value) := by
  have ceilAbove : value.abs ≤ (value.abs.ceil : Rat) := Rat.le_ceil
  have ceilNonneg : 0 ≤ value.abs.ceil :=
    Rat.intCast_nonneg.mp (Rat.le_trans Rat.abs_nonneg ceilAbove)
  have below := Nat.lt_log2_self (n := value.abs.ceil.toNat)
  have cast : ((value.abs.ceil.toNat : Nat) : Rat) <
      ((2 ^ (Nat.log2 value.abs.ceil.toNat + 1) : Nat) : Rat) :=
    Rat.natCast_lt_natCast.mpr below
  have same : ((value.abs.ceil.toNat : Nat) : Rat) = (value.abs.ceil : Rat) := by
    rw [← Rat.intCast_natCast, Int.toNat_of_nonneg ceilNonneg]
  rw [same] at cast
  show value.abs < ((2 ^ (Nat.log2 value.abs.ceil.toNat + 1) : Nat) : Rat)
  exact Rat.not_le.mp fun above => Rat.not_le.mpr cast (Rat.le_trans above ceilAbove)

/-! ### Rounded squaring -/

/-- Square `count` times, rounding down to the grid after each square. -/
@[expose] public def squareDown (precision : Nat) : Nat → Rat → Rat
  | 0, value => value
  | count + 1, value => squareDown precision count (roundDown precision (value * value))

/-- Square `count` times, rounding up to the grid after each square. -/
@[expose] public def squareUp (precision : Nat) : Nat → Rat → Rat
  | 0, value => value
  | count + 1, value => squareUp precision count (roundUp precision (value * value))

public theorem one_le_squareDown (precision : Nat) :
    ∀ (count : Nat) {value : Rat}, 1 ≤ value → 1 ≤ squareDown precision count value
  | 0, _, above => above
  | count + 1, _, above =>
      one_le_squareDown precision count (one_le_roundDown (one_le_mul_self above))

public theorem one_le_squareUp (precision : Nat) :
    ∀ (count : Nat) {value : Rat}, 1 ≤ value → 1 ≤ squareUp precision count value
  | 0, _, above => above
  | count + 1, _, above =>
      one_le_squareUp precision count (one_le_roundUp (one_le_mul_self above))

private theorem ofRat_nonnegative {value : Rat} (nonnegative : 0 ≤ value) :
    le zero (selection.ofRat value) := by
  rw [← ofRat_zero]
  exact (ofRat_le_iff 0 value).mpr nonnegative

private theorem double_scale (count : Nat) (point : selection.Carrier) :
    mul (selection.ofRat (scale count)) (add point point) =
      mul (selection.ofRat (scale (count + 1))) point := by
  rw [scale_succ, ofRat_mul]
  real_grind

/-- Squaring with downward rounding keeps a lower bound of the exponential,
doubling its exponent at each step. -/
private theorem squareDown_le_exp (precision : Nat) :
    ∀ (count : Nat) {value : Rat} {point : selection.Carrier}, 0 ≤ value →
      le (selection.ofRat value) (Problib.Analysis.exp point) →
      le (selection.ofRat (squareDown precision count value))
        (Problib.Analysis.exp (mul (selection.ofRat (scale count)) point))
  | 0, value, point, _, below => by
      show le (selection.ofRat value) _
      rw [scale_zero, ofRat_one, one_mul]
      exact below
  | count + 1, value, point, nonnegative, below => by
      show le (selection.ofRat (squareDown precision count
        (roundDown precision (value * value)))) _
      have squared : le (selection.ofRat (value * value))
          (Problib.Analysis.exp (add point point)) := by
        rw [ofRat_mul, exp_add]
        exact le_trans (mul_le_mul_nonnegative_right below (ofRat_nonnegative nonnegative))
          (mul_le_mul_nonnegative_left below (le_of_lt (exp_positive point)))
      have rounded : le (selection.ofRat (roundDown precision (value * value)))
          (Problib.Analysis.exp (add point point)) :=
        le_trans ((ofRat_le_iff _ _).mpr (roundDown_le _ _)) squared
      have next := squareDown_le_exp precision count
        (roundDown_nonnegative (Rat.mul_nonneg nonnegative nonnegative)) rounded
      rwa [double_scale] at next

/-- Squaring with upward rounding keeps an upper bound of the exponential,
doubling its exponent at each step. -/
private theorem exp_le_squareUp (precision : Nat) :
    ∀ (count : Nat) {value : Rat} {point : selection.Carrier},
      le (Problib.Analysis.exp point) (selection.ofRat value) →
      le (Problib.Analysis.exp (mul (selection.ofRat (scale count)) point))
        (selection.ofRat (squareUp precision count value))
  | 0, value, point, above => by
      show le _ (selection.ofRat value)
      rw [scale_zero, ofRat_one, one_mul]
      exact above
  | count + 1, value, point, above => by
      show le _ (selection.ofRat (squareUp precision count
        (roundUp precision (value * value))))
      have expNonnegative := le_of_lt (exp_positive point)
      have squared : le (Problib.Analysis.exp (add point point))
          (selection.ofRat (value * value)) := by
        rw [ofRat_mul, exp_add]
        exact le_trans (mul_le_mul_nonnegative_right above expNonnegative)
          (mul_le_mul_nonnegative_left above (le_trans expNonnegative above))
      have rounded : le (Problib.Analysis.exp (add point point))
          (selection.ofRat (roundUp precision (value * value))) :=
        le_trans squared ((ofRat_le_iff _ _).mpr (le_roundUp _ _))
      have next := exp_le_squareUp precision count rounded
      rwa [double_scale] at next

/-! ### Relative gaps -/

/-- One rounded squaring at most doubles a relative gap and adds two grid
steps. -/
private theorem gap_square {upper lower spread step upperNext lowerNext : Rat}
    (upperOne : 1 ≤ upper) (spreadNonnegative : 0 ≤ spread) (spreadOne : spread ≤ 1)
    (stepNonnegative : 0 ≤ step) (gap : upper * (1 - spread) ≤ lower)
    (upperAbove : upper * upper ≤ upperNext) (upperNear : upperNext ≤ upper * upper + step)
    (lowerNear : lower * lower ≤ lowerNext + step) :
    upperNext * (1 - (2 * spread + 2 * step)) ≤ lowerNext := by
  have factorNonnegative : 0 ≤ 1 - spread := by grind
  have shrunkNonnegative : 0 ≤ upper * (1 - spread) :=
    Rat.mul_nonneg (Rat.le_trans (by decide) upperOne) factorNonnegative
  have lowerNonnegative : 0 ≤ lower := Rat.le_trans shrunkNonnegative gap
  have squared : upper * (1 - spread) * (upper * (1 - spread)) ≤ lower * lower :=
    Rat.le_trans (Rat.mul_le_mul_of_nonneg_right gap shrunkNonnegative)
      (Rat.mul_le_mul_of_nonneg_left gap lowerNonnegative)
  have nextOne : 1 ≤ upperNext := Rat.le_trans (one_le_mul_self upperOne) upperAbove
  have spreadSquare := Rat.mul_nonneg spreadNonnegative spreadNonnegative
  have spreadSquareBelow : spread * spread ≤ spread * 1 :=
    Rat.mul_le_mul_of_nonneg_left spreadOne spreadNonnegative
  have factorSquare := Rat.mul_nonneg factorNonnegative factorNonnegative
  have doubled : upperNext * (1 - 2 * spread) ≤
      upperNext * ((1 - spread) * (1 - spread)) :=
    Rat.mul_le_mul_of_nonneg_left (by grind) (Rat.le_trans (by decide) nextOne)
  have rounded : upperNext * ((1 - spread) * (1 - spread)) ≤
      (upper * upper + step) * ((1 - spread) * (1 - spread)) :=
    Rat.mul_le_mul_of_nonneg_right upperNear factorSquare
  have stepShrunk : step * ((1 - spread) * (1 - spread)) ≤ step * 1 :=
    Rat.mul_le_mul_of_nonneg_left (by grind) stepNonnegative
  have stepGrown : step * 1 ≤ step * upperNext :=
    Rat.mul_le_mul_of_nonneg_left nextOne stepNonnegative
  grind

/-- Rounded squaring chains keep a relative gap that doubles per step. -/
private theorem chain_gap (precision : Nat) :
    ∀ (count : Nat) {upper lower spread : Rat}, 1 ≤ upper → 0 ≤ spread →
      scale count * (spread + 2 * (1 / scale precision)) ≤ 1 →
      upper * (1 - spread) ≤ lower →
      squareUp precision count upper *
          (1 - scale count * (spread + 2 * (1 / scale precision))) ≤
        squareDown precision count lower
  | 0, upper, lower, spread, upperOne, _, _, gap => by
      show upper * (1 - scale 0 * (spread + 2 * (1 / scale precision))) ≤ lower
      have stepNonnegative := step_nonnegative precision
      have shrunk := Rat.mul_le_mul_of_nonneg_left
        (show 1 - scale 0 * (spread + 2 * (1 / scale precision)) ≤ 1 - spread by
          rw [scale_zero]; grind)
        (Rat.le_trans (by decide) upperOne)
      exact Rat.le_trans shrunk gap
  | count + 1, upper, lower, spread, upperOne, spreadNonnegative, bounded, gap => by
      show squareUp precision count (roundUp precision (upper * upper)) * _ ≤
        squareDown precision count (roundDown precision (lower * lower))
      have stepNonnegative := step_nonnegative precision
      have countOne := one_le_scale count
      rw [scale_succ] at bounded
      have spreadOne : spread ≤ 1 := by
        have grown : spread + 2 * (1 / scale precision) ≤
            scale count * 2 * (spread + 2 * (1 / scale precision)) := by
          have := Rat.mul_le_mul_of_nonneg_right
            (show (1 : Rat) ≤ scale count * 2 by grind)
            (show 0 ≤ spread + 2 * (1 / scale precision) by grind)
          grind
        grind
      have lowerNear : lower * lower ≤
          roundDown precision (lower * lower) + 1 / scale precision := by
        have := sub_roundDown_le precision (lower * lower)
        grind
      have upperNear : roundUp precision (upper * upper) ≤
          upper * upper + 1 / scale precision := by
        have := roundUp_sub_le precision (upper * upper)
        grind
      have nextGap := gap_square upperOne spreadNonnegative spreadOne stepNonnegative gap
        (le_roundUp precision (upper * upper)) upperNear lowerNear
      have nextBounded : scale count *
          ((2 * spread + 2 * (1 / scale precision)) + 2 * (1 / scale precision)) ≤ 1 := by
        grind
      have next := chain_gap precision count (one_le_roundUp (one_le_mul_self upperOne))
        (by grind) nextBounded nextGap
      have same : scale count *
          ((2 * spread + 2 * (1 / scale precision)) + 2 * (1 / scale precision)) =
          scale (count + 1) * (spread + 2 * (1 / scale precision)) := by
        rw [scale_succ]
        grind
      rwa [same] at next

/-- The rounded tangent bounds at a small nonnegative point have relative gap
at most its square plus two grid steps. -/
private theorem initial_gap {point step low high : Rat} (nonnegative : 0 ≤ point)
    (small : point ≤ 1 / 2) (stepNonnegative : 0 ≤ step) (stepSmall : step ≤ 1 / 4)
    (lowAbove : 1 + point ≤ low + step) (highBelow : high ≤ 1 / (1 - point) + step) :
    high * (1 - (point * point + 2 * step)) ≤ low := by
  have gapPositive : 0 < 1 - point := by grind
  have reciprocal : 1 / (1 - point) * (1 - point) = 1 := by
    rw [Rat.div_def, Rat.one_mul]
    exact Rat.inv_mul_cancel _ (by grind)
  have reciprocalOne : 1 ≤ 1 / (1 - point) :=
    (le_div_iff_mul_le gapPositive).mpr (by grind)
  have pointSquare : point * point ≤ point * (1 / 2) :=
    Rat.mul_le_mul_of_nonneg_left small nonnegative
  have factorNonnegative : 0 ≤ 1 - (point * point + 2 * step) := by grind
  have factorOne : 1 - (point * point + 2 * step) ≤ 1 := by
    have := Rat.mul_nonneg nonnegative nonnegative
    grind
  have raised := Rat.mul_le_mul_of_nonneg_right highBelow factorNonnegative
  have expanded : 1 / (1 - point) * (1 - point) * (1 + point) = 1 + point := by
    rw [reciprocal, Rat.one_mul]
  have stepShrunk := Rat.mul_le_mul_of_nonneg_left factorOne stepNonnegative
  have stepGrown := Rat.mul_le_mul_of_nonneg_left reciprocalOne stepNonnegative
  grind

/-! ### Point bounds -/

/-- The halvings that bring the tangent bounds' relative gap below
`2^-(precision + 3)`. -/
@[expose] public def expHalvings (precision : Nat) (value : Rat) : Nat :=
  precision + 2 * bits value + 3

/-- The grid of the squaring chains. -/
@[expose] public def expGrid (precision : Nat) (value : Rat) : Nat :=
  precision + expHalvings precision value + 3

/-- A lower bound of `exp value` for nonnegative `value`. -/
@[expose] public def expLowerOfNonneg (precision : Nat) (value : Rat) : Rat :=
  squareDown (expGrid precision value) (expHalvings precision value)
    (roundDown (expGrid precision value) (1 + value / scale (expHalvings precision value)))

/-- An upper bound of `exp value` for nonnegative `value`. -/
@[expose] public def expUpperOfNonneg (precision : Nat) (value : Rat) : Rat :=
  squareUp (expGrid precision value) (expHalvings precision value)
    (roundUp (expGrid precision value)
      (1 / (1 - value / scale (expHalvings precision value))))

/-- A positive rational at or below `exp value`, within relative gap `2^-p` of
`expUpper`. -/
@[expose] public def expLower (precision : Nat) (value : Rat) : Rat :=
  if 0 ≤ value then expLowerOfNonneg precision value
  else (expUpperOfNonneg precision (-value))⁻¹

/-- A rational at or above `exp value`. -/
@[expose] public def expUpper (precision : Nat) (value : Rat) : Rat :=
  if 0 ≤ value then expUpperOfNonneg precision value
  else (expLowerOfNonneg precision (-value))⁻¹


/-- `scale (first + second + 3)` splits into its factors. -/
private theorem scale_split (first second : Nat) :
    scale (first + second + 3) = scale first * scale second * 8 := by
  rw [scale_add (first + second) 3, scale_add first second]
  rfl

/-- The halved argument of a nonnegative value is at most an eighth. -/
private theorem halved_small (precision : Nat) {value : Rat} (nonnegative : 0 ≤ value) :
    value / scale (expHalvings precision value) ≤ 1 / 8 := by
  have below := abs_lt_scale_bits value
  rw [Rat.abs_of_nonneg nonnegative] at below
  have split : scale (expHalvings precision value) =
      scale (precision + bits value) * scale (bits value) * 8 := by
    unfold expHalvings
    rw [show precision + 2 * bits value + 3 = precision + bits value + bits value + 3 by omega]
    exact scale_split _ _
  apply (div_le_iff_le_mul (scale_positive _)).mpr
  rw [split]
  have large := one_le_scale (precision + bits value)
  have bitsPositive := scale_positive (bits value)
  have grown : 1 * scale (bits value) ≤ scale (precision + bits value) * scale (bits value) :=
    Rat.mul_le_mul_of_nonneg_right large (Rat.le_of_lt bitsPositive)
  grind

/-- The spread a squaring chain ends with, written in the scales it is built
from, is at most one grid step of the target precision. -/
private theorem spread_bound {value halving grid precisionScale bitsScale : Rat}
    (nonnegative : 0 ≤ value) (below : value < bitsScale) (precisionPositive : 0 < precisionScale)
    (bitsPositive : 0 < bitsScale)
    (halvingSplit : halving = precisionScale * (bitsScale * bitsScale) * 8)
    (gridSplit : grid = precisionScale * halving * 8) :
    halving * (value / halving * (value / halving) + 2 * (1 / grid) + 2 * (1 / grid)) ≤
      1 / precisionScale := by
  have halvingPositive : 0 < halving := by
    rw [halvingSplit]
    exact Rat.mul_pos (Rat.mul_pos precisionPositive (Rat.mul_pos bitsPositive bitsPositive))
      (by decide)
  have halvingNonzero := Rat.ne_of_gt halvingPositive
  have precisionNonzero := Rat.ne_of_gt precisionPositive
  have square : halving * (value / halving * (value / halving)) = value * value / halving := by
    rw [← Rat.mul_assoc, show halving * (value / halving) = value by
      rw [Rat.mul_comm]
      exact Rat.div_mul_cancel halvingNonzero]
    rw [Rat.div_def, Rat.div_def, Rat.mul_assoc]
  have squareBelow : value * value ≤ bitsScale * bitsScale :=
    Rat.le_trans (Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt below) nonnegative)
      (Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt below) (Rat.le_of_lt bitsPositive))
  have reciprocal : 1 / precisionScale * precisionScale = 1 := by
    rw [Rat.div_def, Rat.one_mul]
    exact Rat.inv_mul_cancel precisionScale precisionNonzero
  have squareBound : value * value / halving ≤ 1 / 8 * (1 / precisionScale) := by
    apply (div_le_iff_le_mul halvingPositive).mpr
    have product : 1 / 8 * (1 / precisionScale) * halving = bitsScale * bitsScale := by
      rw [halvingSplit]
      rw [show 1 / 8 * (1 / precisionScale) * (precisionScale * (bitsScale * bitsScale) * 8) =
          (1 / precisionScale * precisionScale) * (bitsScale * bitsScale) by grind,
        reciprocal, Rat.one_mul]
    rw [product]
    exact squareBelow
  have stepTerm : halving * (1 / grid) = 1 / 8 * (1 / precisionScale) := by
    rw [gridSplit, Rat.div_def, Rat.one_mul, Rat.inv_mul_rev, Rat.inv_mul_rev]
    rw [show halving * ((8 : Rat)⁻¹ * (halving⁻¹ * precisionScale⁻¹)) =
        halving * halving⁻¹ * ((8 : Rat)⁻¹ * precisionScale⁻¹) by grind,
      Rat.mul_inv_cancel halving halvingNonzero, Rat.one_mul]
    rw [show (8 : Rat)⁻¹ = 1 / 8 by decide +kernel,
      show precisionScale⁻¹ = 1 / precisionScale by rw [Rat.div_def, Rat.one_mul]]
  have expand : halving * (value / halving * (value / halving) + 2 * (1 / grid) +
      2 * (1 / grid)) = halving * (value / halving * (value / halving)) +
        4 * (halving * (1 / grid)) := by
    grind
  rw [expand, square, stepTerm]
  have inverseNonnegative : 0 ≤ 1 / precisionScale :=
    (le_div_iff_mul_le precisionPositive).mpr (by rw [Rat.zero_mul]; decide)
  grind

/-- The spread a nonnegative value's chain ends with is below `2^-precision`. -/
private theorem final_spread (precision : Nat) {value : Rat} (nonnegative : 0 ≤ value) :
    scale (expHalvings precision value) *
        (value / scale (expHalvings precision value) *
            (value / scale (expHalvings precision value)) +
          2 * (1 / scale (expGrid precision value)) +
          2 * (1 / scale (expGrid precision value))) ≤
      1 / scale precision := by
  have below := abs_lt_scale_bits value
  rw [Rat.abs_of_nonneg nonnegative] at below
  apply spread_bound nonnegative below (scale_positive precision) (scale_positive (bits value))
  · unfold expHalvings
    rw [show precision + 2 * bits value + 3 = precision + (bits value + bits value) + 3 by
      omega, scale_split, scale_add]
  · unfold expGrid
    exact scale_split _ _

/-- A nonnegative value's bounds are at least one and their relative gap is
below `2^-precision`. -/
private theorem nonneg_gap (precision : Nat) {value : Rat} (nonnegative : 0 ≤ value) :
    1 ≤ expLowerOfNonneg precision value ∧ 1 ≤ expUpperOfNonneg precision value ∧
      expUpperOfNonneg precision value * (1 - 1 / scale precision) ≤
        expLowerOfNonneg precision value := by
  have small := halved_small precision nonnegative
  have halvedNonnegative : 0 ≤ value / scale (expHalvings precision value) :=
    (le_div_iff_mul_le (scale_positive _)).mpr (by rw [Rat.zero_mul]; exact nonnegative)
  have stepNonnegative := step_nonnegative (expGrid precision value)
  have stepSmall : 1 / scale (expGrid precision value) ≤ 1 / 4 :=
    Rat.le_trans (step_le_eighth (precision + expHalvings precision value)) (by decide +kernel)
  have reciprocalOne : 1 ≤ 1 / (1 - value / scale (expHalvings precision value)) :=
    (le_div_iff_mul_le (by grind)).mpr (by grind)
  have lowStart : 1 ≤ roundDown (expGrid precision value)
      (1 + value / scale (expHalvings precision value)) :=
    one_le_roundDown (by grind)
  have highStart : 1 ≤ roundUp (expGrid precision value)
      (1 / (1 - value / scale (expHalvings precision value))) :=
    one_le_roundUp reciprocalOne
  have lowAbove : 1 + value / scale (expHalvings precision value) ≤
      roundDown (expGrid precision value) (1 + value / scale (expHalvings precision value)) +
        1 / scale (expGrid precision value) := by
    have := sub_roundDown_le (expGrid precision value)
      (1 + value / scale (expHalvings precision value))
    grind
  have highBelow : roundUp (expGrid precision value)
      (1 / (1 - value / scale (expHalvings precision value))) ≤
      1 / (1 - value / scale (expHalvings precision value)) +
        1 / scale (expGrid precision value) := by
    have := roundUp_sub_le (expGrid precision value)
      (1 / (1 - value / scale (expHalvings precision value)))
    grind
  have startGap := initial_gap halvedNonnegative (by grind) stepNonnegative stepSmall
    lowAbove highBelow
  have spread := final_spread precision nonnegative
  have chain := chain_gap (expGrid precision value) (expHalvings precision value) highStart
    (by have := Rat.mul_nonneg halvedNonnegative halvedNonnegative; grind)
    (Rat.le_trans spread (step_le_one precision)) startGap
  have upperOne : 1 ≤ expUpperOfNonneg precision value := one_le_squareUp _ _ highStart
  refine ⟨one_le_squareDown _ _ lowStart, upperOne, ?_⟩
  have upperNonnegative : 0 ≤ expUpperOfNonneg precision value :=
    Rat.le_trans (by decide) upperOne
  exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_left (by grind) upperNonnegative) chain

/-! ### Containment of point values -/

/-- The tangent line at zero lies below the exponential. -/
private theorem tangent_le (point : Rat) :
    le (selection.ofRat (1 + point)) (Problib.Analysis.exp (selection.ofRat point)) := by
  rw [ofRat_add, ofRat_one]
  exact Gaussian.exp_tangent (selection.ofRat point)

/-- The reciprocal of the reflected tangent line lies above the exponential. -/
private theorem le_reflected {point : Rat} (below : point < 1) :
    le (Problib.Analysis.exp (selection.ofRat point)) (selection.ofRat (1 / (1 - point))) := by
  have tangent := Gaussian.exp_tangent (neg (selection.ofRat point))
  rw [exp_neg] at tangent
  have reflected : le (selection.ofRat (1 - point))
      (inverse (Problib.Analysis.exp (selection.ofRat point))) := by
    rw [ofRat_sub, ofRat_one, sub_eq_add_neg]
    exact tangent
  have positive : lt zero (selection.ofRat (1 - point)) := by
    rw [← ofRat_zero]
    exact (ofRat_lt_iff _ _).mpr (by grind)
  have inverted := inverse_le_inverse_of_positive positive reflected
  rw [inverse_inverse, ← ofRat_inverse] at inverted
  rw [show (1 : Rat) / (1 - point) = (1 - point)⁻¹ by rw [Rat.div_def, Rat.one_mul]]
  exact inverted

private theorem halving_cancel (precision : Nat) (value : Rat) :
    scale (expHalvings precision value) * (value / scale (expHalvings precision value)) =
      value := by
  rw [Rat.mul_comm]
  exact Rat.div_mul_cancel (scale_ne_zero _)

private theorem expLowerOfNonneg_le (precision : Nat) {value : Rat} (nonnegative : 0 ≤ value) :
    le (selection.ofRat (expLowerOfNonneg precision value))
      (Problib.Analysis.exp (selection.ofRat value)) := by
  have halvedNonnegative : 0 ≤ value / scale (expHalvings precision value) :=
    (le_div_iff_mul_le (scale_positive _)).mpr (by rw [Rat.zero_mul]; exact nonnegative)
  have start : le (selection.ofRat (roundDown (expGrid precision value)
      (1 + value / scale (expHalvings precision value))))
      (Problib.Analysis.exp (selection.ofRat (value / scale (expHalvings precision value)))) :=
    le_trans ((ofRat_le_iff _ _).mpr (roundDown_le _ _)) (tangent_le _)
  have chain := squareDown_le_exp (expGrid precision value) (expHalvings precision value)
    (roundDown_nonnegative (by grind)) start
  rw [← ofRat_mul, halving_cancel] at chain
  exact chain

private theorem exp_le_expUpperOfNonneg (precision : Nat) {value : Rat}
    (nonnegative : 0 ≤ value) :
    le (Problib.Analysis.exp (selection.ofRat value))
      (selection.ofRat (expUpperOfNonneg precision value)) := by
  have small := halved_small precision nonnegative
  have start : le
      (Problib.Analysis.exp (selection.ofRat (value / scale (expHalvings precision value))))
      (selection.ofRat (roundUp (expGrid precision value)
        (1 / (1 - value / scale (expHalvings precision value))))) :=
    le_trans (le_reflected (by grind)) ((ofRat_le_iff _ _).mpr (le_roundUp _ _))
  have chain := exp_le_squareUp (expGrid precision value) (expHalvings precision value) start
  rw [← ofRat_mul, halving_cancel] at chain
  exact chain

public theorem expLower_le (precision : Nat) (value : Rat) :
    le (selection.ofRat (expLower precision value))
      (Problib.Analysis.exp (selection.ofRat value)) := by
  unfold expLower
  split
  · rename_i nonnegative
    exact expLowerOfNonneg_le precision nonnegative
  · rename_i negative
    have reflected : 0 ≤ -value := by grind
    have above := exp_le_expUpperOfNonneg precision reflected
    have inverted := inverse_le_inverse_of_positive (exp_positive _) above
    rw [← ofRat_inverse, ← exp_neg, ← ofRat_neg, Rat.neg_neg] at inverted
    exact inverted

public theorem le_expUpper (precision : Nat) (value : Rat) :
    le (Problib.Analysis.exp (selection.ofRat value))
      (selection.ofRat (expUpper precision value)) := by
  unfold expUpper
  split
  · rename_i nonnegative
    exact exp_le_expUpperOfNonneg precision nonnegative
  · rename_i negative
    have reflected : 0 ≤ -value := by grind
    have below := expLowerOfNonneg_le precision reflected
    have lowerOne := (nonneg_gap precision reflected).1
    have positive : lt zero (selection.ofRat (expLowerOfNonneg precision (-value))) := by
      rw [← ofRat_zero]
      exact (ofRat_lt_iff _ _).mpr (by grind)
    have inverted := inverse_le_inverse_of_positive positive below
    rw [← ofRat_inverse, ← exp_neg, ← ofRat_neg, Rat.neg_neg] at inverted
    exact inverted

public theorem expLower_positive (precision : Nat) (value : Rat) :
    0 < expLower precision value := by
  unfold expLower
  split
  · rename_i nonnegative
    have := (nonneg_gap precision nonnegative).1
    grind
  · rename_i negative
    have := (nonneg_gap precision (show 0 ≤ -value by grind)).2.1
    exact Rat.inv_pos.mpr (by grind)

public theorem expLower_le_expUpper (precision : Nat) {first second : Rat}
    (ordered : first ≤ second) : expLower precision first ≤ expUpper precision second :=
  (ofRat_le_iff _ _).mp (le_trans (expLower_le precision first)
    (le_trans (exp_monotone ((ofRat_le_iff _ _).mpr ordered)) (le_expUpper precision second)))

/-- The upper bound exceeds the lower bound by a relative gap below
`2^-precision`. -/
public theorem expUpper_gap (precision : Nat) (value : Rat) :
    expUpper precision value * (1 - 1 / scale precision) ≤ expLower precision value := by
  unfold expUpper expLower
  split
  · rename_i nonnegative
    exact (nonneg_gap precision nonnegative).2.2
  · rename_i negative
    obtain ⟨lowerOne, upperOne, gap⟩ := nonneg_gap precision (show 0 ≤ -value by grind)
    have lowerPositive : 0 < expLowerOfNonneg precision (-value) := by grind
    have upperPositive : 0 < expUpperOfNonneg precision (-value) := by grind
    rw [show (expUpperOfNonneg precision (-value))⁻¹ =
        1 / expUpperOfNonneg precision (-value) by rw [Rat.div_def, Rat.one_mul]]
    apply (le_div_iff_mul_le upperPositive).mpr
    have scaled := Rat.mul_le_mul_of_nonneg_left gap
      (Rat.le_of_lt (Rat.inv_pos.mpr lowerPositive))
    rw [Rat.inv_mul_cancel _ (Rat.ne_of_gt lowerPositive)] at scaled
    rw [show (expLowerOfNonneg precision (-value))⁻¹ * (1 - 1 / scale precision) *
        expUpperOfNonneg precision (-value) =
        (expLowerOfNonneg precision (-value))⁻¹ *
          (expUpperOfNonneg precision (-value) * (1 - 1 / scale precision)) by grind]
    exact scaled

/-- The exponential's increment is at most the exponent's increment times the
larger value. -/
private theorem exp_increment_le (first second : selection.Carrier) :
    le (sub (Problib.Analysis.exp second) (Problib.Analysis.exp first))
      (mul (Problib.Analysis.exp second) (sub second first)) := by
  have tangent := mul_le_mul_nonnegative_left (Gaussian.exp_tangent (sub first second))
    (le_of_lt (exp_positive second))
  rw [← exp_add, add_sub_cancel] at tangent
  real_grind

/-! ### Intervals -/

namespace Interval

/-- The enclosure of the exponential over an interval: the lower bound at the
lower endpoint and the upper bound at the upper endpoint, two bits finer than
the grid `2^-precision` they are rounded out to. -/
@[expose] public def exp (precision : Nat) (interval : Interval) : Interval where
  lo := roundDown precision (expLower (precision + 2) interval.lo)
  hi := roundUp precision (expUpper (precision + 2) interval.hi)
  ordered := Rat.le_trans (roundDown_le _ _)
    (Rat.le_trans (expLower_le_expUpper _ interval.ordered) (le_roundUp _ _))

/-- The exponential's enclosure contains the exponential of every member. -/
public theorem Contains.exp {interval : Interval} {value : selection.Carrier}
    (member : interval.Contains value) (precision : Nat) :
    (interval.exp precision).Contains (Problib.Analysis.exp value) := by
  constructor
  · show le (selection.ofRat (roundDown precision (expLower (precision + 2) interval.lo))) _
    exact le_trans ((ofRat_le_iff _ _).mpr (roundDown_le _ _))
      (le_trans (expLower_le _ _) (exp_monotone member.1))
  · show le _ (selection.ofRat (roundUp precision (expUpper (precision + 2) interval.hi)))
    exact le_trans (exp_monotone member.2)
      (le_trans (le_expUpper _ _) ((ofRat_le_iff _ _).mpr (le_roundUp _ _)))

/-- The exponential's enclosure is at most `exp hi` times the input width plus
one grid step, plus two grid steps of rounding. A point's enclosure shrinks
like `(exp x + 2) 2^-precision`. -/
public theorem width_exp_le (precision : Nat) (interval : Interval) :
    le (selection.ofRat (interval.exp precision).width)
      (Dedekind.add (Dedekind.mul (Problib.Analysis.exp (selection.ofRat interval.hi))
          (selection.ofRat (interval.width + 1 / scale precision)))
        (selection.ofRat (2 / scale precision))) := by
  have positive := scale_positive precision
  have stepNonnegative := step_nonnegative precision
  -- rational facts
  have fineStep : 1 / scale (precision + 2) = 1 / scale precision * (1 / 4) := by
    rw [scale_add precision 2, Rat.div_def, Rat.div_def, Rat.div_def, Rat.one_mul, Rat.one_mul,
      Rat.one_mul, Rat.inv_mul_rev, Rat.mul_comm]
    rfl
  have fineSmall : 1 / scale (precision + 2) ≤ 1 / 2 := by
    rw [fineStep]
    have := step_le_one precision
    grind
  have fineTriple : 3 * (1 / scale (precision + 2)) ≤ 1 / scale precision := by
    rw [fineStep]
    grind
  have rounding : (interval.exp precision).width ≤
      expUpper (precision + 2) interval.hi - expLower (precision + 2) interval.lo +
        2 / scale precision := by
    have up := roundUp_sub_le precision (expUpper (precision + 2) interval.hi)
    have down := sub_roundDown_le precision (expLower (precision + 2) interval.lo)
    have twice : (2 : Rat) / scale precision = 1 / scale precision + 1 / scale precision := by
      rw [Rat.div_def, Rat.div_def, ← Rat.add_mul,
        show (1 : Rat) + 1 = 2 by decide +kernel]
    show roundUp precision (expUpper (precision + 2) interval.hi) -
      roundDown precision (expLower (precision + 2) interval.lo) ≤ _
    rw [twice]
    grind
  have upperGap := expUpper_gap (precision + 2) interval.hi
  have lowerGap := expUpper_gap (precision + 2) interval.lo
  have upperPositive : 0 < expUpper (precision + 2) interval.hi := by
    have := expLower_positive (precision + 2) interval.hi
    have := expLower_le_expUpper (precision + 2) (Rat.le_refl (a := interval.hi))
    grind
  have upperGapReal : le (Dedekind.mul (selection.ofRat (expUpper (precision + 2) interval.hi))
      (Dedekind.sub one (selection.ofRat (1 / scale (precision + 2)))))
      (selection.ofRat (expLower (precision + 2) interval.hi)) := by
    have := (ofRat_le_iff _ _).mpr upperGap
    rwa [ofRat_mul, ofRat_sub, ofRat_one] at this
  have lowerGapReal : le (Dedekind.mul (selection.ofRat (expUpper (precision + 2) interval.lo))
      (Dedekind.sub one (selection.ofRat (1 / scale (precision + 2)))))
      (selection.ofRat (expLower (precision + 2) interval.lo)) := by
    have := (ofRat_le_iff _ _).mpr lowerGap
    rwa [ofRat_mul, ofRat_sub, ofRat_one] at this
  have highLower := expLower_le (precision + 2) interval.hi
  have lowUpper := le_expUpper (precision + 2) interval.lo
  have monotone := exp_monotone ((ofRat_le_iff _ _).mpr interval.ordered)
  have increment := exp_increment_le (selection.ofRat interval.lo)
    (selection.ofRat interval.hi)
  have expNonnegative := le_of_lt (exp_positive (selection.ofRat interval.hi))
  have factorNonnegative :
      le zero (Dedekind.sub one (selection.ofRat (1 / scale (precision + 2)))) := by
    have := (ofRat_le_iff _ _).mpr (show 0 ≤ 1 - 1 / scale (precision + 2) by grind)
    rwa [ofRat_zero, ofRat_sub, ofRat_one] at this
  have lowShrunk := mul_le_mul_nonnegative_right lowUpper factorNonnegative
  have half : le one
      (Dedekind.mul (selection.ofRat 2)
        (Dedekind.sub one (selection.ofRat (1 / scale (precision + 2))))) := by
    have := (ofRat_le_iff _ _).mpr
      (show (1 : Rat) ≤ 2 * (1 - 1 / scale (precision + 2)) by grind)
    rwa [ofRat_one, ofRat_mul, ofRat_sub, ofRat_one] at this
  have upperNonnegative : le zero (selection.ofRat (expUpper (precision + 2) interval.hi)) :=
    ofRat_nonnegative (Rat.le_of_lt upperPositive)
  have halfScaled := mul_le_mul_nonnegative_left half upperNonnegative
  have upperBelow : le (selection.ofRat (expUpper (precision + 2) interval.hi))
      (Dedekind.mul (selection.ofRat 2) (Problib.Analysis.exp (selection.ofRat interval.hi))) := by
    real_grind
  have fineNonnegative : le zero (selection.ofRat (1 / scale (precision + 2))) :=
    ofRat_nonnegative (step_nonnegative _)
  have upperStep := mul_le_mul_nonnegative_right upperBelow fineNonnegative
  have lowerStep := mul_le_mul_nonnegative_right monotone fineNonnegative
  have tripleReal :
      le (Dedekind.mul (selection.ofRat 3) (selection.ofRat (1 / scale (precision + 2))))
      (selection.ofRat (1 / scale precision)) := by
    have := (ofRat_le_iff _ _).mpr fineTriple
    rwa [ofRat_mul] at this
  have tripleScaled := mul_le_mul_nonnegative_left tripleReal expNonnegative
  have roundingReal := (ofRat_le_iff _ _).mpr rounding
  rw [ofRat_add, ofRat_sub] at roundingReal
  rw [show interval.width = interval.hi - interval.lo from rfl, ofRat_add, ofRat_sub]
  real_grind

end Interval

end Problib.Analysis.Enclosure
