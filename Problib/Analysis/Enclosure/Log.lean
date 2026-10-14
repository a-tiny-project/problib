module

public import Problib.Analysis.Enclosure.Exp
public import Problib.Analysis.Logarithm.Derivative
import Problib.Real.Grind

/-! Certified enclosures of the logarithm.

The logarithm is the integral logarithm `logIntegral`, the inverse of the
exponential on positive reals. At any rational `g` the logarithm's increment
bounds give `g + 1 - exp g / x ≤ log x ≤ g + x / exp g - 1`, and replacing
`exp g` by its rational enclosure keeps both bounds. A refinement step takes
`g` at the midpoint of an enclosure `[low, high]` of `log x`, intersects it with
the two bounds and rounds outward. The product of the two ratios
`expUpper g / x` and `x / expLower g` is the exponential's relative gap, so one
of them is within one grid step of one. The step therefore at least halves the
width, up to three grid steps, and near the logarithm the tangent bounds close
quadratically, which makes the loop stop early in practice.

The start comes from the binary logarithm `m` of the integer part of `x` or of
its reciprocal: `m / 2 ≤ log x ≤ m + 1` because `1/2 ≤ log 2 ≤ 1`. The loop's
fuel covers the start's width at the halving rate, so the point enclosure is
narrower than `2^-(p + 1)` by theorem.

An interval's enclosure needs a positive lower endpoint and refuses otherwise.
It takes the lower bound at the lower endpoint and the upper bound at the upper
endpoint, since the logarithm increases, and its width is at most
`width / lo + 3 / 2^p`, the logarithm's modulus on `[lo, hi]` plus rounding.
-/

set_option autoImplicit false

namespace Problib.Analysis.Enclosure

open Problib.Real
open Problib.Real.Construction
open Problib.Real.Construction.Dedekind
open Problib.Analysis.Logarithm

/-! ### Refinement -/

/-- The lower tangent bound of `log value` at `middle`. -/
@[expose] public def logBelow (precision : Nat) (value middle : Rat) : Rat :=
  middle + 1 - expUpper precision middle / value

/-- The upper tangent bound of `log value` at `middle`. -/
@[expose] public def logAbove (precision : Nat) (value middle : Rat) : Rat :=
  middle + value / expLower precision middle - 1

/-- One refinement of an enclosure `[low, high]` of `log value` at its
midpoint, rounded outward to the grid `2^-precision`. -/
@[expose] public def logStep (precision : Nat) (value low high : Rat) : Rat × Rat :=
  (roundDown precision (max low (logBelow precision value ((low + high) / 2))),
    roundUp precision (min high (logAbove precision value ((low + high) / 2))))

/-- Refine until the enclosure is at most `target` wide or the fuel runs out. -/
@[expose] public def logLoop (precision : Nat) (value target : Rat) :
    Nat → Rat → Rat → Rat × Rat
  | 0, low, high => (low, high)
  | fuel + 1, low, high =>
      if high - low ≤ target then (low, high)
      else
        match logStep precision value low high with
        | (nextLow, nextHigh) => logLoop precision value target fuel nextLow nextHigh

/-- A first enclosure of `log value` for positive `value`, from the binary
logarithm of the integer part of `value` or of its reciprocal. -/
@[expose] public def logStart (value : Rat) : Rat × Rat :=
  if 1 ≤ value then
    ((Nat.log2 value.floor.toNat : Rat) / 2, (Nat.log2 value.floor.toNat : Rat) + 1)
  else
    (-((Nat.log2 value⁻¹.floor.toNat : Rat) + 1), -((Nat.log2 value⁻¹.floor.toNat : Rat) / 2))

/-- An enclosure of `log value`, for positive `value`, narrower than
`2^-(precision + 1)`. -/
@[expose] public def logPoint (precision : Nat) (value : Rat) : Rat × Rat :=
  logLoop (precision + 5) value (1 / scale (precision + 1))
    (precision + bits ((logStart value).2 - (logStart value).1) + 3)
    (logStart value).1 (logStart value).2

/-! ### Real bounds -/

private theorem ofRat_nonnegative {value : Rat} (nonnegative : 0 ≤ value) :
    le zero (selection.ofRat value) := by
  rw [← ofRat_zero]
  exact (ofRat_le_iff 0 value).mpr nonnegative

private theorem ofRat_positive {value : Rat} (positive : 0 < value) :
    lt zero (selection.ofRat value) := by
  rw [← ofRat_zero]
  exact (ofRat_lt_iff 0 value).mpr positive

/-- The logarithm lies above the lower tangent bound at every midpoint. -/
public theorem logBelow_le (precision : Nat) {value : Rat} (positive : 0 < value)
    (middle : Rat) :
    le (selection.ofRat (logBelow precision value middle))
      (logIntegral (selection.ofRat value)) := by
  have tangent := Gaussian.exp_tangent
    (sub (selection.ofRat middle) (logIntegral (selection.ofRat value)))
  rw [sub_eq_add_neg, exp_add, exp_neg, exp_log _ (ofRat_positive positive),
    ← ofRat_inverse] at tangent
  have upper := mul_le_mul_nonnegative_right (le_expUpper precision middle)
    (ofRat_nonnegative (Rat.le_of_lt (Rat.inv_pos.mpr positive)))
  unfold logBelow
  rw [Rat.div_def, ofRat_sub, ofRat_add, ofRat_one, ofRat_mul]
  real_grind

/-- The logarithm lies below the upper tangent bound at every midpoint. -/
public theorem le_logAbove (precision : Nat) {value : Rat} (positive : 0 < value)
    (middle : Rat) :
    le (logIntegral (selection.ofRat value))
      (selection.ofRat (logAbove precision value middle)) := by
  have tangent := Gaussian.exp_tangent
    (sub (logIntegral (selection.ofRat value)) (selection.ofRat middle))
  rw [sub_eq_add_neg, exp_add, exp_neg, exp_log _ (ofRat_positive positive)] at tangent
  have inverted := inverse_le_inverse_of_positive
    (ofRat_positive (expLower_positive precision middle)) (expLower_le precision middle)
  rw [← ofRat_inverse] at inverted
  have scaled := mul_le_mul_nonnegative_left inverted (le_of_lt (ofRat_positive positive))
  unfold logAbove
  rw [Rat.div_def, ofRat_sub, ofRat_add, ofRat_one, ofRat_mul]
  real_grind

/-- A refinement step keeps an enclosure. -/
private theorem logStep_contains (precision : Nat) {value : Rat} (positive : 0 < value)
    {low high : Rat} (below : le (selection.ofRat low) (logIntegral (selection.ofRat value)))
    (above : le (logIntegral (selection.ofRat value)) (selection.ofRat high)) :
    le (selection.ofRat (logStep precision value low high).1)
        (logIntegral (selection.ofRat value)) ∧
      le (logIntegral (selection.ofRat value))
        (selection.ofRat (logStep precision value low high).2) := by
  constructor
  · show le (selection.ofRat (roundDown precision
      (max low (logBelow precision value ((low + high) / 2))))) _
    refine le_trans ((ofRat_le_iff _ _).mpr (roundDown_le _ _)) ?_
    rw [Rat.max_def]
    split
    · exact logBelow_le precision positive _
    · exact below
  · show le _ (selection.ofRat (roundUp precision
      (min high (logAbove precision value ((low + high) / 2)))))
    refine le_trans ?_ ((ofRat_le_iff _ _).mpr (le_roundUp _ _))
    rw [Rat.min_def]
    split
    · exact above
    · exact le_logAbove precision positive _

/-- The refinement loop keeps an enclosure. -/
private theorem logLoop_contains (precision : Nat) {value : Rat} (positive : 0 < value)
    (target : Rat) :
    ∀ (fuel : Nat) {low high : Rat},
      le (selection.ofRat low) (logIntegral (selection.ofRat value)) →
      le (logIntegral (selection.ofRat value)) (selection.ofRat high) →
      le (selection.ofRat (logLoop precision value target fuel low high).1)
          (logIntegral (selection.ofRat value)) ∧
        le (logIntegral (selection.ofRat value))
          (selection.ofRat (logLoop precision value target fuel low high).2)
  | 0, _, _, below, above => ⟨below, above⟩
  | fuel + 1, low, high, below, above => by
      simp only [logLoop]
      split
      · exact ⟨below, above⟩
      · have step := logStep_contains precision positive below above
        generalize logStep precision value low high = next at step ⊢
        obtain ⟨nextLow, nextHigh⟩ := next
        exact logLoop_contains precision positive target fuel step.1 step.2

/-! ### Halving -/

/-- Two ratios whose product is at most the inverse of a relative gap below
one half cannot both exceed one by more than the gap. -/
private theorem gap_split {upper lower value step : Rat} (positive : 0 < value)
    (lowerPositive : 0 < lower) (stepNonnegative : 0 ≤ step) (small : step ≤ 1 / 2)
    (gap : upper * (1 - step) ≤ lower) :
    upper / value ≤ 1 + step ∨ value / lower ≤ 1 + step := by
  by_cases first : upper / value ≤ 1 + step
  · exact Or.inl first
  · right
    apply Rat.not_lt.mp
    intro second
    have firstAbove := Rat.not_le.mp first
    have firstCancel : upper / value * value = upper :=
      Rat.div_mul_cancel (Rat.ne_of_gt positive)
    have secondCancel : value / lower * lower = value :=
      Rat.div_mul_cancel (Rat.ne_of_gt lowerPositive)
    have product : upper / value * (value / lower) * lower = upper := by
      rw [Rat.mul_assoc, secondCancel, firstCancel]
    have bounded : upper / value * (value / lower) * (1 - step) ≤ 1 := by
      apply Rat.le_of_mul_le_mul_right _ lowerPositive
      rw [show upper / value * (value / lower) * (1 - step) * lower =
          upper / value * (value / lower) * lower * (1 - step) by grind, product, Rat.one_mul]
      exact gap
    have firstProduct := Rat.mul_pos (show 0 < upper / value - (1 + step) by grind)
      (show 0 < value / lower by grind)
    have secondProduct := Rat.mul_pos (show 0 < 1 + step by grind)
      (show 0 < value / lower - (1 + step) by grind)
    have squared := Rat.mul_pos
      (show 0 < upper / value * (value / lower) - (1 + step) * (1 + step) by grind)
      (show 0 < 1 - step by grind)
    have stepSquare := Rat.mul_le_mul_of_nonneg_left small stepNonnegative
    have stepCube := Rat.mul_le_mul_of_nonneg_left stepSquare stepNonnegative
    grind

/-- One refinement at most halves the width, up to three grid steps. -/
private theorem logStep_width (precision : Nat) {value : Rat} (positive : 0 < value)
    (small : 1 / scale precision ≤ 1 / 2) (low high : Rat) :
    (logStep precision value low high).2 - (logStep precision value low high).1 ≤
      (high - low) / 2 + 3 * (1 / scale precision) := by
  have stepNonnegative := step_nonnegative precision
  have split := gap_split positive (expLower_positive precision ((low + high) / 2))
    stepNonnegative small (expUpper_gap precision ((low + high) / 2))
  have upperRounding := roundUp_sub_le precision
    (min high (logAbove precision value ((low + high) / 2)))
  have lowerRounding := sub_roundDown_le precision
    (max low (logBelow precision value ((low + high) / 2)))
  show roundUp precision (min high (logAbove precision value ((low + high) / 2))) -
      roundDown precision (max low (logBelow precision value ((low + high) / 2))) ≤ _
  unfold logAbove logBelow at *
  grind

/-- With fuel to halve the width down to `base`, the loop ends at most
`target` wide. -/
private theorem logLoop_width (precision : Nat) {value : Rat} (positive : 0 < value)
    (small : 1 / scale precision ≤ 1 / 2) {target base : Rat}
    (fits : base + 6 * (1 / scale precision) ≤ target) :
    ∀ (fuel : Nat) (low high : Rat),
      high - low ≤ scale fuel * base + 6 * (1 / scale precision) →
      (logLoop precision value target fuel low high).2 -
          (logLoop precision value target fuel low high).1 ≤ target
  | 0, low, high, wide => by
      show high - low ≤ target
      rw [scale_zero, Rat.one_mul] at wide
      exact Rat.le_trans wide fits
  | fuel + 1, low, high, wide => by
      simp only [logLoop]
      split
      · rename_i close
        exact close
      · have step := logStep_width precision positive small low high
        generalize logStep precision value low high = next at step ⊢
        obtain ⟨nextLow, nextHigh⟩ := next
        apply logLoop_width precision positive small fits fuel nextLow nextHigh
        rw [scale_succ] at wide
        dsimp only at step
        grind

/-! ### The start -/

/-- One grid step at a finer precision is a fraction of a coarser one. -/
public theorem step_add (precision extra : Nat) :
    1 / scale (precision + extra) = 1 / scale precision * (1 / scale extra) := by
  rw [scale_add, Rat.div_def, Rat.div_def, Rat.div_def, Rat.one_mul, Rat.one_mul, Rat.one_mul,
    Rat.inv_mul_rev, Rat.mul_comm]

private theorem two_eq : add one one = selection.ofRat 2 := by
  rw [← ofRat_one, ← ofRat_add]
  exact congrArg selection.ofRat (by decide +kernel)

private theorem powerTwo_eq (count : Nat) : powerTwo count = selection.ofRat (scale count) := by
  induction count with
  | zero =>
      rw [scale_zero, ofRat_one]
      rfl
  | succ count previous =>
      rw [powerTwo, previous, scale_succ, ofRat_mul, two_eq]

private theorem log_scale (count : Nat) :
    logIntegral (selection.ofRat (scale count)) =
      mul (selection.ofRat (count : Rat)) (logIntegral (selection.ofRat 2)) := by
  rw [← powerTwo_eq, log_powerTwo, two_eq]

/-- `1/2 ≤ log 2 ≤ 1`, from the reciprocal rectangles over `[1, 2]`. -/
private theorem log_two_bounds :
    le (selection.ofRat (1 / 2)) (logIntegral (selection.ofRat 2)) ∧
      le (logIntegral (selection.ofRat 2)) one := by
  have bounds := log_increment_bounds (ofRat_positive (show (0 : Rat) < 1 by decide +kernel))
    ((ofRat_le_iff _ _).mpr (show (1 : Rat) ≤ 2 by decide +kernel))
  rw [show logIntegral (selection.ofRat 1) = zero by rw [ofRat_one]; exact log_one, sub_zero,
    ← ofRat_sub, ← ofRat_div, ← ofRat_div] at bounds
  rw [show ((2 : Rat) - 1) / 2 = 1 / 2 by decide +kernel,
    show ((2 : Rat) - 1) / 1 = 1 by decide +kernel, ofRat_one] at bounds
  exact bounds

private theorem log_bounds_of_one_le {value : Rat} (above : 1 ≤ value) :
    le (selection.ofRat ((Nat.log2 value.floor.toNat : Rat) / 2))
        (logIntegral (selection.ofRat value)) ∧
      le (logIntegral (selection.ofRat value))
        (selection.ofRat ((Nat.log2 value.floor.toNat : Rat) + 1)) := by
  have floorOne : (1 : Int) ≤ value.floor := Rat.le_floor_iff.mpr (by simpa using above)
  have nonzero : value.floor.toNat ≠ 0 := by omega
  have cast : ((value.floor.toNat : Nat) : Rat) = (value.floor : Rat) := by
    rw [← Rat.intCast_natCast, Int.toNat_of_nonneg (by omega)]
  have floorBelow : (value.floor : Rat) ≤ value := Rat.floor_le value
  have floorAbove : value < (value.floor : Rat) + 1 := by
    have := Rat.lt_floor_add_one value
    rwa [Rat.intCast_add, Rat.intCast_one] at this
  have lowPower : scale (Nat.log2 value.floor.toNat) ≤ value := by
    have := Rat.natCast_le_natCast.mpr (Nat.log2_self_le nonzero)
    rw [cast] at this
    exact Rat.le_trans this floorBelow
  have highPower : value ≤ scale (Nat.log2 value.floor.toNat + 1) := by
    have successor : value.floor.toNat + 1 ≤ 2 ^ (Nat.log2 value.floor.toNat + 1) :=
      Nat.lt_log2_self
    have := Rat.natCast_le_natCast.mpr successor
    rw [Rat.natCast_add, cast] at this
    have one : ((1 : Nat) : Rat) = 1 := rfl
    rw [one] at this
    show value ≤ ((2 ^ (Nat.log2 value.floor.toNat + 1) : Nat) : Rat)
    grind
  have valuePositive : 0 < value := by grind
  have lowLog := log_monotone _ _ (ofRat_positive (scale_positive _))
    ((ofRat_le_iff _ _).mpr lowPower)
  have highLog := log_monotone _ _ (ofRat_positive valuePositive)
    ((ofRat_le_iff _ _).mpr highPower)
  rw [log_scale] at lowLog highLog
  rw [Rat.natCast_add, show ((1 : Nat) : Rat) = 1 from rfl] at highLog
  obtain ⟨twoLow, twoHigh⟩ := log_two_bounds
  have lowScaled := mul_le_mul_nonnegative_left twoLow
    (ofRat_nonnegative (Rat.natCast_nonneg (a := Nat.log2 value.floor.toNat)))
  have highScaled := mul_le_mul_nonnegative_left twoHigh
    (ofRat_nonnegative (show 0 ≤ (Nat.log2 value.floor.toNat : Rat) + 1 by
      have := Rat.natCast_nonneg (a := Nat.log2 value.floor.toNat)
      grind))
  rw [mul_one] at highScaled
  constructor
  · rw [show (Nat.log2 value.floor.toNat : Rat) / 2 =
        (Nat.log2 value.floor.toNat : Rat) * (1 / 2) by
      rw [Rat.div_def, Rat.div_def, Rat.one_mul], ofRat_mul]
    exact le_trans lowScaled lowLog
  · exact le_trans highLog highScaled

private theorem logStart_contains {value : Rat} (positive : 0 < value) :
    le (selection.ofRat (logStart value).1) (logIntegral (selection.ofRat value)) ∧
      le (logIntegral (selection.ofRat value)) (selection.ofRat (logStart value).2) := by
  unfold logStart
  split
  · rename_i above
    exact log_bounds_of_one_le above
  · rename_i below
    have reciprocalAbove : 1 ≤ value⁻¹ := by
      have := inv_le_inv_of_positive positive (Rat.le_of_lt (Rat.not_le.mp below))
      rwa [show (1 : Rat)⁻¹ = 1 by decide +kernel] at this
    obtain ⟨lowBound, highBound⟩ := log_bounds_of_one_le reciprocalAbove
    have flip : logIntegral (selection.ofRat value) =
        neg (logIntegral (selection.ofRat value⁻¹)) := by
      rw [← log_inverse _ (ofRat_positive (Rat.inv_pos.mpr positive)), ← ofRat_inverse,
        Rat.inv_inv]
    rw [flip]
    constructor
    · show le (selection.ofRat (-((Nat.log2 value⁻¹.floor.toNat : Rat) + 1))) _
      rw [ofRat_neg]
      exact neg_le_neg_iff.mpr highBound
    · show le _ (selection.ofRat (-((Nat.log2 value⁻¹.floor.toNat : Rat) / 2)))
      rw [ofRat_neg]
      exact neg_le_neg_iff.mpr lowBound

private theorem logStart_width (value : Rat) :
    (logStart value).2 - (logStart value).1 ≤
      scale (bits ((logStart value).2 - (logStart value).1)) := by
  have below := abs_lt_scale_bits ((logStart value).2 - (logStart value).1)
  have nonnegative : 0 ≤ (logStart value).2 - (logStart value).1 := by
    unfold logStart
    split
    · have := Rat.natCast_nonneg (a := Nat.log2 value.floor.toNat)
      grind
    · have := Rat.natCast_nonneg (a := Nat.log2 value⁻¹.floor.toNat)
      grind
  rw [Rat.abs_of_nonneg nonnegative] at below
  exact Rat.le_of_lt below

/-! ### Point enclosures -/

/-- The point enclosure contains the logarithm of a positive rational. -/
public theorem logPoint_contains (precision : Nat) {value : Rat} (positive : 0 < value) :
    le (selection.ofRat (logPoint precision value).1) (logIntegral (selection.ofRat value)) ∧
      le (logIntegral (selection.ofRat value)) (selection.ofRat (logPoint precision value).2) :=
  logLoop_contains (precision + 5) positive _ _ (logStart_contains positive).1
    (logStart_contains positive).2

/-- The point enclosure of a positive rational's logarithm is at most
`2^-(precision + 1)` wide. -/
public theorem logPoint_width (precision : Nat) {value : Rat} (positive : 0 < value) :
    (logPoint precision value).2 - (logPoint precision value).1 ≤
      1 / scale (precision + 1) := by
  have small : 1 / scale (precision + 5) ≤ 1 / 2 := by
    have eighth := step_le_eighth (precision + 2)
    rw [show precision + 2 + 3 = precision + 5 from rfl] at eighth
    exact Rat.le_trans eighth (by decide +kernel)
  have stepNonnegative := step_nonnegative precision
  have fits : 1 / scale (precision + 3) + 6 * (1 / scale (precision + 5)) ≤
      1 / scale (precision + 1) := by
    rw [step_add precision 3, step_add precision 5, step_add precision 1]
    have scaleThree : scale 3 = 8 := by decide +kernel
    have scaleFive : scale 5 = 32 := by decide +kernel
    have scaleOne : scale 1 = 2 := by decide +kernel
    rw [scaleThree, scaleFive, scaleOne]
    grind
  apply logLoop_width (precision + 5) positive small fits
  have start := logStart_width value
  have split : scale (precision + bits ((logStart value).2 - (logStart value).1) + 3) *
      (1 / scale (precision + 3)) = scale (bits ((logStart value).2 - (logStart value).1)) := by
    rw [show precision + bits ((logStart value).2 - (logStart value).1) + 3 =
        bits ((logStart value).2 - (logStart value).1) + (precision + 3) by omega,
      scale_add, Rat.mul_assoc, show scale (precision + 3) * (1 / scale (precision + 3)) = 1 by
        rw [Rat.mul_comm]
        exact Rat.div_mul_cancel (Rat.ne_of_gt (scale_positive _)), Rat.mul_one]
  rw [split]
  have := step_nonnegative (precision + 5)
  grind

/-- The lower end of the point enclosure lies at or below its upper end. -/
public theorem logPoint_ordered (precision : Nat) {low high : Rat} (positive : 0 < low)
    (ordered : low ≤ high) :
    roundDown precision (logPoint (precision + 2) low).1 ≤
      roundUp precision (logPoint (precision + 2) high).2 := by
  have highPositive : 0 < high := by grind
  have chain := le_trans (logPoint_contains (precision + 2) positive).1
    (le_trans (log_monotone _ _ (ofRat_positive positive) ((ofRat_le_iff _ _).mpr ordered))
      (logPoint_contains (precision + 2) highPositive).2)
  exact Rat.le_trans (roundDown_le _ _)
    (Rat.le_trans ((ofRat_le_iff _ _).mp chain) (le_roundUp _ _))

/-! ### Intervals -/

namespace Interval

/-- The enclosure of the logarithm over an interval with a positive lower
endpoint, refused otherwise: the lower bound at the lower endpoint and the
upper bound at the upper endpoint, two bits finer than the grid
`2^-precision` they are rounded out to. -/
@[expose] public def log? (precision : Nat) (interval : Interval) : Option Interval :=
  if positive : 0 < interval.lo then
    some ⟨roundDown precision (logPoint (precision + 2) interval.lo).1,
      roundUp precision (logPoint (precision + 2) interval.hi).2,
      logPoint_ordered precision positive interval.ordered⟩
  else none

/-- The logarithm's enclosure is refused exactly when the interval reaches
zero or below. -/
public theorem log?_isSome_iff (precision : Nat) (interval : Interval) :
    (interval.log? precision).isSome = true ↔ 0 < interval.lo := by
  unfold log?
  by_cases positive : 0 < interval.lo
  · simp [positive]
  · simp [positive]

/-- The logarithm's enclosure contains the logarithm of every member. -/
public theorem Contains.log {interval result : Interval} {value : selection.Carrier}
    {precision : Nat} (computed : interval.log? precision = some result)
    (member : interval.Contains value) : result.Contains (logIntegral value) := by
  unfold log? at computed
  split at computed
  · rename_i positive
    cases computed
    have lowPositive := ofRat_positive positive
    have valuePositive := lt_of_lt_of_le lowPositive member.1
    constructor
    · exact le_trans ((ofRat_le_iff _ _).mpr (roundDown_le _ _))
        (le_trans (logPoint_contains (precision + 2) positive).1
          (log_monotone _ _ lowPositive member.1))
    · exact le_trans (log_monotone _ _ valuePositive member.2)
        (le_trans (logPoint_contains (precision + 2)
          (show 0 < interval.hi by have := interval.ordered; grind)).2
          ((ofRat_le_iff _ _).mpr (le_roundUp _ _)))
  · cases computed

/-- A computed enclosure whose endpoints lie in `[lower, upper]` places the
logarithm of every member there. The check is a Boolean on rationals, so the
kernel can decide it. -/
public theorem Contains.log_bracket {interval : Interval} {value : selection.Carrier}
    (member : interval.Contains value) {precision : Nat} {lower upper : Rat}
    (checked : (interval.log? precision).any
      (fun result => decide (lower ≤ result.lo ∧ result.hi ≤ upper)) = true) :
    le (selection.ofRat lower) (logIntegral value) ∧
      le (logIntegral value) (selection.ofRat upper) := by
  cases computed : interval.log? precision with
  | none =>
      rw [computed, Option.any_none] at checked
      cases checked
  | some result =>
      rw [computed, Option.any_some] at checked
      have bounds := of_decide_eq_true checked
      have enclosed := Contains.log computed member
      exact ⟨le_trans ((ofRat_le_iff _ _).mpr bounds.1) enclosed.1,
        le_trans enclosed.2 ((ofRat_le_iff _ _).mpr bounds.2)⟩

/-- The logarithm's enclosure is at most `width / lo` wide, the logarithm's
modulus on the interval, plus three grid steps. -/
public theorem width_log_le {interval result : Interval} {precision : Nat}
    (computed : interval.log? precision = some result) :
    result.width ≤ interval.width / interval.lo + 3 / scale precision := by
  unfold log? at computed
  split at computed
  · rename_i positive
    cases computed
    have highPositive : 0 < interval.hi := by
      have := interval.ordered
      grind
    have lowWidth := logPoint_width (precision + 2) positive
    have highWidth := logPoint_width (precision + 2) highPositive
    have lowAbove := (logPoint_contains (precision + 2) positive).2
    have highBelow := (logPoint_contains (precision + 2) highPositive).1
    have increment := (log_increment_bounds (ofRat_positive positive)
      ((ofRat_le_iff _ _).mpr interval.ordered)).2
    have realGap : le (selection.ofRat ((logPoint (precision + 2) interval.hi).1 -
        (logPoint (precision + 2) interval.lo).2))
        (selection.ofRat ((interval.hi - interval.lo) / interval.lo)) := by
      rw [ofRat_sub, ofRat_div, ofRat_sub]
      real_grind
    have gap := (ofRat_le_iff _ _).mp realGap
    have upperRounding := roundUp_sub_le precision (logPoint (precision + 2) interval.hi).2
    have lowerRounding := sub_roundDown_le precision (logPoint (precision + 2) interval.lo).1
    have fine : 1 / scale (precision + 2 + 1) = 1 / scale precision * (1 / 8) := by
      rw [show precision + 2 + 1 = precision + 3 from rfl, step_add precision 3]
      rfl
    have three : (3 : Rat) / scale precision = 3 * (1 / scale precision) := by
      rw [Rat.div_def, Rat.div_def, Rat.one_mul]
    have stepNonnegative := step_nonnegative precision
    rw [fine] at lowWidth highWidth
    show roundUp precision (logPoint (precision + 2) interval.hi).2 -
        roundDown precision (logPoint (precision + 2) interval.lo).1 ≤
      (interval.hi - interval.lo) / interval.lo + 3 / scale precision
    rw [three]
    grind
  · cases computed

end Interval

end Problib.Analysis.Enclosure
