module

public import Problib.Real.Arithmetic

/-! Closed intervals with rational endpoints that enclose real numbers.

Deciding a comparison between two reals, or reporting a real to a stated
precision, needs a computable interval that provably contains it. An
`Interval` is a pair of rationals `lo ≤ hi`, and `Contains` says that a real of
Problib's carrier lies between their embeddings. Every operation here computes
on the rational endpoints alone, so the kernel evaluates it by `decide`, and
each has a containment theorem proved once over the reals: when the inputs
contain `x` and `y`, the output contains the real result. Addition, negation,
subtraction and multiplication are total. Inversion and division refuse, by
returning `none`, exactly when the denominator interval contains zero.

`roundDown` and `roundUp` move a rational to the grid of spacing
`2^-precision` below or above it. Rounding an interval outward keeps
containment, adds at most two grid steps of width, and keeps the endpoints of a
long computation small.

Each width theorem bounds the output width by the input widths and
magnitudes, so enclosures of shrinking width compose into enclosures of
shrinking width.
-/

set_option autoImplicit false

namespace Problib.Analysis.Enclosure

open Problib.Real.Construction
open Problib.Real.Construction.Dedekind

/-! ### Rational facts -/

/-- Division by a positive rational moves across an upper bound. -/
public theorem div_le_iff_le_mul {numerator bound divisor : Rat} (positive : 0 < divisor) :
    numerator / divisor ≤ bound ↔ numerator ≤ bound * divisor := by
  constructor
  · intro below
    apply Rat.not_lt.mp
    intro above
    exact Rat.not_lt.mpr below ((Rat.lt_div_iff positive).mpr above)
  · intro below
    apply Rat.not_lt.mp
    intro above
    exact Rat.not_lt.mpr below ((Rat.lt_div_iff positive).mp above)

/-- Division by a positive rational moves across a lower bound. -/
public theorem le_div_iff_mul_le {numerator bound divisor : Rat} (positive : 0 < divisor) :
    bound ≤ numerator / divisor ↔ bound * divisor ≤ numerator := by
  constructor
  · intro above
    apply Rat.not_lt.mp
    intro below
    exact Rat.not_lt.mpr above ((Rat.div_lt_iff positive).mpr below)
  · intro above
    apply Rat.not_lt.mp
    intro below
    exact Rat.not_lt.mpr above ((Rat.div_lt_iff positive).mp below)

/-- A product of two factors bounded in size is bounded by the product of the
bounds. -/
public theorem mul_le_mul_of_bounded {first second firstBound secondBound : Rat}
    (firstLower : -firstBound ≤ first) (firstUpper : first ≤ firstBound)
    (secondLower : -secondBound ≤ second) (secondUpper : second ≤ secondBound) :
    first * second ≤ firstBound * secondBound := by
  have firstBoundNonnegative : 0 ≤ firstBound := by
    have := Rat.le_trans firstLower firstUpper
    grind
  have secondBoundNonnegative : 0 ≤ secondBound := by
    have := Rat.le_trans secondLower secondUpper
    grind
  have productNonnegative := Rat.mul_nonneg firstBoundNonnegative secondBoundNonnegative
  rcases Rat.le_total (a := 0) (b := first) with firstNonnegative | firstNonpositive
  · rcases Rat.le_total (a := 0) (b := second) with secondNonnegative | secondNonpositive
    · exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right firstUpper secondNonnegative)
        (Rat.mul_le_mul_of_nonneg_left secondUpper firstBoundNonnegative)
    · have flipped : 0 ≤ -second := by grind
      have := Rat.mul_nonneg firstNonnegative flipped
      rw [Rat.mul_neg] at this
      grind
  · have flipped : 0 ≤ -first := by grind
    rcases Rat.le_total (a := 0) (b := second) with secondNonnegative | secondNonpositive
    · have := Rat.mul_nonneg flipped secondNonnegative
      rw [Rat.neg_mul] at this
      grind
    · have secondFlipped : 0 ≤ -second := by grind
      have firstAbove : -first ≤ firstBound := by grind
      have secondAbove : -second ≤ secondBound := by grind
      have bounded := Rat.le_trans (Rat.mul_le_mul_of_nonneg_right firstAbove secondFlipped)
        (Rat.mul_le_mul_of_nonneg_left secondAbove firstBoundNonnegative)
      rw [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg] at bounded
      exact bounded

/-- Reciprocals reverse order between positive rationals. -/
public theorem inv_le_inv_of_positive {smaller larger : Rat} (positive : 0 < smaller)
    (ordered : smaller ≤ larger) : larger⁻¹ ≤ smaller⁻¹ := by
  apply (ofRat_le_iff _ _).mp
  rw [ofRat_inverse, ofRat_inverse]
  apply inverse_le_inverse_of_positive _ ((ofRat_le_iff _ _).mpr ordered)
  rw [← ofRat_zero]
  exact (ofRat_lt_iff 0 smaller).mpr positive

/-! ### The dyadic grid -/

/-- The number of grid steps per unit at a precision, `2^precision`. -/
@[expose] public def scale (precision : Nat) : Rat := ((2 ^ precision : Nat) : Rat)

public theorem scale_positive (precision : Nat) : 0 < scale precision :=
  Rat.natCast_pos.mpr (Nat.two_pow_pos precision)

/-- The grid point at or below `value`. -/
@[expose] public def roundDown (precision : Nat) (value : Rat) : Rat :=
  ((value * scale precision).floor : Rat) / scale precision

/-- The grid point at or above `value`. -/
@[expose] public def roundUp (precision : Nat) (value : Rat) : Rat :=
  ((value * scale precision).ceil : Rat) / scale precision

public theorem roundDown_le (precision : Nat) (value : Rat) :
    roundDown precision value ≤ value :=
  (div_le_iff_le_mul (scale_positive precision)).mpr (Rat.floor_le _)

public theorem le_roundUp (precision : Nat) (value : Rat) :
    value ≤ roundUp precision value :=
  (le_div_iff_mul_le (scale_positive precision)).mpr Rat.le_ceil

/-- Rounding down loses less than one grid step. -/
public theorem sub_roundDown_le (precision : Nat) (value : Rat) :
    value - roundDown precision value ≤ 1 / scale precision := by
  have positive := scale_positive precision
  have floorAbove := Rat.lt_floor (x := value * scale precision)
  have shifted : value * scale precision ≤
      ((value * scale precision).floor : Rat) + 1 := by grind
  have divided : value ≤ (((value * scale precision).floor : Rat) + 1) / scale precision :=
    (le_div_iff_mul_le positive).mpr shifted
  have split : (((value * scale precision).floor : Rat) + 1) / scale precision =
      roundDown precision value + 1 / scale precision := by
    rw [roundDown, Rat.div_def, Rat.div_def, Rat.div_def, Rat.add_mul]
  rw [split] at divided
  grind

/-- Rounding up gains less than one grid step. -/
public theorem roundUp_sub_le (precision : Nat) (value : Rat) :
    roundUp precision value - value ≤ 1 / scale precision := by
  have positive := scale_positive precision
  have ceilBelow := Rat.ceil_lt (x := value * scale precision)
  have shifted : ((value * scale precision).ceil : Rat) - 1 ≤
      value * scale precision := by grind
  have divided : (((value * scale precision).ceil : Rat) - 1) / scale precision ≤ value :=
    (div_le_iff_le_mul positive).mpr shifted
  have split : (((value * scale precision).ceil : Rat) - 1) / scale precision =
      roundUp precision value - 1 / scale precision := by
    rw [roundUp, Rat.div_def, Rat.div_def, Rat.div_def, Rat.sub_eq_add_neg,
      Rat.sub_eq_add_neg, Rat.add_mul, Rat.neg_mul]
  rw [split] at divided
  grind

/-- Rounding down keeps a nonnegative value nonnegative. -/
public theorem roundDown_nonnegative {precision : Nat} {value : Rat} (nonnegative : 0 ≤ value) :
    0 ≤ roundDown precision value := by
  have positive := scale_positive precision
  have scaled : (0 : Int) ≤ (value * scale precision).floor := by
    apply Rat.le_floor_iff.mpr
    have := Rat.mul_nonneg nonnegative (Rat.le_of_lt positive)
    simpa using this
  apply (le_div_iff_mul_le positive).mpr
  rw [Rat.zero_mul]
  exact Rat.intCast_nonneg.mpr scaled

/-! ### Real facts -/

/-- A real between two others multiplies a fixed factor to a product between
theirs, in one order or the other. -/
private theorem mul_between {lower upper value factor : selection.Carrier}
    (lowerValue : le lower value) (valueUpper : le value upper) :
    (le (mul lower factor) (mul value factor) ∧ le (mul value factor) (mul upper factor)) ∨
      (le (mul upper factor) (mul value factor) ∧
        le (mul value factor) (mul lower factor)) := by
  rcases le_total zero factor with nonnegative | nonpositive
  · exact Or.inl ⟨mul_le_mul_nonnegative_right lowerValue nonnegative,
      mul_le_mul_nonnegative_right valueUpper nonnegative⟩
  · have flipped : le zero (neg factor) := neg_nonnegative_iff.mpr nonpositive
    refine Or.inr ⟨?_, ?_⟩
    · have scaled := mul_le_mul_nonnegative_right valueUpper flipped
      rw [mul_neg, mul_neg] at scaled
      exact neg_le_neg_iff.mp scaled
    · have scaled := mul_le_mul_nonnegative_right lowerValue flipped
      rw [mul_neg, mul_neg] at scaled
      exact neg_le_neg_iff.mp scaled

/-- An embedded endpoint times a real inside `[low, high]` lies between the
smaller and larger endpoint products. -/
private theorem endpoint_mul_bounds (endpoint low high : Rat) {value : selection.Carrier}
    (lowValue : le (selection.ofRat low) value) (valueHigh : le value (selection.ofRat high)) :
    le (selection.ofRat (min (endpoint * low) (endpoint * high)))
        (mul (selection.ofRat endpoint) value) ∧
      le (mul (selection.ofRat endpoint) value)
        (selection.ofRat (max (endpoint * low) (endpoint * high))) := by
  have lowerLow := (ofRat_le_iff _ _).mpr
    (show min (endpoint * low) (endpoint * high) ≤ endpoint * low by grind)
  have lowerHigh := (ofRat_le_iff _ _).mpr
    (show min (endpoint * low) (endpoint * high) ≤ endpoint * high by grind)
  have upperLow := (ofRat_le_iff _ _).mpr
    (show endpoint * low ≤ max (endpoint * low) (endpoint * high) by grind)
  have upperHigh := (ofRat_le_iff _ _).mpr
    (show endpoint * high ≤ max (endpoint * low) (endpoint * high) by grind)
  rw [ofRat_mul] at lowerLow lowerHigh upperLow upperHigh
  rw [mul_comm (selection.ofRat endpoint) (selection.ofRat low)] at lowerLow upperLow
  rw [mul_comm (selection.ofRat endpoint) (selection.ofRat high)] at lowerHigh upperHigh
  rw [mul_comm (selection.ofRat endpoint) value]
  rcases mul_between (factor := selection.ofRat endpoint) lowValue valueHigh with
    ⟨first, second⟩ | ⟨first, second⟩
  · exact ⟨le_trans lowerLow first, le_trans second upperHigh⟩
  · exact ⟨le_trans lowerHigh first, le_trans second upperLow⟩

/-! ### Intervals -/

/-- A closed interval with rational endpoints. -/
public structure Interval where
  /-- The lower endpoint. -/
  lo : Rat
  /-- The upper endpoint. -/
  hi : Rat
  /-- The endpoints are ordered. -/
  ordered : lo ≤ hi

namespace Interval

/-- The real `value` lies between the embedded endpoints. -/
@[expose] public def Contains (interval : Interval) (value : selection.Carrier) : Prop :=
  Dedekind.le (selection.ofRat interval.lo) value ∧
    Dedekind.le value (selection.ofRat interval.hi)

/-- The distance between the endpoints. -/
@[expose] public def width (interval : Interval) : Rat := interval.hi - interval.lo

/-- The largest endpoint size, a bound for the size of every member. -/
@[expose] public def magnitude (interval : Interval) : Rat := max (-interval.lo) interval.hi

public theorem width_nonnegative (interval : Interval) : 0 ≤ interval.width := by
  have := interval.ordered
  unfold width
  grind

public theorem magnitude_nonnegative (interval : Interval) : 0 ≤ interval.magnitude := by
  have := interval.ordered
  unfold magnitude
  grind

/-- The interval holding exactly one rational. -/
@[expose] public def point (value : Rat) : Interval := ⟨value, value, Rat.le_refl⟩

@[expose] public def add (left right : Interval) : Interval where
  lo := left.lo + right.lo
  hi := left.hi + right.hi
  ordered := by
    have := left.ordered
    have := right.ordered
    grind

@[expose] public def neg (interval : Interval) : Interval where
  lo := -interval.hi
  hi := -interval.lo
  ordered := by
    have := interval.ordered
    grind

@[expose] public def sub (left right : Interval) : Interval := left.add right.neg

/-- The smallest of the four endpoint products. -/
@[expose] public def mulLo (left right : Interval) : Rat :=
  min (min (left.lo * right.lo) (left.lo * right.hi))
    (min (left.hi * right.lo) (left.hi * right.hi))

/-- The largest of the four endpoint products. -/
@[expose] public def mulHi (left right : Interval) : Rat :=
  max (max (left.lo * right.lo) (left.lo * right.hi))
    (max (left.hi * right.lo) (left.hi * right.hi))

@[expose] public def mul (left right : Interval) : Interval where
  lo := mulLo left right
  hi := mulHi left right
  ordered := by
    unfold mulLo mulHi
    grind

/-- The reciprocal interval, refused when the interval contains zero. -/
@[expose] public def inv? (interval : Interval) : Option Interval :=
  if positive : 0 < interval.lo then
    some ⟨interval.hi⁻¹, interval.lo⁻¹, inv_le_inv_of_positive positive interval.ordered⟩
  else if negative : interval.hi < 0 then
    some ⟨interval.hi⁻¹, interval.lo⁻¹, by
      have flipped : -interval.lo⁻¹ ≤ -interval.hi⁻¹ := by
        have := inv_le_inv_of_positive (smaller := -interval.hi) (larger := -interval.lo)
          (by grind) (by have := interval.ordered; grind)
        apply (ofRat_le_iff _ _).mp
        have embedded := (ofRat_le_iff _ _).mpr this
        rw [ofRat_inverse, ofRat_inverse, ofRat_neg, ofRat_neg, inverse_neg,
          inverse_neg] at embedded
        rw [ofRat_neg, ofRat_neg, ofRat_inverse, ofRat_inverse]
        exact embedded
      grind⟩
  else none

/-- The quotient interval, refused when the denominator contains zero. -/
@[expose] public def div? (numerator denominator : Interval) : Option Interval :=
  denominator.inv?.map numerator.mul

/-- The interval rounded outward to the grid of spacing `2^-precision`. -/
@[expose] public def round (precision : Nat) (interval : Interval) : Interval where
  lo := roundDown precision interval.lo
  hi := roundUp precision interval.hi
  ordered := Rat.le_trans (roundDown_le precision interval.lo)
    (Rat.le_trans interval.ordered (le_roundUp precision interval.hi))

/-! ### Containment -/

public theorem contains_point (value : Rat) : (point value).Contains (selection.ofRat value) :=
  ⟨le_refl _, le_refl _⟩

public theorem Contains.add {left right : Interval} {first second : selection.Carrier}
    (firstMember : left.Contains first) (secondMember : right.Contains second) :
    (left.add right).Contains (Dedekind.add first second) := by
  constructor
  · show Dedekind.le (selection.ofRat (left.lo + right.lo)) _
    rw [ofRat_add]
    exact add_le_add firstMember.1 secondMember.1
  · show Dedekind.le _ (selection.ofRat (left.hi + right.hi))
    rw [ofRat_add]
    exact add_le_add firstMember.2 secondMember.2

public theorem Contains.neg {interval : Interval} {value : selection.Carrier}
    (member : interval.Contains value) : interval.neg.Contains (Dedekind.neg value) := by
  constructor
  · show Dedekind.le (selection.ofRat (-interval.hi)) _
    rw [ofRat_neg]
    exact neg_le_neg_iff.mpr member.2
  · show Dedekind.le _ (selection.ofRat (-interval.lo))
    rw [ofRat_neg]
    exact neg_le_neg_iff.mpr member.1

public theorem Contains.sub {left right : Interval} {first second : selection.Carrier}
    (firstMember : left.Contains first) (secondMember : right.Contains second) :
    (left.sub right).Contains (Dedekind.sub first second) := by
  rw [sub_eq_add_neg]
  exact firstMember.add secondMember.neg

public theorem Contains.mul {left right : Interval} {first second : selection.Carrier}
    (firstMember : left.Contains first) (secondMember : right.Contains second) :
    (left.mul right).Contains (Dedekind.mul first second) := by
  have lowBounds := endpoint_mul_bounds left.lo right.lo right.hi secondMember.1 secondMember.2
  have highBounds := endpoint_mul_bounds left.hi right.lo right.hi secondMember.1 secondMember.2
  have lowerFirst := (ofRat_le_iff _ _).mpr
    (show mulLo left right ≤ min (left.lo * right.lo) (left.lo * right.hi) by
      unfold mulLo; grind)
  have lowerSecond := (ofRat_le_iff _ _).mpr
    (show mulLo left right ≤ min (left.hi * right.lo) (left.hi * right.hi) by
      unfold mulLo; grind)
  have upperFirst := (ofRat_le_iff _ _).mpr
    (show max (left.lo * right.lo) (left.lo * right.hi) ≤ mulHi left right by
      unfold mulHi; grind)
  have upperSecond := (ofRat_le_iff _ _).mpr
    (show max (left.hi * right.lo) (left.hi * right.hi) ≤ mulHi left right by
      unfold mulHi; grind)
  constructor
  · show Dedekind.le (selection.ofRat (mulLo left right)) _
    rcases mul_between (factor := second) firstMember.1 firstMember.2 with
      ⟨below, _⟩ | ⟨below, _⟩
    · exact le_trans lowerFirst (le_trans lowBounds.1 below)
    · exact le_trans lowerSecond (le_trans highBounds.1 below)
  · show Dedekind.le _ (selection.ofRat (mulHi left right))
    rcases mul_between (factor := second) firstMember.1 firstMember.2 with
      ⟨_, above⟩ | ⟨_, above⟩
    · exact le_trans above (le_trans highBounds.2 upperSecond)
    · exact le_trans above (le_trans lowBounds.2 upperFirst)

/-- The reciprocal interval contains the reciprocal of every member. -/
public theorem Contains.inv {interval result : Interval} {value : selection.Carrier}
    (computed : interval.inv? = some result) (member : interval.Contains value) :
    result.Contains (inverse value) := by
  unfold inv? at computed
  split at computed
  · rename_i positive
    cases computed
    have lowPositive : lt zero (selection.ofRat interval.lo) := by
      rw [← ofRat_zero]
      exact (ofRat_lt_iff 0 interval.lo).mpr positive
    have valuePositive := lt_of_lt_of_le lowPositive member.1
    constructor
    · show Dedekind.le (selection.ofRat interval.hi⁻¹) _
      rw [ofRat_inverse]
      exact inverse_le_inverse_of_positive valuePositive member.2
    · show Dedekind.le _ (selection.ofRat interval.lo⁻¹)
      rw [ofRat_inverse]
      exact inverse_le_inverse_of_positive lowPositive member.1
  · split at computed
    · rename_i _ negative
      cases computed
      have highNegative : lt (selection.ofRat interval.hi) zero := by
        rw [← ofRat_zero]
        exact (ofRat_lt_iff interval.hi 0).mpr negative
      have flippedHigh : lt zero (Dedekind.neg (selection.ofRat interval.hi)) :=
        neg_positive_iff.mpr highNegative
      have flippedValue : lt zero (Dedekind.neg value) :=
        lt_of_lt_of_le flippedHigh (neg_le_neg_iff.mpr member.2)
      constructor
      · show Dedekind.le (selection.ofRat interval.hi⁻¹) _
        rw [ofRat_inverse]
        have reversed := inverse_le_inverse_of_positive flippedHigh
          (neg_le_neg_iff.mpr member.2)
        rw [inverse_neg, inverse_neg] at reversed
        exact neg_le_neg_iff.mp reversed
      · show Dedekind.le _ (selection.ofRat interval.lo⁻¹)
        rw [ofRat_inverse]
        have reversed := inverse_le_inverse_of_positive flippedValue
          (neg_le_neg_iff.mpr member.1)
        rw [inverse_neg, inverse_neg] at reversed
        exact neg_le_neg_iff.mp reversed
    · cases computed

/-- The quotient interval contains the quotient of every pair of members. -/
public theorem Contains.div {numerator denominator result : Interval}
    {first second : selection.Carrier}
    (computed : numerator.div? denominator = some result)
    (firstMember : numerator.Contains first) (secondMember : denominator.Contains second) :
    result.Contains (Dedekind.div first second) := by
  unfold div? at computed
  cases reciprocal : denominator.inv? with
  | none => rw [reciprocal] at computed; cases computed
  | some inverted =>
      rw [reciprocal] at computed
      cases computed
      rw [div_eq_mul_inverse]
      exact firstMember.mul (Contains.inv reciprocal secondMember)

public theorem Contains.round {interval : Interval} {value : selection.Carrier}
    (member : interval.Contains value) (precision : Nat) :
    (interval.round precision).Contains value :=
  ⟨le_trans ((ofRat_le_iff _ _).mpr (roundDown_le precision interval.lo)) member.1,
    le_trans member.2 ((ofRat_le_iff _ _).mpr (le_roundUp precision interval.hi))⟩

/-- A member of an interval with an empty interior is its rational endpoint. -/
public theorem Contains.eq_of_width_zero {interval : Interval} {value : selection.Carrier}
    (member : interval.Contains value) (flat : interval.width = 0) :
    value = selection.ofRat interval.lo := by
  have same : interval.hi = interval.lo := by
    unfold width at flat
    grind
  apply le_antisymm
  · rw [← same]
    exact member.2
  · exact member.1

/-! ### Refusals -/

public theorem inv?_isSome_iff (interval : Interval) :
    interval.inv?.isSome = true ↔ 0 < interval.lo ∨ interval.hi < 0 := by
  unfold inv?
  by_cases positive : 0 < interval.lo
  · simp [positive]
  · by_cases negative : interval.hi < 0
    · simp [positive, negative]
    · simp [positive, negative]

public theorem div?_isSome_iff (numerator denominator : Interval) :
    (numerator.div? denominator).isSome = true ↔ 0 < denominator.lo ∨ denominator.hi < 0 := by
  unfold div?
  rw [Option.isSome_map]
  exact inv?_isSome_iff denominator

/-! ### Order between members -/

/-- Every member of an interval lies below every member of an interval above it. -/
public theorem Contains.lt_of_hi_lt_lo {left right : Interval} {first second : selection.Carrier}
    (firstMember : left.Contains first) (secondMember : right.Contains second)
    (separated : left.hi < right.lo) : Dedekind.lt first second :=
  lt_of_le_of_lt firstMember.2
    (lt_of_lt_of_le ((ofRat_lt_iff _ _).mpr separated) secondMember.1)

/-- Every member of an interval lies at or below every member of an interval
that starts where it ends. -/
public theorem Contains.le_of_hi_le_lo {left right : Interval} {first second : selection.Carrier}
    (firstMember : left.Contains first) (secondMember : right.Contains second)
    (separated : left.hi ≤ right.lo) : Dedekind.le first second :=
  le_trans firstMember.2 (le_trans ((ofRat_le_iff _ _).mpr separated) secondMember.1)

/-! ### Widths -/

public theorem width_point (value : Rat) : (point value).width = 0 := by
  unfold width point
  grind

public theorem width_add (left right : Interval) :
    (left.add right).width = left.width + right.width := by
  unfold width add
  grind

public theorem width_neg (interval : Interval) : interval.neg.width = interval.width := by
  unfold width neg
  grind

public theorem width_sub (left right : Interval) :
    (left.sub right).width = left.width + right.width := by
  unfold sub
  rw [width_add, width_neg]

/-- Two endpoint products differ by at most the first width times the second
magnitude plus the first magnitude times the second width. -/
private theorem product_difference_le (left right : Interval) {first other : Rat}
    {second another : Rat}
    (firstLow : left.lo ≤ first) (firstHigh : first ≤ left.hi)
    (otherLow : left.lo ≤ other) (otherHigh : other ≤ left.hi)
    (secondLow : right.lo ≤ second) (secondHigh : second ≤ right.hi)
    (anotherLow : right.lo ≤ another) (anotherHigh : another ≤ right.hi) :
    first * second - other * another ≤
      left.width * right.magnitude + left.magnitude * right.width := by
  have firstPart := mul_le_mul_of_bounded (first := first - other) (second := second)
    (firstBound := left.width) (secondBound := right.magnitude)
    (by unfold width; grind) (by unfold width; grind)
    (by unfold magnitude; grind) (by unfold magnitude; grind)
  have secondPart := mul_le_mul_of_bounded (first := other) (second := second - another)
    (firstBound := left.magnitude) (secondBound := right.width)
    (by unfold magnitude; grind) (by unfold magnitude; grind)
    (by unfold width; grind) (by unfold width; grind)
  have split : first * second - other * another =
      (first - other) * second + other * (second - another) := by grind
  rw [split]
  grind

public theorem width_mul_le (left right : Interval) :
    (left.mul right).width ≤ left.width * right.magnitude + left.magnitude * right.width := by
  have leftOrdered := left.ordered
  have rightOrdered := right.ordered
  have bound := fun {first other second another : Rat}
      (firstLow : left.lo ≤ first) (firstHigh : first ≤ left.hi)
      (otherLow : left.lo ≤ other) (otherHigh : other ≤ left.hi)
      (secondLow : right.lo ≤ second) (secondHigh : second ≤ right.hi)
      (anotherLow : right.lo ≤ another) (anotherHigh : another ≤ right.hi) =>
    product_difference_le left right firstLow firstHigh otherLow otherHigh secondLow secondHigh
      anotherLow anotherHigh
  have low := Rat.le_refl (a := left.lo)
  have high := Rat.le_refl (a := left.hi)
  have rlow := Rat.le_refl (a := right.lo)
  have rhigh := Rat.le_refl (a := right.hi)
  have p1 := bound low leftOrdered low leftOrdered rlow rightOrdered rlow rightOrdered
  have p2 := bound low leftOrdered low leftOrdered rlow rightOrdered rightOrdered rhigh
  have p3 := bound low leftOrdered leftOrdered high rlow rightOrdered rlow rightOrdered
  have p4 := bound low leftOrdered leftOrdered high rlow rightOrdered rightOrdered rhigh
  have p5 := bound low leftOrdered low leftOrdered rightOrdered rhigh rlow rightOrdered
  have p6 := bound low leftOrdered low leftOrdered rightOrdered rhigh rightOrdered rhigh
  have p7 := bound low leftOrdered leftOrdered high rightOrdered rhigh rlow rightOrdered
  have p8 := bound low leftOrdered leftOrdered high rightOrdered rhigh rightOrdered rhigh
  have p9 := bound leftOrdered high low leftOrdered rlow rightOrdered rlow rightOrdered
  have p10 := bound leftOrdered high low leftOrdered rlow rightOrdered rightOrdered rhigh
  have p11 := bound leftOrdered high leftOrdered high rlow rightOrdered rlow rightOrdered
  have p12 := bound leftOrdered high leftOrdered high rlow rightOrdered rightOrdered rhigh
  have p13 := bound leftOrdered high low leftOrdered rightOrdered rhigh rlow rightOrdered
  have p14 := bound leftOrdered high low leftOrdered rightOrdered rhigh rightOrdered rhigh
  have p15 := bound leftOrdered high leftOrdered high rightOrdered rhigh rlow rightOrdered
  have p16 := bound leftOrdered high leftOrdered high rightOrdered rhigh rightOrdered rhigh
  show mulHi left right - mulLo left right ≤ _
  unfold mulHi mulLo
  grind

/-- Inverting a positive interval scales its width by the product of its
endpoints. -/
public theorem width_inv {interval result : Interval} (computed : interval.inv? = some result) :
    result.width * (interval.lo * interval.hi) = interval.width := by
  have ordered := interval.ordered
  have reciprocal : ∀ (low high : Rat), low ≠ 0 → high ≠ 0 →
      (low⁻¹ - high⁻¹) * (low * high) = high - low := by
    intro low high lowNonzero highNonzero
    rw [Rat.sub_eq_add_neg, Rat.add_mul, Rat.neg_mul, ← Rat.mul_assoc,
      Rat.inv_mul_cancel _ lowNonzero, Rat.one_mul, Rat.mul_comm low high,
      ← Rat.mul_assoc, Rat.inv_mul_cancel _ highNonzero, Rat.one_mul, ← Rat.sub_eq_add_neg]
  unfold inv? at computed
  split at computed
  · rename_i positive
    cases computed
    exact reciprocal interval.lo interval.hi (by grind) (by grind)
  · split at computed
    · rename_i negative
      cases computed
      exact reciprocal interval.lo interval.hi (by grind) (by grind)
    · cases computed

public theorem width_round_le (precision : Nat) (interval : Interval) :
    (interval.round precision).width ≤ interval.width + 2 / scale precision := by
  have down := sub_roundDown_le precision interval.lo
  have up := roundUp_sub_le precision interval.hi
  have twice : (2 : Rat) / scale precision = 1 / scale precision + 1 / scale precision := by
    rw [Rat.div_def, Rat.div_def, ← Rat.add_mul, show (1 : Rat) + 1 = 2 by decide +kernel]
  unfold width round
  rw [twice]
  grind

end Interval

end Problib.Analysis.Enclosure
