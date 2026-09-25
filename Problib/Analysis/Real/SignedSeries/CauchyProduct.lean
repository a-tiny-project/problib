module

public import Problib.Analysis.Real.SignedSeries.Products

/-! Degreewise convolution for signed series.

The Cauchy product is indexed by total degree. Its finite rows are sums in the
sealed real carrier. The nonnegative identity compares triangular and square
partial sums; positive and negative parts then give the signed identity under
absolute convergence.
-/

set_option autoImplicit false

namespace Problib.Analysis.Real.SignedSeries

open Problib.Real.Construction.Dedekind

noncomputable section

private instance : Std.Associative (α := selection.Carrier) add :=
  ⟨fun left middle right => add_assoc left middle right⟩

private instance : Std.Commutative (α := selection.Carrier) add :=
  ⟨add_comm⟩

private instance : Std.Commutative (α := selection.Carrier) mul :=
  ⟨mul_comm⟩

/-- The coefficient of total degree `degreeValue` in a Cauchy product. -/
@[expose] public def convolution (first second : Nat → selection.Carrier)
    (degreeValue : Nat) : selection.Carrier :=
  partialSum
    (fun index => mul (first index) (second (degreeValue - index)))
    (degreeValue + 1)

public theorem partial_sum_congr_below {first second : Nat → selection.Carrier}
    (count : Nat)
    (equal : ∀ index, index < count → first index = second index) :
    partialSum first count = partialSum second count := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [partial_sum_succ, partial_sum_succ,
        induction (fun index later => equal index (Nat.lt_succ_of_lt later)),
        equal count (Nat.lt_succ_self count)]

private theorem partial_sum_le_below {first second : Nat → selection.Carrier}
    (count : Nat)
    (included : ∀ index, index < count → le (first index) (second index)) :
    le (partialSum first count) (partialSum second count) := by
  induction count with
  | zero => exact le_refl zero
  | succ count induction =>
      rw [partial_sum_succ, partial_sum_succ]
      exact add_le_add
        (induction (fun index earlier => included index
          (Nat.lt_succ_of_lt earlier)))
        (included count (Nat.lt_succ_self count))

public theorem convolution_zero (first second : Nat → selection.Carrier) :
    convolution first second 0 = mul (first 0) (second 0) := by
  rw [convolution, partial_sum_succ, partial_sum_zero, zero_add]

/-- A new diagonal consists of the previous diagonal with the second
sequence shifted, followed by its right endpoint. -/
public theorem convolution_succ (first second : Nat → selection.Carrier)
    (degreeValue : Nat) :
    convolution first second (degreeValue + 1) =
      add (convolution first (fun index => second (index + 1)) degreeValue)
        (mul (first (degreeValue + 1)) (second 0)) := by
  unfold convolution
  rw [partial_sum_succ]
  have equal :
      partialSum
          (fun index => mul (first index)
            (second (degreeValue + 1 - index)))
          (degreeValue + 1) =
        partialSum
          (fun index => mul (first index)
            (second ((degreeValue - index) + 1)))
          (degreeValue + 1) := by
    apply partial_sum_congr_below
    intro index earlier
    have arithmetic : degreeValue + 1 - index =
        (degreeValue - index) + 1 := by omega
    rw [arithmetic]
  rw [equal]
  have endValue : degreeValue + 1 - (degreeValue + 1) = 0 := by omega
  rw [endValue]

private theorem abs_partial_sum_le (values : Nat → selection.Carrier)
    (count : Nat) :
    le (abs (partialSum values count))
      (partialSum (fun index => abs (values index)) count) := by
  induction count with
  | zero =>
      rw [partial_sum_zero, partial_sum_zero, abs_zero]
      exact le_refl zero
  | succ count induction =>
      rw [partial_sum_succ, partial_sum_succ]
      exact le_trans (abs_add_le _ _)
        (add_le_add induction (le_refl _))

/-- The convolution of absolute coefficients bounds every signed diagonal. -/
public theorem abs_convolution_le (first second : Nat → selection.Carrier)
    (degreeValue : Nat) :
    le (abs (convolution first second degreeValue))
      (convolution (fun index => abs (first index))
        (fun index => abs (second index)) degreeValue) := by
  have bound := abs_partial_sum_le
    (fun index => mul (first index) (second (degreeValue - index)))
    (degreeValue + 1)
  have equal :
      partialSum
        (fun index => abs (mul (first index)
          (second (degreeValue - index)))) (degreeValue + 1) =
      convolution (fun index => abs (first index))
        (fun index => abs (second index)) degreeValue := by
    unfold convolution
    apply partial_sum_congr_below
    intro index _
    exact abs_mul (first index) (second (degreeValue - index))
  rw [equal] at bound
  exact bound

public theorem convolution_nonnegative
    {first second : Nat → selection.Carrier}
    (firstNonnegative : ∀ index, le zero (first index))
    (secondNonnegative : ∀ index, le zero (second index))
    (degreeValue : Nat) :
    le zero (convolution first second degreeValue) := by
  unfold convolution
  exact partial_sum_nonnegative
    (fun index => mul_nonnegative (firstNonnegative index)
      (secondNonnegative (degreeValue - index)))
    (degreeValue + 1)

public theorem convolution_add_left
    (first second right : Nat → selection.Carrier)
    (degreeValue : Nat) :
    convolution (fun index => add (first index) (second index))
        right degreeValue =
      add (convolution first right degreeValue)
        (convolution second right degreeValue) := by
  unfold convolution
  have equal :
      (fun index => mul (add (first index) (second index))
        (right (degreeValue - index))) =
      (fun index => add
        (mul (first index) (right (degreeValue - index)))
        (mul (second index) (right (degreeValue - index)))) := by
    funext index
    exact add_mul _ _ _
  rw [equal, partial_sum_add]

public theorem convolution_add_right
    (left first second : Nat → selection.Carrier)
    (degreeValue : Nat) :
    convolution left (fun index => add (first index) (second index))
        degreeValue =
      add (convolution left first degreeValue)
        (convolution left second degreeValue) := by
  unfold convolution
  have equal :
      (fun index => mul (left index)
        (add (first (degreeValue - index))
          (second (degreeValue - index)))) =
      (fun index => add
        (mul (left index) (first (degreeValue - index)))
        (mul (left index) (second (degreeValue - index)))) := by
    funext index
    exact mul_add _ _ _
  rw [equal, partial_sum_add]

public theorem convolution_neg_left
    (left right : Nat → selection.Carrier) (degreeValue : Nat) :
    convolution (fun index => neg (left index)) right degreeValue =
      neg (convolution left right degreeValue) := by
  unfold convolution
  have equal :
      (fun index => mul (neg (left index))
        (right (degreeValue - index))) =
      (fun index => neg (mul (left index)
        (right (degreeValue - index)))) := by
    funext index
    exact neg_mul _ _
  rw [equal, partial_sum_neg]

public theorem convolution_neg_right
    (left right : Nat → selection.Carrier) (degreeValue : Nat) :
    convolution left (fun index => neg (right index)) degreeValue =
      neg (convolution left right degreeValue) := by
  unfold convolution
  have equal :
      (fun index => mul (left index)
        (neg (right (degreeValue - index)))) =
      (fun index => neg (mul (left index)
        (right (degreeValue - index)))) := by
    funext index
    exact mul_neg _ _
  rw [equal, partial_sum_neg]

public theorem convolution_sub_left
    (first second right : Nat → selection.Carrier)
    (degreeValue : Nat) :
    convolution (fun index => sub (first index) (second index))
        right degreeValue =
      sub (convolution first right degreeValue)
        (convolution second right degreeValue) := by
  have termsEqual :
      (fun index => sub (first index) (second index)) =
      (fun index => add (first index) (neg (second index))) := by
    funext index
    exact sub_eq_add_neg _ _
  rw [termsEqual, convolution_add_left, convolution_neg_left,
    sub_eq_add_neg]

public theorem convolution_sub_right
    (left first second : Nat → selection.Carrier)
    (degreeValue : Nat) :
    convolution left (fun index => sub (first index) (second index))
        degreeValue =
      sub (convolution left first degreeValue)
        (convolution left second degreeValue) := by
  have termsEqual :
      (fun index => sub (first index) (second index)) =
      (fun index => add (first index) (neg (second index))) := by
    funext index
    exact sub_eq_add_neg _ _
  rw [termsEqual, convolution_add_right, convolution_neg_right,
    sub_eq_add_neg]

/-- A triangular double sum, grouped first by its left index. -/
@[expose] public def triangleRows (first second : Nat → selection.Carrier)
    (count : Nat) : selection.Carrier :=
  partialSum
    (fun index => mul (first index)
      (partialSum second (count - index))) count

public theorem triangleRows_succ (first second : Nat → selection.Carrier)
    (count : Nat) :
    triangleRows first second (count + 1) =
      add (triangleRows first second count)
        (convolution first second count) := by
  unfold triangleRows convolution
  rw [partial_sum_succ]
  have split :
      partialSum
          (fun index => mul (first index)
            (partialSum second (count + 1 - index))) count =
        add
          (partialSum
            (fun index => mul (first index)
              (partialSum second (count - index))) count)
          (partialSum
            (fun index => mul (first index)
              (second (count - index))) count) := by
    calc
      partialSum
          (fun index => mul (first index)
            (partialSum second (count + 1 - index))) count =
        partialSum
          (fun index => add
            (mul (first index) (partialSum second (count - index)))
            (mul (first index) (second (count - index)))) count := by
        apply partial_sum_congr_below
        intro index earlier
        have arithmetic : count + 1 - index =
            (count - index) + 1 := by omega
        rw [arithmetic, partial_sum_succ, mul_add]
      _ = _ := partial_sum_add _ _ count
  rw [split]
  have endpoint : count + 1 - count = 1 := by omega
  rw [endpoint, partial_sum_succ, partial_sum_zero, zero_add]
  rw [partial_sum_succ
    (fun index => mul (first index) (second (count - index))) count,
    Nat.sub_self]
  ac_rfl

/-- Summing the Cauchy coefficients through a degree cutoff equals the
triangular row sum below that cutoff. -/
public theorem partial_sum_convolution_eq_triangleRows
    (first second : Nat → selection.Carrier) (count : Nat) :
    partialSum (convolution first second) count =
      triangleRows first second count := by
  induction count with
  | zero => rw [partial_sum_zero, triangleRows, partial_sum_zero]
  | succ count induction =>
      rw [partial_sum_succ, induction, triangleRows_succ]

private theorem partial_sum_mul_right
    (values : Nat → selection.Carrier) (factor : selection.Carrier)
    (count : Nat) :
    partialSum (fun index => mul (values index) factor) count =
      mul (partialSum values count) factor := by
  have equal : (fun index => mul (values index) factor) =
      (fun index => mul factor (values index)) := by
    funext index
    exact mul_comm _ _
  rw [equal, partial_sum_scale, mul_comm]

/-- A nonnegative triangle fits inside the square with the same cutoff. -/
public theorem triangle_le_rectangle
    {first second : Nat → selection.Carrier}
    (firstNonnegative : ∀ index, le zero (first index))
    (secondNonnegative : ∀ index, le zero (second index))
    (count : Nat) :
    le (partialSum (convolution first second) count)
      (mul (partialSum first count) (partialSum second count)) := by
  rw [partial_sum_convolution_eq_triangleRows]
  unfold triangleRows
  have pointwise : ∀ index,
      le (mul (first index) (partialSum second (count - index)))
        (mul (first index) (partialSum second count)) := by
    intro index
    have included : count - index ≤ count := by omega
    exact mul_le_mul_nonnegative_left
      (partial_sum_monotone secondNonnegative included)
      (firstNonnegative index)
  exact le_trans (partial_sum_le pointwise count) (by
    rw [partial_sum_mul_right]
    exact le_refl _)

/-- Every nonnegative square fits inside the triangle at twice the cutoff. -/
public theorem rectangle_le_double_triangle
    {first second : Nat → selection.Carrier}
    (firstNonnegative : ∀ index, le zero (first index))
    (secondNonnegative : ∀ index, le zero (second index))
    (count : Nat) :
    le (mul (partialSum first count) (partialSum second count))
      (partialSum (convolution first second) (count + count)) := by
  rw [partial_sum_convolution_eq_triangleRows]
  unfold triangleRows
  have pointwise : ∀ index,
      index < count →
      le (mul (first index) (partialSum second count))
        (mul (first index)
          (partialSum second (count + count - index))) := by
    intro index earlier
    have included : count ≤ count + count - index := by omega
    exact mul_le_mul_nonnegative_left
      (partial_sum_monotone secondNonnegative included)
      (firstNonnegative index)
  have firstBound : le
      (mul (partialSum first count) (partialSum second count))
      (partialSum
        (fun index => mul (first index)
          (partialSum second (count + count - index))) count) := by
    rw [← partial_sum_mul_right]
    exact partial_sum_le_below count pointwise
  have rowsNonnegative : ∀ index,
      le zero (mul (first index)
        (partialSum second (count + count - index))) := by
    intro index
    exact mul_nonnegative (firstNonnegative index)
      (partial_sum_nonnegative secondNonnegative _)
  exact le_trans firstBound
    (partial_sum_monotone rowsNonnegative (by omega))

private theorem limit_le_of_eventually_le
    {values : Nat → selection.Carrier} {limit upper : selection.Carrier}
    (converges : Problib.Analysis.Real.ConvergesTo values limit)
    (stage : Nat) (bounded : ∀ index, stage ≤ index → le (values index) upper) :
    le limit upper := by
  apply Problib.Analysis.Real.le_of_forall_lt_add
  intro tolerance positive
  rcases converges tolerance positive with ⟨convergesStage, close⟩
  let index := max stage convergesStage
  have near := close index (Nat.le_max_right _ _)
  rw [abs_sub_comm] at near
  have upperNear := (abs_lt.mp near).right
  have summed := add_lt_add_le upperNear
    (bounded index (Nat.le_max_left _ _))
  rw [sub_add_cancel, add_comm tolerance upper] at summed
  exact summed

private theorem le_limit_of_eventually_le
    {values : Nat → selection.Carrier} {limit lower : selection.Carrier}
    (converges : Problib.Analysis.Real.ConvergesTo values limit)
    (stage : Nat) (bounded : ∀ index, stage ≤ index → le lower (values index)) :
    le lower limit := by
  apply Problib.Analysis.Real.le_of_forall_lt_add
  intro tolerance positive
  rcases converges tolerance positive with ⟨convergesStage, close⟩
  let index := max stage convergesStage
  have near := close index (Nat.le_max_right _ _)
  have upperNear := (abs_lt.mp near).right
  have shifted := add_lt_add_right limit upperNear
  rw [sub_add_cancel] at shifted
  have strict := lt_of_le_of_lt
    (bounded index (Nat.le_max_left _ _)) shifted
  rwa [add_comm tolerance limit] at strict

public theorem partial_sum_le_sum_nonnegative
    {values : Nat → selection.Carrier}
    (nonnegative : ∀ index, le zero (values index))
    (certificate : Summable values) (count : Nat) :
    le (partialSum values count) (sum values certificate) :=
  le_limit_of_eventually_le
    (partial_sum_converges values certificate) count
    (fun _ later => partial_sum_monotone nonnegative later)

private theorem sum_nonnegative
    {values : Nat → selection.Carrier}
    (nonnegative : ∀ index, le zero (values index))
    (certificate : Summable values) :
    le zero (sum values certificate) := by
  have included := partial_sum_le_sum_nonnegative nonnegative certificate 0
  rwa [partial_sum_zero] at included

/-- A nonnegative Cauchy convolution has bounded partial sums whenever each
factor is summable. -/
public theorem convolution_summable_nonnegative
    {first second : Nat → selection.Carrier}
    (firstNonnegative : ∀ index, le zero (first index))
    (secondNonnegative : ∀ index, le zero (second index))
    (firstSummable : Summable first)
    (secondSummable : Summable second) :
    Summable (convolution first second) := by
  have firstLimitNonnegative := sum_nonnegative firstNonnegative firstSummable
  apply summable_of_nonnegative_bounded
    (convolution_nonnegative firstNonnegative secondNonnegative)
  refine ⟨mul (sum first firstSummable) (sum second secondSummable),
    fun count => ?_⟩
  have firstBound := partial_sum_le_sum_nonnegative firstNonnegative firstSummable count
  have secondBound := partial_sum_le_sum_nonnegative secondNonnegative secondSummable count
  have rectangleBound : le
      (mul (partialSum first count) (partialSum second count))
      (mul (sum first firstSummable) (sum second secondSummable)) :=
    le_trans
      (mul_le_mul_nonnegative_right firstBound
        (partial_sum_nonnegative secondNonnegative count))
      (mul_le_mul_nonnegative_left secondBound firstLimitNonnegative)
  exact le_trans
    (triangle_le_rectangle firstNonnegative secondNonnegative count)
    rectangleBound

/-- The infinite nonnegative Cauchy product sums to the product of its two
signed-real sums. No extended-real subtraction occurs. -/
public theorem sum_convolution_nonnegative
    {first second : Nat → selection.Carrier}
    (firstNonnegative : ∀ index, le zero (first index))
    (secondNonnegative : ∀ index, le zero (second index))
    (firstSummable : Summable first)
    (secondSummable : Summable second) :
    sum (convolution first second)
        (convolution_summable_nonnegative firstNonnegative
          secondNonnegative firstSummable secondSummable) =
      mul (sum first firstSummable) (sum second secondSummable) := by
  let convolutionCertificate := convolution_summable_nonnegative
    firstNonnegative secondNonnegative firstSummable secondSummable
  have productConverges := converges_to_mul
    (partial_sum_converges first firstSummable)
    (partial_sum_converges second secondSummable)
  have upper : le
      (sum (convolution first second) convolutionCertificate)
      (mul (sum first firstSummable) (sum second secondSummable)) := by
    apply limit_le_of_eventually_le
      (partial_sum_converges (convolution first second)
        convolutionCertificate) 0
    intro count _
    exact le_trans
      (triangle_le_rectangle firstNonnegative secondNonnegative count)
      (le_trans
        (mul_le_mul_nonnegative_right
          (partial_sum_le_sum_nonnegative firstNonnegative firstSummable count)
          (partial_sum_nonnegative secondNonnegative count))
        (mul_le_mul_nonnegative_left
          (partial_sum_le_sum_nonnegative secondNonnegative secondSummable count)
          (sum_nonnegative firstNonnegative firstSummable)))
  have lower : le
      (mul (sum first firstSummable) (sum second secondSummable))
      (sum (convolution first second) convolutionCertificate) := by
    apply limit_le_of_eventually_le productConverges 0
    intro count _
    exact le_trans
      (rectangle_le_double_triangle firstNonnegative secondNonnegative count)
      (partial_sum_le_sum_nonnegative
        (convolution_nonnegative firstNonnegative secondNonnegative)
        convolutionCertificate (count + count))
  exact le_antisymm upper lower

private theorem absolute_values_summable
    {values : Nat → selection.Carrier}
    (certificate : AbsolutelySummable values) :
    Summable (fun index => abs (values index)) := by
  rcases certificate with ⟨upper, bounded⟩
  exact summable_of_nonnegative_bounded
    (fun index => abs_nonnegative (values index))
    ⟨upper, bounded⟩

/-- Absolute convergence of both factors supplies a coefficientwise
nonnegative majorant for the full Cauchy product. -/
public theorem convolution_absolute
    {first second : Nat → selection.Carrier}
    (firstAbsolute : AbsolutelySummable first)
    (secondAbsolute : AbsolutelySummable second) :
    AbsolutelySummable (convolution first second) := by
  let firstMagnitude := fun index => abs (first index)
  let secondMagnitude := fun index => abs (second index)
  have firstSummable := absolute_values_summable firstAbsolute
  have secondSummable := absolute_values_summable secondAbsolute
  have magnitudeNonnegative : ∀ index,
      le zero (convolution firstMagnitude secondMagnitude index) :=
    convolution_nonnegative
      (fun index => abs_nonnegative (first index))
      (fun index => abs_nonnegative (second index))
  have magnitudeSummable : Summable
      (convolution firstMagnitude secondMagnitude) :=
    convolution_summable_nonnegative
      (fun index => abs_nonnegative (first index))
      (fun index => abs_nonnegative (second index))
      firstSummable secondSummable
  refine ⟨sum (convolution firstMagnitude secondMagnitude)
    magnitudeSummable, fun count => ?_⟩
  exact le_trans
    (partial_sum_le (fun index => abs_convolution_le first second index)
      count)
    (partial_sum_le_sum_nonnegative magnitudeNonnegative magnitudeSummable count)

public theorem convolution_summable_absolute
    {first second : Nat → selection.Carrier}
    (firstAbsolute : AbsolutelySummable first)
    (secondAbsolute : AbsolutelySummable second) :
    Summable (convolution first second) :=
  summable_of_absolute_bound
    (convolution_absolute firstAbsolute secondAbsolute)

private theorem positive_part_summable_of_absolute
    {values : Nat → selection.Carrier}
    (certificate : AbsolutelySummable values) :
    Summable (fun index => positivePart (values index)) := by
  rcases certificate with ⟨upper, bounded⟩
  exact summable_of_nonnegative_bounded
    (fun index => positive_part_nonnegative (values index))
    ⟨upper, fun count => le_trans
      (partial_sum_le
        (fun index => positive_part_le_abs (values index)) count)
      (bounded count)⟩

private theorem negative_part_summable_of_absolute
    {values : Nat → selection.Carrier}
    (certificate : AbsolutelySummable values) :
    Summable (fun index => negativePart (values index)) := by
  rcases certificate with ⟨upper, bounded⟩
  exact summable_of_nonnegative_bounded
    (fun index => negative_part_nonnegative (values index))
    ⟨upper, fun count => le_trans
      (partial_sum_le
        (fun index => negative_part_le_abs (values index)) count)
      (bounded count)⟩

private theorem sum_congr {first second : Nat → selection.Carrier}
    (equal : first = second)
    (firstSummable : Summable first) (secondSummable : Summable second) :
    sum first firstSummable = sum second secondSummable := by
  cases equal
  rfl

private theorem sum_sub {first second : Nat → selection.Carrier}
    (firstSummable : Summable first) (secondSummable : Summable second) :
    sum (fun index => sub (first index) (second index))
        (summable_sub firstSummable secondSummable) =
      sub (sum first firstSummable) (sum second secondSummable) := by
  have termsEqual :
      (fun index => sub (first index) (second index)) =
      (fun index => add (first index) (neg (second index))) := by
    funext index
    exact sub_eq_add_neg _ _
  calc
    sum (fun index => sub (first index) (second index))
        (summable_sub firstSummable secondSummable) =
      sum (fun index => add (first index) (neg (second index)))
        (summable_add firstSummable (summable_neg secondSummable)) :=
      sum_congr termsEqual _ _
    _ = add (sum first firstSummable)
        (sum (fun index => neg (second index))
          (summable_neg secondSummable)) :=
      sum_add firstSummable (summable_neg secondSummable)
    _ = sub (sum first firstSummable) (sum second secondSummable) := by
      rw [sum_neg, sub_eq_add_neg]

private theorem sum_positive_sub_negative
    {values : Nat → selection.Carrier}
    (absolute : AbsolutelySummable values) :
    sum values (summable_of_absolute_bound absolute) =
      sub
        (sum (fun index => positivePart (values index))
          (positive_part_summable_of_absolute absolute))
        (sum (fun index => negativePart (values index))
          (negative_part_summable_of_absolute absolute)) := by
  let positiveSummable := positive_part_summable_of_absolute absolute
  let negativeSummable := negative_part_summable_of_absolute absolute
  have termsEqual : values =
      (fun index => sub (positivePart (values index))
        (negativePart (values index))) := by
    funext index
    exact (positive_sub_negative (values index)).symm
  calc
    sum values (summable_of_absolute_bound absolute) =
      sum (fun index => sub (positivePart (values index))
        (negativePart (values index)))
        (summable_sub positiveSummable negativeSummable) :=
      sum_congr termsEqual _ _
    _ = _ := sum_sub positiveSummable negativeSummable

/-- Absolutely convergent signed series obey the infinite Cauchy-product
identity. The proof reduces the four signed quadrants to the nonnegative
triangle/square comparison, then reconstructs each signed sum. -/
public theorem sum_convolution_absolute
    {first second : Nat → selection.Carrier}
    (firstAbsolute : AbsolutelySummable first)
    (secondAbsolute : AbsolutelySummable second) :
    sum (convolution first second)
        (convolution_summable_absolute firstAbsolute secondAbsolute) =
      mul (sum first (summable_of_absolute_bound firstAbsolute))
        (sum second (summable_of_absolute_bound secondAbsolute)) := by
  let firstPositive := fun index => positivePart (first index)
  let firstNegative := fun index => negativePart (first index)
  let secondPositive := fun index => positivePart (second index)
  let secondNegative := fun index => negativePart (second index)
  have firstPositiveSummable :=
    positive_part_summable_of_absolute firstAbsolute
  have firstNegativeSummable :=
    negative_part_summable_of_absolute firstAbsolute
  have secondPositiveSummable :=
    positive_part_summable_of_absolute secondAbsolute
  have secondNegativeSummable :=
    negative_part_summable_of_absolute secondAbsolute
  have firstPositiveNonnegative : ∀ index,
      le zero (firstPositive index) :=
    fun index => positive_part_nonnegative (first index)
  have firstNegativeNonnegative : ∀ index,
      le zero (firstNegative index) :=
    fun index => negative_part_nonnegative (first index)
  have secondPositiveNonnegative : ∀ index,
      le zero (secondPositive index) :=
    fun index => positive_part_nonnegative (second index)
  have secondNegativeNonnegative : ∀ index,
      le zero (secondNegative index) :=
    fun index => negative_part_nonnegative (second index)
  let pp := convolution firstPositive secondPositive
  let pn := convolution firstPositive secondNegative
  let np := convolution firstNegative secondPositive
  let nn := convolution firstNegative secondNegative
  have ppSummable := convolution_summable_nonnegative
    firstPositiveNonnegative secondPositiveNonnegative
    firstPositiveSummable secondPositiveSummable
  have pnSummable := convolution_summable_nonnegative
    firstPositiveNonnegative secondNegativeNonnegative
    firstPositiveSummable secondNegativeSummable
  have npSummable := convolution_summable_nonnegative
    firstNegativeNonnegative secondPositiveNonnegative
    firstNegativeSummable secondPositiveSummable
  have nnSummable := convolution_summable_nonnegative
    firstNegativeNonnegative secondNegativeNonnegative
    firstNegativeSummable secondNegativeSummable
  let firstDifference := summable_sub ppSummable pnSummable
  let secondDifference := summable_sub npSummable nnSummable
  let combined := summable_sub firstDifference secondDifference
  have firstEqual : first =
      (fun index => sub (firstPositive index) (firstNegative index)) := by
    funext index
    exact (positive_sub_negative (first index)).symm
  have secondEqual : second =
      (fun index => sub (secondPositive index) (secondNegative index)) := by
    funext index
    exact (positive_sub_negative (second index)).symm
  have convolutionEqual : convolution first second =
      (fun index => sub (sub (pp index) (pn index))
        (sub (np index) (nn index))) := by
    funext index
    have expanded : convolution first second index =
        convolution
          (fun index => sub (firstPositive index) (firstNegative index))
          (fun index => sub (secondPositive index) (secondNegative index))
          index := by
      rw [← firstEqual, ← secondEqual]
    rw [expanded]
    rw [convolution_sub_left,
      convolution_sub_right, convolution_sub_right]
  calc
    sum (convolution first second)
        (convolution_summable_absolute firstAbsolute secondAbsolute) =
      sum (fun index => sub (sub (pp index) (pn index))
        (sub (np index) (nn index))) combined :=
      sum_congr convolutionEqual _ _
    _ = sub
        (sum (fun index => sub (pp index) (pn index)) firstDifference)
        (sum (fun index => sub (np index) (nn index)) secondDifference) :=
      sum_sub firstDifference secondDifference
    _ = sub (sub (sum pp ppSummable) (sum pn pnSummable))
        (sub (sum np npSummable) (sum nn nnSummable)) := by
      rw [sum_sub ppSummable pnSummable,
        sum_sub npSummable nnSummable]
    _ = sub
        (sub
          (mul (sum firstPositive firstPositiveSummable)
            (sum secondPositive secondPositiveSummable))
          (mul (sum firstPositive firstPositiveSummable)
            (sum secondNegative secondNegativeSummable)))
        (sub
          (mul (sum firstNegative firstNegativeSummable)
            (sum secondPositive secondPositiveSummable))
          (mul (sum firstNegative firstNegativeSummable)
            (sum secondNegative secondNegativeSummable))) := by
      rw [sum_convolution_nonnegative
        firstPositiveNonnegative secondPositiveNonnegative
        firstPositiveSummable secondPositiveSummable,
        sum_convolution_nonnegative
        firstPositiveNonnegative secondNegativeNonnegative
        firstPositiveSummable secondNegativeSummable,
        sum_convolution_nonnegative
        firstNegativeNonnegative secondPositiveNonnegative
        firstNegativeSummable secondPositiveSummable,
        sum_convolution_nonnegative
        firstNegativeNonnegative secondNegativeNonnegative
        firstNegativeSummable secondNegativeSummable]
    _ = mul
        (sub (sum firstPositive firstPositiveSummable)
          (sum firstNegative firstNegativeSummable))
        (sub (sum secondPositive secondPositiveSummable)
          (sum secondNegative secondNegativeSummable)) := by
      rw [sub_mul, mul_sub, mul_sub]
    _ = mul (sum first (summable_of_absolute_bound firstAbsolute))
        (sum second (summable_of_absolute_bound secondAbsolute)) := by
      rw [sum_positive_sub_negative firstAbsolute,
        sum_positive_sub_negative secondAbsolute]

end

end Problib.Analysis.Real.SignedSeries
