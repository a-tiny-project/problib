module

public import Problib.Analysis.Real.MonotoneSequence
public import Problib.Analysis.Real.Cauchy

/-! Signed series on problib's sealed real carrier.

The nonnegative `ENNReal.tsum` is defined even when it is infinite. A signed
series instead carries an explicit convergence certificate, so subtraction is
never performed on infinite sums. Its partial sums use the same count convention
as `ENNReal.partialSum`: the value at `count` sums indices below `count`.
-/

set_option autoImplicit false

namespace Problib.Analysis.Real.SignedSeries

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real

noncomputable section

private instance : Std.Associative (α := selection.Carrier) add :=
  ⟨fun left middle right => add_assoc left middle right⟩

private instance : Std.Commutative (α := selection.Carrier) add :=
  ⟨add_comm⟩

/-- A constant real sequence converges to its value. -/
public theorem converges_to_const (value : selection.Carrier) :
    ConvergesTo (fun _ : Nat => value) value := by
  intro epsilon positive
  refine ⟨0, fun _ _ => ?_⟩
  rw [sub_self, abs_zero]
  exact positive

/-- A real sequence has at most one limit. -/
public theorem converges_to_unique {values : Nat → selection.Carrier}
    {first second : selection.Carrier}
    (firstLimit : ConvergesTo values first)
    (secondLimit : ConvergesTo values second) : first = second := by
  classical
  apply Classical.byContradiction
  intro distinct
  have gapPositive : lt zero (abs (sub first second)) :=
    abs_positive_of_nonzero (fun vanished => distinct (by
      have shifted : add second (sub first second) = add second zero :=
        congrArg (fun value => add second value) vanished
      rwa [add_sub_cancel, add_zero] at shifted))
  have tolerancePositive := half_positive gapPositive
  rcases firstLimit _ tolerancePositive with ⟨firstStage, firstBound⟩
  rcases secondLimit _ tolerancePositive with ⟨secondStage, secondBound⟩
  let stage := max firstStage secondStage
  have firstClose := firstBound stage (Nat.le_max_left _ _)
  have secondClose := secondBound stage (Nat.le_max_right _ _)
  have triangle := abs_add_le (sub first (values stage)) (sub (values stage) second)
  rw [sub_add_sub, abs_sub_comm first (values stage)] at triangle
  have strict := add_lt_add firstClose secondClose
  rw [add_half] at strict
  exact lt_irrefl _ (lt_of_le_of_lt triangle strict)

/-- Addition preserves convergence of signed real sequences. -/
public theorem converges_to_add {first second : Nat → selection.Carrier}
    {firstLimit secondLimit : selection.Carrier}
    (firstConverges : ConvergesTo first firstLimit)
    (secondConverges : ConvergesTo second secondLimit) :
    ConvergesTo (fun index => add (first index) (second index))
      (add firstLimit secondLimit) := by
  intro epsilon positive
  have tolerancePositive := half_positive positive
  rcases firstConverges _ tolerancePositive with ⟨firstStage, firstBound⟩
  rcases secondConverges _ tolerancePositive with ⟨secondStage, secondBound⟩
  refine ⟨max firstStage secondStage, fun index later => ?_⟩
  have firstLater := Nat.le_trans (Nat.le_max_left _ _) later
  have secondLater := Nat.le_trans (Nat.le_max_right _ _) later
  have split : sub (add (first index) (second index))
      (add firstLimit secondLimit) =
      add (sub (first index) firstLimit) (sub (second index) secondLimit) := by
    simp only [sub_eq_add_neg, neg_add]
    ac_rfl
  rw [split]
  have triangle := abs_add_le (sub (first index) firstLimit)
    (sub (second index) secondLimit)
  have strict := add_lt_add (firstBound index firstLater)
    (secondBound index secondLater)
  rw [add_half] at strict
  exact lt_of_le_of_lt triangle strict

/-- Negation preserves convergence of signed real sequences. -/
public theorem converges_to_neg {values : Nat → selection.Carrier}
    {limit : selection.Carrier} (converges : ConvergesTo values limit) :
    ConvergesTo (fun index => neg (values index)) (neg limit) := by
  intro epsilon positive
  rcases converges epsilon positive with ⟨stage, bound⟩
  refine ⟨stage, fun index later => ?_⟩
  have split : sub (neg (values index)) (neg limit) =
      neg (sub (values index) limit) := by
    rw [sub_eq_add_neg, sub_eq_add_neg, neg_add, neg_neg]
  rw [split, abs_neg]
  exact bound index later

/-- Multiplication by a fixed real preserves convergence. -/
public theorem converges_to_scale {values : Nat → selection.Carrier}
    {limit : selection.Carrier} (factor : selection.Carrier)
    (converges : ConvergesTo values limit) :
    ConvergesTo (fun index => mul factor (values index)) (mul factor limit) := by
  intro epsilon positive
  let bound := add (abs factor) one
  have boundPositive : lt zero bound := by
    have raised := add_lt_add_left (abs factor) one_positive
    exact lt_of_le_of_lt (abs_nonnegative factor) (by
      rwa [add_zero] at raised)
  have boundNonzero : bound ≠ zero := by
    intro vanished
    have copy := boundPositive
    rw [vanished] at copy
    exact lt_irrefl zero copy
  have tolerancePositive : lt zero (div epsilon bound) :=
    div_positive positive boundPositive
  rcases converges _ tolerancePositive with ⟨stage, close⟩
  refine ⟨stage, fun index later => ?_⟩
  rw [← mul_sub, abs_mul]
  have factorBound : le (abs factor) bound := by
    have raised := add_lt_add_left (abs factor) one_positive
    exact le_of_lt (by rwa [add_zero] at raised)
  have small := close index later
  have scaled := mul_lt_mul_positive_left small boundPositive
  rw [mul_div_cancel epsilon boundNonzero] at scaled
  exact lt_of_le_of_lt
    (mul_le_mul_nonnegative_right factorBound
      (abs_nonnegative (sub (values index) limit))) scaled

public theorem converges_to_sub {first second : Nat → selection.Carrier}
    {firstLimit secondLimit : selection.Carrier}
    (firstConverges : ConvergesTo first firstLimit)
    (secondConverges : ConvergesTo second secondLimit) :
    ConvergesTo (fun index => sub (first index) (second index))
      (sub firstLimit secondLimit) := by
  simpa only [sub_eq_add_neg] using
    converges_to_add firstConverges (converges_to_neg secondConverges)

public theorem converges_to_shift {values : Nat → selection.Carrier}
    {limit : selection.Carrier} (converges : ConvergesTo values limit) :
    ConvergesTo (fun index => values (index + 1)) limit := by
  intro epsilon positive
  rcases converges epsilon positive with ⟨stage, close⟩
  exact ⟨stage, fun index later => close (index + 1)
    (Nat.le_succ_of_le later)⟩

/-- The signed sum of the first `count` coefficients. -/
@[expose] public def partialSum (values : Nat → selection.Carrier) :
    Nat → selection.Carrier
  | 0 => zero
  | count + 1 => add (partialSum values count) (values count)

public theorem partial_sum_zero (values : Nat → selection.Carrier) :
    partialSum values 0 = zero := rfl

public theorem partial_sum_succ (values : Nat → selection.Carrier) (count : Nat) :
    partialSum values (count + 1) = add (partialSum values count) (values count) := rfl

public theorem partial_sum_add (first second : Nat → selection.Carrier)
    (count : Nat) :
    partialSum (fun index => add (first index) (second index)) count =
      add (partialSum first count) (partialSum second count) := by
  induction count with
  | zero => simp only [partialSum, zero_add]
  | succ count induction =>
      simp only [partial_sum_succ, induction]
      ac_rfl

public theorem partial_sum_neg (values : Nat → selection.Carrier)
    (count : Nat) :
    partialSum (fun index => neg (values index)) count =
      neg (partialSum values count) := by
  induction count with
  | zero => simp only [partialSum, neg_zero]
  | succ count induction =>
      simp only [partial_sum_succ, induction, neg_add]

public theorem partial_sum_scale (factor : selection.Carrier)
    (values : Nat → selection.Carrier) (count : Nat) :
    partialSum (fun index => mul factor (values index)) count =
      mul factor (partialSum values count) := by
  induction count with
  | zero => simp only [partialSum, mul_zero]
  | succ count induction =>
      simp only [partial_sum_succ, induction, mul_add]

public theorem partial_sum_append (values : Nat → selection.Carrier)
    (start count : Nat) :
    partialSum values (start + count) =
      add (partialSum values start)
        (partialSum (fun index => values (start + index)) count) := by
  induction count with
  | zero => rw [Nat.add_zero, partialSum, add_zero]
  | succ count induction =>
      rw [Nat.add_succ, partial_sum_succ, induction, partial_sum_succ, add_assoc]

public theorem partial_sum_zero_after {values : Nat → selection.Carrier}
    {cutoff : Nat} (zeroAfter : ∀ index, cutoff ≤ index → values index = zero)
    {count : Nat} (later : cutoff ≤ count) :
    partialSum values count = partialSum values cutoff := by
  have tailZero : ∀ length,
      partialSum (fun index => values (cutoff + index)) length = zero := by
    intro length
    induction length with
    | zero => rfl
    | succ length induction =>
        rw [partial_sum_succ, induction, zeroAfter (cutoff + length)
          (Nat.le_add_right _ _), add_zero]
  have countEq : cutoff + (count - cutoff) = count := Nat.add_sub_of_le later
  calc
    partialSum values count = partialSum values (cutoff + (count - cutoff)) := by
      rw [countEq]
    _ = add (partialSum values cutoff)
          (partialSum (fun index => values (cutoff + index)) (count - cutoff)) :=
      partial_sum_append values cutoff (count - cutoff)
    _ = partialSum values cutoff := by rw [tailZero, add_zero]

public theorem partial_sum_monotone {values : Nat → selection.Carrier}
    (nonnegative : ∀ index, le zero (values index))
    {first second : Nat} (included : first ≤ second) :
    le (partialSum values first) (partialSum values second) := by
  have step (index : Nat) :
      le (partialSum values index) (partialSum values (index + 1)) := by
    rw [partial_sum_succ]
    have raised := (add_le_add_left_iff (shift := partialSum values index)).mpr
      (nonnegative index)
    rwa [add_zero] at raised
  induction included with
  | refl => exact le_refl _
  | step _ prior => exact le_trans prior (step _)

public theorem partial_sum_nonnegative {values : Nat → selection.Carrier}
    (nonnegative : ∀ index, le zero (values index)) (count : Nat) :
    le zero (partialSum values count) := by
  induction count with
  | zero => exact le_refl zero
  | succ count induction =>
      rw [partial_sum_succ]
      exact add_nonnegative induction (nonnegative count)

public theorem partial_sum_le {first second : Nat → selection.Carrier}
    (terms : ∀ index, le (first index) (second index)) (count : Nat) :
    le (partialSum first count) (partialSum second count) := by
  induction count with
  | zero => exact le_refl _
  | succ count induction =>
      rw [partial_sum_succ, partial_sum_succ]
      exact add_le_add induction (terms count)

/-- Positive and negative parts are kept in the signed carrier so their
partial sums can be compared to an absolute majorant. -/
@[expose] public noncomputable def positivePart (value : selection.Carrier) :
    selection.Carrier := by
  classical
  exact if le zero value then value else zero

@[expose] public noncomputable def negativePart (value : selection.Carrier) :
    selection.Carrier := by
  classical
  exact if le zero value then zero else neg value

public theorem positive_part_nonnegative (value : selection.Carrier) :
    le zero (positivePart value) := by
  classical
  by_cases nonnegative : le zero value
  · simp only [positivePart, if_pos nonnegative]
    exact nonnegative
  · simp only [positivePart, if_neg nonnegative]
    exact le_refl zero

public theorem negative_part_nonnegative (value : selection.Carrier) :
    le zero (negativePart value) := by
  classical
  by_cases nonnegative : le zero value
  · simp only [negativePart, if_pos nonnegative]
    exact le_refl zero
  · simp only [negativePart, if_neg nonnegative]
    exact neg_nonnegative_iff.mpr (le_of_lt (lt_of_not_le nonnegative))

public theorem positive_part_le_abs (value : selection.Carrier) :
    le (positivePart value) (abs value) := by
  classical
  by_cases nonnegative : le zero value
  · rw [positivePart, if_pos nonnegative, abs_of_nonnegative nonnegative]
    exact le_refl _
  · rw [positivePart, if_neg nonnegative]
    exact abs_nonnegative value

public theorem negative_part_le_abs (value : selection.Carrier) :
    le (negativePart value) (abs value) := by
  classical
  by_cases nonnegative : le zero value
  · rw [negativePart, if_pos nonnegative]
    exact abs_nonnegative value
  · have nonpositive := le_of_lt (lt_of_not_le nonnegative)
    rw [negativePart, if_neg nonnegative, abs_of_nonpositive nonpositive]
    exact le_refl _

public theorem positive_sub_negative (value : selection.Carrier) :
    sub (positivePart value) (negativePart value) = value := by
  classical
  by_cases nonnegative : le zero value
  · rw [positivePart, negativePart, if_pos nonnegative, if_pos nonnegative, sub_zero]
  · rw [positivePart, negativePart, if_neg nonnegative, if_neg nonnegative,
      zero_sub, neg_neg]

public theorem partial_sum_sub (first second : Nat → selection.Carrier)
    (count : Nat) :
    partialSum (fun index => sub (first index) (second index)) count =
      sub (partialSum first count) (partialSum second count) := by
  simp only [sub_eq_add_neg, partial_sum_add, partial_sum_neg]

/-- `Summable` holds when signed partial sums have a real limit. -/
@[expose] public def Summable (values : Nat → selection.Carrier) : Prop :=
  ∃ total : selection.Carrier, ConvergesTo (partialSum values) total

@[expose] public def CauchyPartialSums (values : Nat → selection.Carrier) : Prop :=
  Cauchy (partialSum values)

public theorem summable_cauchy {values : Nat → selection.Carrier}
    (certificate : Summable values) : CauchyPartialSums values := by
  rcases certificate with ⟨total, converges⟩
  intro epsilon positive
  have halfPositive := half_positive positive
  rcases converges _ halfPositive with ⟨stage, close⟩
  refine ⟨stage, fun first second firstLater secondLater => ?_⟩
  have triangle := abs_add_le (sub (partialSum values first) total)
    (sub total (partialSum values second))
  rw [sub_add_sub, abs_sub_comm total (partialSum values second)] at triangle
  have strict := add_lt_add (close first firstLater) (close second secondLater)
  rw [add_half] at strict
  exact lt_of_le_of_lt triangle strict

/-- Cauchy partial sums converge on the sealed real carrier. -/
public theorem summable_of_cauchy {values : Nat → selection.Carrier}
    (cauchy : CauchyPartialSums values) : Summable values :=
  cauchy_converges cauchy

/-- Terms of a convergent signed series tend to zero. -/
public theorem terms_converge_zero {values : Nat → selection.Carrier}
    (certificate : Summable values) : ConvergesTo values zero := by
  rcases certificate with ⟨total, converges⟩
  have differences := converges_to_sub (converges_to_shift converges) converges
  rw [sub_self] at differences
  have equal :
      (fun index => sub (partialSum values (index + 1))
        (partialSum values index)) = values := by
    funext index
    rw [partial_sum_succ, add_sub_self]
  rw [equal] at differences
  exact differences

/-- The value of a summable signed series, with its certificate explicit. -/
@[expose] public noncomputable def sum (values : Nat → selection.Carrier)
    (certificate : Summable values) : selection.Carrier :=
  Classical.choose certificate

public theorem partial_sum_converges (values : Nat → selection.Carrier)
    (certificate : Summable values) :
    ConvergesTo (partialSum values) (sum values certificate) :=
  Classical.choose_spec certificate

public theorem sum_eq_of_converges (values : Nat → selection.Carrier)
    (certificate : Summable values) {total : selection.Carrier}
    (converges : ConvergesTo (partialSum values) total) :
    sum values certificate = total :=
  converges_to_unique (partial_sum_converges values certificate) converges

public theorem summable_add {first second : Nat → selection.Carrier}
    (firstSummable : Summable first) (secondSummable : Summable second) :
    Summable (fun index => add (first index) (second index)) := by
  rcases firstSummable with ⟨firstTotal, firstConverges⟩
  rcases secondSummable with ⟨secondTotal, secondConverges⟩
  refine ⟨add firstTotal secondTotal, ?_⟩
  have combined := converges_to_add firstConverges secondConverges
  have equal :
      (fun count => partialSum (fun index => add (first index) (second index)) count) =
        (fun count => add (partialSum first count) (partialSum second count)) := by
    funext count
    exact partial_sum_add first second count
  change ConvergesTo
    (fun count => partialSum (fun index => add (first index) (second index)) count)
    (add firstTotal secondTotal)
  rw [equal]
  exact combined

public theorem summable_neg {values : Nat → selection.Carrier}
    (certificate : Summable values) :
    Summable (fun index => neg (values index)) := by
  rcases certificate with ⟨total, converges⟩
  refine ⟨neg total, ?_⟩
  have negated := converges_to_neg converges
  have equal :
      (fun count => partialSum (fun index => neg (values index)) count) =
        (fun count => neg (partialSum values count)) := by
    funext count
    exact partial_sum_neg values count
  change ConvergesTo
    (fun count => partialSum (fun index => neg (values index)) count) (neg total)
  rw [equal]
  exact negated

public theorem summable_scale {values : Nat → selection.Carrier}
    (factor : selection.Carrier) (certificate : Summable values) :
    Summable (fun index => mul factor (values index)) := by
  rcases certificate with ⟨total, converges⟩
  refine ⟨mul factor total, ?_⟩
  have scaled := converges_to_scale factor converges
  have equal :
      (fun count => partialSum (fun index => mul factor (values index)) count) =
        (fun count => mul factor (partialSum values count)) := by
    funext count
    exact partial_sum_scale factor values count
  change ConvergesTo
    (fun count => partialSum (fun index => mul factor (values index)) count)
    (mul factor total)
  rw [equal]
  exact scaled

public theorem summable_sub {first second : Nat → selection.Carrier}
    (firstSummable : Summable first) (secondSummable : Summable second) :
    Summable (fun index => sub (first index) (second index)) := by
  have combined := summable_add firstSummable (summable_neg secondSummable)
  simpa only [sub_eq_add_neg] using combined

public theorem summable_of_eventually_zero {values : Nat → selection.Carrier}
    {cutoff : Nat} (zeroAfter : ∀ index, cutoff ≤ index → values index = zero) :
    Summable values := by
  refine ⟨partialSum values cutoff, ?_⟩
  intro epsilon positive
  refine ⟨cutoff, fun index later => ?_⟩
  rw [partial_sum_zero_after zeroAfter later, sub_self, abs_zero]
  exact positive

/-- Dedekind completeness supplies the sum of bounded nonnegative partial sums. -/
public theorem summable_of_nonnegative_bounded {values : Nat → selection.Carrier}
    (nonnegative : ∀ index, le zero (values index))
    (bounded : ∃ upper : selection.Carrier,
      ∀ count, le (partialSum values count) upper) :
    Summable values :=
  monotone_bounded_converges (partialSum values)
    (fun _ _ included => partial_sum_monotone nonnegative included) bounded

/-- Absolute summability is a real bound on every partial sum of magnitudes. -/
@[expose] public def AbsolutelySummable (values : Nat → selection.Carrier) : Prop :=
  ∃ upper : selection.Carrier,
    ∀ count, le (partialSum (fun index => abs (values index)) count) upper

/-- A bounded absolute majorant gives a signed sum, without subtracting
infinite extended-nonnegative values. -/
public theorem summable_of_absolute_bound {values : Nat → selection.Carrier}
    (absolute : AbsolutelySummable values) : Summable values := by
  rcases absolute with ⟨upper, upperBound⟩
  have positiveSummable : Summable (fun index => positivePart (values index)) :=
    summable_of_nonnegative_bounded
      (fun index => positive_part_nonnegative (values index))
      ⟨upper, fun count => le_trans
        (partial_sum_le (fun index => positive_part_le_abs (values index)) count)
        (upperBound count)⟩
  have negativeSummable : Summable (fun index => negativePart (values index)) :=
    summable_of_nonnegative_bounded
      (fun index => negative_part_nonnegative (values index))
      ⟨upper, fun count => le_trans
        (partial_sum_le (fun index => negative_part_le_abs (values index)) count)
        (upperBound count)⟩
  have combined := summable_sub positiveSummable negativeSummable
  have same : values = fun index =>
      sub (positivePart (values index)) (negativePart (values index)) := by
    funext index
    exact (positive_sub_negative (values index)).symm
  rw [same]
  exact combined

/-- A bounded nonnegative series controls a signed series term by term. -/
public theorem summable_of_majorant {values majorant : Nat → selection.Carrier}
    (dominates : ∀ index, le (abs (values index)) (majorant index))
    (bounded : ∃ upper : selection.Carrier,
      ∀ count, le (partialSum majorant count) upper) :
    Summable values := by
  rcases bounded with ⟨upper, upperBound⟩
  apply summable_of_absolute_bound
  exact ⟨upper, fun count => le_trans (partial_sum_le dominates count)
    (upperBound count)⟩

public theorem sum_add {first second : Nat → selection.Carrier}
    (firstSummable : Summable first) (secondSummable : Summable second) :
    sum (fun index => add (first index) (second index))
      (summable_add firstSummable secondSummable) =
      add (sum first firstSummable) (sum second secondSummable) := by
  apply sum_eq_of_converges
  have combined := converges_to_add
    (partial_sum_converges first firstSummable)
    (partial_sum_converges second secondSummable)
  have equal :
      (fun count => partialSum (fun index => add (first index) (second index)) count) =
        (fun count => add (partialSum first count) (partialSum second count)) := by
    funext count
    exact partial_sum_add first second count
  change ConvergesTo
    (fun count => partialSum (fun index => add (first index) (second index)) count)
    (add (sum first firstSummable) (sum second secondSummable))
  rw [equal]
  exact combined

public theorem sum_neg {values : Nat → selection.Carrier}
    (certificate : Summable values) :
    sum (fun index => neg (values index)) (summable_neg certificate) =
      neg (sum values certificate) := by
  apply sum_eq_of_converges
  have negated := converges_to_neg (partial_sum_converges values certificate)
  have equal :
      (fun count => partialSum (fun index => neg (values index)) count) =
        (fun count => neg (partialSum values count)) := by
    funext count
    exact partial_sum_neg values count
  change ConvergesTo
    (fun count => partialSum (fun index => neg (values index)) count)
    (neg (sum values certificate))
  rw [equal]
  exact negated

public theorem sum_scale {values : Nat → selection.Carrier}
    (factor : selection.Carrier) (certificate : Summable values) :
    sum (fun index => mul factor (values index))
      (summable_scale factor certificate) =
      mul factor (sum values certificate) := by
  apply sum_eq_of_converges
  have scaled := converges_to_scale factor
    (partial_sum_converges values certificate)
  have equal :
      (fun count => partialSum (fun index => mul factor (values index)) count) =
        (fun count => mul factor (partialSum values count)) := by
    funext count
    exact partial_sum_scale factor values count
  change ConvergesTo
    (fun count => partialSum (fun index => mul factor (values index)) count)
    (mul factor (sum values certificate))
  rw [equal]
  exact scaled

end

end Problib.Analysis.Real.SignedSeries
