module

public import Foundations.Real.Series.Tail

set_option autoImplicit false

namespace Foundations.Real.Coding

open ENNReal

/-- Dyadic weight assigned to the given Boolean coordinate index. -/
@[expose] public noncomputable def weight (index : Nat) : ENNReal :=
  finite (NNReal.dyadic NNReal.one (2 * index + 1))

private noncomputable def budget (index : Nat) : ENNReal :=
  finite (NNReal.dyadic NNReal.one (2 * index))

private theorem weight_add_budget (index : Nat) :
    le (add (weight index) (budget (index + 1))) (budget index) := by
  have successor : 2 * (index + 1) = (2 * index + 1) + 1 := by omega
  have bound := NNReal.addLeAddLeft
    (NNReal.halfLe (NNReal.half (NNReal.dyadic NNReal.one (2 * index))))
    (NNReal.half (NNReal.dyadic NNReal.one (2 * index)))
  rw [NNReal.halfAddHalf] at bound
  simpa only [weight, budget, successor, NNReal.dyadic, le, add] using bound

private theorem weight_not_le_budget (index : Nat) :
    ¬le (weight index) (budget (index + 1)) := by
  have successor : 2 * (index + 1) = (2 * index + 1) + 1 := by omega
  have less := NNReal.halfLt (NNReal.dyadicPositive NNReal.onePositive (2 * index + 1))
  simpa only [weight, budget, successor, NNReal.dyadic, le, add] using less.2

/-- Contribution of coordinate index to the coded series, either its weight or zero. -/
@[expose] public noncomputable def term (bits : Nat → Bool) (index : Nat) : ENNReal :=
  if bits index = true then weight index else zero

/-- Each coordinate term is bounded above by its dyadic weight. -/
public theorem term_le_weight (bits : Nat → Bool) (index : Nat) :
    le (term bits index) (weight index) := by
  unfold term
  split
  · exact leRefl _
  · exact zeroLe _

/-- Extended real sum of weighted Boolean stream terms. -/
@[expose] public noncomputable def encode (bits : Nat → Bool) : ENNReal :=
  tsum (term bits)

private theorem partialSum_add_budget (bits : Nat → Bool) (start count : Nat) :
    le (add (partialSum (fun index => term bits (start + index)) count)
      (budget (start + count))) (budget start) := by
  induction count with
  | zero =>
      rw [partialSum, zeroAdd, Nat.add_zero]
      exact leRefl _
  | succ count induction =>
      rw [partialSum, addAssoc, Nat.add_succ]
      exact leTrans (addLeAddLeft
        (leTrans (addLeAddRight (term_le_weight bits (start + count)) _)
          (weight_add_budget (start + count))) _) induction

private theorem tail_le_budget (bits : Nat → Bool) (start : Nat) :
    le (tsum (fun index => term bits (start + index))) (budget start) := by
  apply tsumLe
  intro count
  have bound := addLeAddLeft (zeroLe (budget (start + count)))
    (partialSum (fun index => term bits (start + index)) count)
  rw [addZero] at bound
  exact leTrans bound (partialSum_add_budget bits start count)

/-- The sum of all weighted bits is bounded above by one. -/
public theorem encode_le_one (bits : Nat → Bool) : le (encode bits) one := by
  simpa only [encode, budget, Nat.mul_zero, NNReal.dyadic, Nat.zero_add, one] using tail_le_budget bits 0

/-- The encoded sum of any Boolean stream is finite. -/
public theorem encode_finite (bits : Nat → Bool) : Finite (encode bits) :=
  finiteOfLe (encode_le_one bits) True.intro

/-- Every finite prefix sum of weighted bits is finite. -/
public theorem prefix_finite (bits : Nat → Bool) (count : Nat) :
    Finite (partialSum (term bits) count) :=
  finiteOfLe (partialSumLeTsum (term bits) count) (encode_finite bits)

/-- A bit is true if and only if the prefix sum plus its weight does not exceed the total sum. -/
public theorem threshold_iff (bits : Nat → Bool) (index : Nat) :
    le (add (partialSum (term bits) index) (weight index)) (encode bits) ↔
      bits index = true := by
  constructor
  · intro included
    apply Classical.byContradiction
    intro missing
    have decomposition := partialSumAddTail (term bits) (index + 1)
    rw [partialSum, term, if_neg missing, addZero] at decomposition
    have bound : le (add (partialSum (term bits) index) (weight index))
        (add (partialSum (term bits) index) (budget (index + 1))) := by
      apply leTrans included
      rw [encode, ← decomposition]
      exact addLeAddLeft (tail_le_budget bits (index + 1)) _
    exact weight_not_le_budget index
      (leOfAddLeAddLeftOfFinite (prefix_finite bits index) bound)
  · intro present
    have bound := partialSumLeTsum (term bits) (index + 1)
    rw [partialSum, term, if_pos present] at bound
    exact bound

/-- Prefix sum reconstructed iteratively from an extended real value. -/
@[expose] public noncomputable def decodedPrefix (value : ENNReal) : Nat → ENNReal
  | 0 => zero
  | index + 1 => by
      classical
      exact add (decodedPrefix value index)
        (if le (add (decodedPrefix value index) (weight index)) value then weight index else zero)

/-- Boolean coordinate recovered by comparing the prefix sum plus weight against the total value. -/
@[expose] public noncomputable def digit (value : ENNReal) (index : Nat) : Bool := by
  classical
  exact decide (le (add (decodedPrefix value index) (weight index)) value)

/-- Reconstructing the prefix sum from an encoded stream matches the original prefix sum. -/
public theorem prefix_encode (bits : Nat → Bool) (count : Nat) :
    decodedPrefix (encode bits) count = partialSum (term bits) count := by
  classical
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [decodedPrefix, induction, partialSum, term]
      by_cases present : bits count = true
      · rw [if_pos present, if_pos ((threshold_iff bits count).mpr present)]
      · rw [if_neg present, if_neg (fun included => present ((threshold_iff bits count).mp included))]

/-- Decoding the digit of an encoded stream recovers the original coordinate bit. -/
public theorem digit_encode (bits : Nat → Bool) (index : Nat) :
    digit (encode bits) index = bits index := by
  classical
  unfold digit
  rw [prefix_encode, threshold_iff]
  cases bits index <;> simp

/-- Encoding Boolean streams into extended reals is injective. -/
public theorem encode_injective : Function.Injective encode := by
  intro left right equal
  funext index
  rw [← digit_encode left index, equal, digit_encode]

end Foundations.Real.Coding
