module

public import Problib.Real.Series.Algebra

set_option autoImplicit false

namespace Problib.Real.ENNReal

/-- Appending a block of terms to a partial sum decomposes into the initial
partial sum and the shifted partial sum. -/
public theorem partialSum_append (values : Nat → ENNReal) (start count : Nat) :
    partialSum values (start + count) =
      add (partialSum values start)
        (partialSum (fun index => values (start + index)) count) := by
  induction count with
  | zero => rw [Nat.add_zero, partialSum, add_zero]
  | succ count induction =>
      rw [Nat.add_succ, partialSum, induction, partialSum, add_assoc]

/-- The sum of a partial sum and its corresponding tail series equals the total
series sum. -/
public theorem partialSum_add_tail (values : Nat → ENNReal) (start : Nat) :
    add (partialSum values start) (tsum (fun index => values (start + index))) =
      tsum values := by
  apply le_antisymm
  · unfold tsum
    rw [add_iSup]
    apply iSup_le
    intro count
    rw [← partialSum_append]
    exact partialSum_le_tsum values (start + count)
  · apply tsum_le
    intro count
    have longer := partialSum_monotone values (show count ≤ start + count by omega)
    rw [partialSum_append values start count] at longer
    exact le_trans longer
      (add_le_add_left (partialSum_le_tsum (fun index => values (start + index)) count) _)

/-- Every tail series is bounded above by the total series sum. -/
public theorem tail_le_tsum (values : Nat → ENNReal) (start : Nat) :
    le (tsum (fun index => values (start + index))) (tsum values) := by
  have included := add_le_add_right (zero_le (partialSum values start))
    (tsum (fun index => values (start + index)))
  rw [zero_add, partialSum_add_tail] at included
  exact included

/-- The tail series of an extended-nonnegative sequence is antitone with respect
to the starting index. -/
public theorem tail_antitone (values : Nat → ENNReal) {first second : Nat}
    (included : first ≤ second) :
    le (tsum (fun index => values (second + index)))
      (tsum (fun index => values (first + index))) := by
  have bound := tail_le_tsum (fun index => values (first + index)) (second - first)
  simpa only [← Nat.add_assoc, Nat.add_sub_of_le included] using bound

/-- The infimum of the tail series of an extended-nonnegative series with finite
total sum is zero. -/
public theorem iInf_tail_eq_zero {values : Nat → ENNReal}
    (finite : Finite (tsum values)) :
    iInf (fun start => tsum (fun index => values (start + index))) = zero := by
  let lower := iInf (fun start => tsum (fun index => values (start + index)))
  have included : ∀ start, le (add lower (partialSum values start)) (tsum values) := by
    intro start
    have bound := add_le_add_right
      (iInf_le (fun start => tsum (fun index => values (start + index))) start)
      (partialSum values start)
    rw [add_comm (tsum (fun index => values (start + index))),
      partialSum_add_tail] at bound
    exact bound
  have limit := iSup_le included
  rw [← add_iSup] at limit
  change le (add lower (tsum values)) (tsum values) at limit
  apply eq_zero_of_le_zero
  apply le_of_add_le_add_right_of_finite finite
  rw [zero_add]
  exact limit

end Problib.Real.ENNReal
