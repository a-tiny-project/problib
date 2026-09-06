module

public import Foundations.Real.Series.Algebra

set_option autoImplicit false

namespace Foundations.Real.ENNReal

/-- Appending a block of terms to a partial sum decomposes into the initial
partial sum and the shifted partial sum. -/
public theorem partialSumAppend (values : Nat → ENNReal) (start count : Nat) :
    partialSum values (start + count) =
      add (partialSum values start)
        (partialSum (fun index => values (start + index)) count) := by
  induction count with
  | zero => rw [Nat.add_zero, partialSum, addZero]
  | succ count induction =>
      rw [Nat.add_succ, partialSum, induction, partialSum, addAssoc]

/-- The sum of a partial sum and its corresponding tail series equals the total
series sum. -/
public theorem partialSumAddTail (values : Nat → ENNReal) (start : Nat) :
    add (partialSum values start) (tsum (fun index => values (start + index))) =
      tsum values := by
  apply leAntisymm
  · unfold tsum
    rw [addISup]
    apply iSupLe
    intro count
    rw [← partialSumAppend]
    exact partialSumLeTsum values (start + count)
  · apply tsumLe
    intro count
    have longer := partialSumMonotone values (show count ≤ start + count by omega)
    rw [partialSumAppend values start count] at longer
    exact leTrans longer
      (addLeAddLeft (partialSumLeTsum (fun index => values (start + index)) count) _)

/-- Every tail series is bounded above by the total series sum. -/
public theorem tailLeTsum (values : Nat → ENNReal) (start : Nat) :
    le (tsum (fun index => values (start + index))) (tsum values) := by
  have included := addLeAddRight (zeroLe (partialSum values start))
    (tsum (fun index => values (start + index)))
  rw [zeroAdd, partialSumAddTail] at included
  exact included

/-- The tail series of an extended-nonnegative sequence is antitone with respect
to the starting index. -/
public theorem tailAntitone (values : Nat → ENNReal) {first second : Nat}
    (included : first ≤ second) :
    le (tsum (fun index => values (second + index)))
      (tsum (fun index => values (first + index))) := by
  have bound := tailLeTsum (fun index => values (first + index)) (second - first)
  simpa only [← Nat.add_assoc, Nat.add_sub_of_le included] using bound

/-- The infimum of the tail series of an extended-nonnegative series with finite
total sum is zero. -/
public theorem iInfTailEqZero {values : Nat → ENNReal}
    (finite : Finite (tsum values)) :
    iInf (fun start => tsum (fun index => values (start + index))) = zero := by
  let lower := iInf (fun start => tsum (fun index => values (start + index)))
  have included : ∀ start, le (add lower (partialSum values start)) (tsum values) := by
    intro start
    have bound := addLeAddRight
      (iInfLe (fun start => tsum (fun index => values (start + index))) start)
      (partialSum values start)
    rw [addComm (tsum (fun index => values (start + index))),
      partialSumAddTail] at bound
    exact bound
  have limit := iSupLe included
  rw [← addISup] at limit
  change le (add lower (tsum values)) (tsum values) at limit
  apply eqZeroOfLeZero
  apply leOfAddLeAddRightOfFinite finite
  rw [zeroAdd]
  exact limit

end Foundations.Real.ENNReal
