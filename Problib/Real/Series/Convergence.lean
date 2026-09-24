module

public import Problib.Real.Series.Algebra

set_option autoImplicit false

namespace Problib.Real.ENNReal

public theorem partialSum_tsum (values : Nat → Nat → ENNReal)
    (count : Nat) :
    partialSum (fun first => tsum (values first)) count =
      tsum (fun second =>
        partialSum (fun first => values first second) count) := by
  induction count with
  | zero =>
      simpa only [partialSum] using tsum_zero.symm
  | succ count induction =>
      rw [partialSum, induction, ← tsum_add]
      apply tsum_congr
      intro second
      rfl

public theorem tsum_comm (values : Nat → Nat → ENNReal) :
    tsum (fun first => tsum (values first)) =
      tsum (fun second => tsum (fun first => values first second)) := by
  apply le_antisymm
  · apply tsum_le
    intro count
    rw [partialSum_tsum values count]
    apply tsum_le_tsum
    intro second
    exact partialSum_le_tsum (fun first => values first second) count
  · apply tsum_le
    intro count
    rw [partialSum_tsum (fun second first => values first second) count]
    apply tsum_le_tsum
    intro first
    exact partialSum_le_tsum (values first) count

public theorem partialSum_iSup (values : Nat → Nat → ENNReal)
    (monotone : ∀ stage index,
      le (values stage index) (values (stage + 1) index))
    (count : Nat) :
    partialSum (fun index => iSup (fun stage => values stage index)) count =
      iSup (fun stage => partialSum (values stage) count) := by
  induction count with
  | zero =>
      simpa only [partialSum] using (iSup_const zero).symm
  | succ count induction =>
      simp only [partialSum]
      rw [induction]
      exact (iSup_diagonal_add
        (fun stage => partialSum (values stage) count)
        (fun stage => values stage count)
        (fun stage => partialSum_mono (monotone stage) count)
        (fun stage => monotone stage count)).symm

public theorem tsum_iSup (values : Nat → Nat → ENNReal)
    (monotone : ∀ stage index,
      le (values stage index) (values (stage + 1) index)) :
    tsum (fun index => iSup (fun stage => values stage index)) =
      iSup (fun stage => tsum (values stage)) := by
  apply le_antisymm
  · apply tsum_le
    intro count
    rw [partialSum_iSup values monotone count]
    apply iSup_le
    intro stage
    exact le_trans (partialSum_le_tsum (values stage) count)
      (le_iSup (fun current => tsum (values current)) stage)
  · apply iSup_le
    intro stage
    apply tsum_le_tsum
    intro index
    exact le_iSup (fun current => values current index) stage

end Problib.Real.ENNReal
