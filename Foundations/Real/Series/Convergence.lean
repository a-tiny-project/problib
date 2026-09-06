module

public import Foundations.Real.Series.Algebra

set_option autoImplicit false

namespace Foundations.Real.ENNReal

public theorem partialSumTsum (values : Nat → Nat → ENNReal)
    (count : Nat) :
    partialSum (fun first => tsum (values first)) count =
      tsum (fun second =>
        partialSum (fun first => values first second) count) := by
  induction count with
  | zero =>
      simpa only [partialSum] using tsumZero.symm
  | succ count induction =>
      rw [partialSum, induction, ← tsumAdd]
      apply tsumCongr
      intro second
      rfl

public theorem tsumComm (values : Nat → Nat → ENNReal) :
    tsum (fun first => tsum (values first)) =
      tsum (fun second => tsum (fun first => values first second)) := by
  apply leAntisymm
  · apply tsumLe
    intro count
    rw [partialSumTsum values count]
    apply tsumLeTsum
    intro second
    exact partialSumLeTsum (fun first => values first second) count
  · apply tsumLe
    intro count
    rw [partialSumTsum (fun second first => values first second) count]
    apply tsumLeTsum
    intro first
    exact partialSumLeTsum (values first) count

public theorem partialSumISup (values : Nat → Nat → ENNReal)
    (monotone : ∀ stage index,
      le (values stage index) (values (stage + 1) index))
    (count : Nat) :
    partialSum (fun index => iSup (fun stage => values stage index)) count =
      iSup (fun stage => partialSum (values stage) count) := by
  induction count with
  | zero =>
      simpa only [partialSum] using (iSupConst zero).symm
  | succ count induction =>
      simp only [partialSum]
      rw [induction]
      exact (iSupDiagonalAdd
        (fun stage => partialSum (values stage) count)
        (fun stage => values stage count)
        (fun stage => partialSumMono (monotone stage) count)
        (fun stage => monotone stage count)).symm

public theorem tsumISup (values : Nat → Nat → ENNReal)
    (monotone : ∀ stage index,
      le (values stage index) (values (stage + 1) index)) :
    tsum (fun index => iSup (fun stage => values stage index)) =
      iSup (fun stage => tsum (values stage)) := by
  apply leAntisymm
  · apply tsumLe
    intro count
    rw [partialSumISup values monotone count]
    apply iSupLe
    intro stage
    exact leTrans (partialSumLeTsum (values stage) count)
      (leISup (fun current => tsum (values current)) stage)
  · apply iSupLe
    intro stage
    apply tsumLeTsum
    intro index
    exact leISup (fun current => values current index) stage

end Foundations.Real.ENNReal
