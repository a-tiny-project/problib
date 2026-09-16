module

public import Foundations.Real.Series.Core

set_option autoImplicit false

namespace Foundations.Real.ENNReal

public theorem partialSumAdd (left right : Nat → ENNReal) (count : Nat) :
    partialSum (fun index => add (left index) (right index)) count =
      add (partialSum left count) (partialSum right count) := by
  induction count with
  | zero =>
      simp only [partialSum, addZero]
  | succ count induction =>
      simp only [partialSum]
      rw [induction]
      calc
        add
            (add (partialSum left count) (partialSum right count))
            (add (left count) (right count)) =
          add (partialSum left count)
            (add (partialSum right count)
              (add (left count) (right count))) :=
            addAssoc _ _ _
        _ = add (partialSum left count)
            (add (add (partialSum right count) (left count))
              (right count)) :=
            congrArg (add (partialSum left count))
              (addAssoc (partialSum right count)
                (left count) (right count)).symm
        _ = add (partialSum left count)
            (add (add (left count) (partialSum right count))
              (right count)) := by
            rw [addComm (partialSum right count) (left count)]
        _ = add (partialSum left count)
            (add (left count)
              (add (partialSum right count) (right count))) := by
            rw [addAssoc]
        _ = add
            (add (partialSum left count) (left count))
            (add (partialSum right count) (right count)) :=
          (addAssoc _ _ _).symm

public theorem partialSumMulLeft (factor : ENNReal)
    (values : Nat → ENNReal) (count : Nat) :
    partialSum (fun index => mul factor (values index)) count =
      mul factor (partialSum values count) := by
  induction count with
  | zero =>
      simp only [partialSum, mulZero]
  | succ count induction =>
      simp only [partialSum]
      rw [induction, mulAdd]

public theorem sequenceLeLater {values : Nat → ENNReal}
    (step : ∀ index, le (values index) (values (index + 1)))
    {first second : Nat} (included : first ≤ second) :
    le (values first) (values second) := by
  induction second with
  | zero =>
      have equal : first = 0 := by omega
      rw [equal]
      exact leRefl _
  | succ second induction =>
      by_cases equal : first = second + 1
      · rw [equal]
        exact leRefl _
      · have before : first ≤ second := by omega
        exact leTrans (induction before) (step second)

public theorem iSupDiagonalAdd (left right : Nat → ENNReal)
    (leftStep : ∀ index, le (left index) (left (index + 1)))
    (rightStep : ∀ index, le (right index) (right (index + 1))) :
    iSup (fun index => add (left index) (right index)) =
      add (iSup left) (iSup right) := by
  apply leAntisymm
  · apply iSupLe
    intro index
    exact addLeAdd (leISup left index) (leISup right index)
  · rw [addISup]
    apply iSupLe
    intro rightIndex
    rw [addComm (iSup left) (right rightIndex), addISup]
    apply iSupLe
    intro leftIndex
    rw [addComm (right rightIndex) (left leftIndex)]
    let common := Nat.max leftIndex rightIndex
    exact leTrans
      (addLeAdd
        (sequenceLeLater leftStep (Nat.le_max_left _ _))
        (sequenceLeLater rightStep (Nat.le_max_right _ _)))
      (leISup (fun index => add (left index) (right index)) common)

public theorem tsumAdd (left right : Nat → ENNReal) :
    tsum (fun index => add (left index) (right index)) =
      add (tsum left) (tsum right) := by
  unfold tsum
  calc
    iSup (partialSum fun index => add (left index) (right index)) =
        iSup (fun count =>
          add (partialSum left count) (partialSum right count)) := by
      apply congrArg iSup
      funext count
      exact partialSumAdd left right count
    _ = add (iSup (partialSum left)) (iSup (partialSum right)) :=
      iSupDiagonalAdd (partialSum left) (partialSum right)
        (partialSumStep left) (partialSumStep right)

public theorem tsumMulLeft (factor : ENNReal) (values : Nat → ENNReal) :
    tsum (fun index => mul factor (values index)) =
      mul factor (tsum values) := by
  unfold tsum
  calc
    iSup (partialSum fun index => mul factor (values index)) =
        iSup (fun count => mul factor (partialSum values count)) := by
      apply congrArg iSup
      funext count
      exact partialSumMulLeft factor values count
    _ = mul factor (iSup (partialSum values)) :=
      (mulISup factor (partialSum values)).symm

/-- Countable sum of a nonzero extended-nonnegative constant is infinite. -/
public theorem tsumConstOfNeZero {value : ENNReal}
    (nonzero : value ≠ zero) :
    tsum (fun _ => value) = top := by
  have absorbs : le (add (tsum (fun _ => value)) value)
      (tsum (fun _ => value)) := by
    rw [addComm, tsum, addISup]
    apply iSupLe
    intro index
    rw [addComm]
    exact partialSumLeTsum (fun _ => value) (index + 1)
  cases total : tsum (fun _ => value) with
  | top => rfl
  | finite finiteValue =>
      rw [total] at absorbs
      exact False.elim
        ((ltAddOfFiniteOfPositive (value := finite finiteValue)
          True.intro (zeroLtIffNeZero.mpr nonzero)).2 absorbs)

end Foundations.Real.ENNReal
