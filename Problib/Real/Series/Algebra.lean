module

public import Problib.Real.Series.Core

set_option autoImplicit false

namespace Problib.Real.ENNReal

public theorem partialSum_add (left right : Nat → ENNReal) (count : Nat) :
    partialSum (fun index => add (left index) (right index)) count =
      add (partialSum left count) (partialSum right count) := by
  induction count with
  | zero =>
      simp only [partialSum, add_zero]
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
            add_assoc _ _ _
        _ = add (partialSum left count)
            (add (add (partialSum right count) (left count))
              (right count)) :=
            congrArg (add (partialSum left count))
              (add_assoc (partialSum right count)
                (left count) (right count)).symm
        _ = add (partialSum left count)
            (add (add (left count) (partialSum right count))
              (right count)) := by
            rw [add_comm (partialSum right count) (left count)]
        _ = add (partialSum left count)
            (add (left count)
              (add (partialSum right count) (right count))) := by
            rw [add_assoc]
        _ = add
            (add (partialSum left count) (left count))
            (add (partialSum right count) (right count)) :=
          (add_assoc _ _ _).symm

public theorem partialSum_mul_left (factor : ENNReal)
    (values : Nat → ENNReal) (count : Nat) :
    partialSum (fun index => mul factor (values index)) count =
      mul factor (partialSum values count) := by
  induction count with
  | zero =>
      simp only [partialSum, mul_zero]
  | succ count induction =>
      simp only [partialSum]
      rw [induction, mul_add]

public theorem sequence_le_later {values : Nat → ENNReal}
    (step : ∀ index, le (values index) (values (index + 1)))
    {first second : Nat} (included : first ≤ second) :
    le (values first) (values second) := by
  induction second with
  | zero =>
      have equal : first = 0 := by omega
      rw [equal]
      exact le_refl _
  | succ second induction =>
      by_cases equal : first = second + 1
      · rw [equal]
        exact le_refl _
      · have before : first ≤ second := by omega
        exact le_trans (induction before) (step second)

public theorem iSup_diagonal_add (left right : Nat → ENNReal)
    (leftStep : ∀ index, le (left index) (left (index + 1)))
    (rightStep : ∀ index, le (right index) (right (index + 1))) :
    iSup (fun index => add (left index) (right index)) =
      add (iSup left) (iSup right) := by
  apply le_antisymm
  · apply iSup_le
    intro index
    exact add_le_add (le_iSup left index) (le_iSup right index)
  · rw [add_iSup]
    apply iSup_le
    intro rightIndex
    rw [add_comm (iSup left) (right rightIndex), add_iSup]
    apply iSup_le
    intro leftIndex
    rw [add_comm (right rightIndex) (left leftIndex)]
    let common := Nat.max leftIndex rightIndex
    exact le_trans
      (add_le_add
        (sequence_le_later leftStep (Nat.le_max_left _ _))
        (sequence_le_later rightStep (Nat.le_max_right _ _)))
      (le_iSup (fun index => add (left index) (right index)) common)

public theorem tsum_add (left right : Nat → ENNReal) :
    tsum (fun index => add (left index) (right index)) =
      add (tsum left) (tsum right) := by
  unfold tsum
  calc
    iSup (partialSum fun index => add (left index) (right index)) =
        iSup (fun count =>
          add (partialSum left count) (partialSum right count)) := by
      apply congrArg iSup
      funext count
      exact partialSum_add left right count
    _ = add (iSup (partialSum left)) (iSup (partialSum right)) :=
      iSup_diagonal_add (partialSum left) (partialSum right)
        (partialSum_step left) (partialSum_step right)

public theorem tsum_mul_left (factor : ENNReal) (values : Nat → ENNReal) :
    tsum (fun index => mul factor (values index)) =
      mul factor (tsum values) := by
  unfold tsum
  calc
    iSup (partialSum fun index => mul factor (values index)) =
        iSup (fun count => mul factor (partialSum values count)) := by
      apply congrArg iSup
      funext count
      exact partialSum_mul_left factor values count
    _ = mul factor (iSup (partialSum values)) :=
      (mul_iSup factor (partialSum values)).symm

/-- Countable sum of a nonzero extended-nonnegative constant is infinite. -/
public theorem tsum_const_of_ne_zero {value : ENNReal}
    (nonzero : value ≠ zero) :
    tsum (fun _ => value) = top := by
  have absorbs : le (add (tsum (fun _ => value)) value)
      (tsum (fun _ => value)) := by
    rw [add_comm, tsum, add_iSup]
    apply iSup_le
    intro index
    rw [add_comm]
    exact partialSum_le_tsum (fun _ => value) (index + 1)
  cases total : tsum (fun _ => value) with
  | top => rfl
  | finite finiteValue =>
      rw [total] at absorbs
      exact False.elim
        ((lt_add_of_finite_of_positive (value := finite finiteValue)
          True.intro (zero_lt_iff_ne_zero.mpr nonzero)).2 absorbs)

end Problib.Real.ENNReal
