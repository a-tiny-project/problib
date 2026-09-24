module

public import Problib.Real.Extended
import Std

set_option autoImplicit false

namespace Problib.Real.ENNReal

@[expose] public def partialSum (values : Nat → ENNReal) : Nat → ENNReal
  | 0 => zero
  | count + 1 => add (partialSum values count) (values count)

@[expose] public noncomputable def tsum (values : Nat → ENNReal) : ENNReal :=
  iSup (partialSum values)

public theorem partialSum_zero (count : Nat) :
    partialSum (fun _ => zero) count = zero := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [partialSum, induction, add_zero]

public theorem partialSum_congr {left right : Nat → ENNReal}
    (equal : ∀ index, left index = right index) (count : Nat) :
    partialSum left count = partialSum right count := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [partialSum, partialSum, induction, equal count]

public theorem partialSum_mono {left right : Nat → ENNReal}
    (included : ∀ index, le (left index) (right index)) (count : Nat) :
    le (partialSum left count) (partialSum right count) := by
  induction count with
  | zero => exact le_refl zero
  | succ count induction =>
      exact add_le_add induction (included count)

public theorem partialSum_step (values : Nat → ENNReal) (count : Nat) :
    le (partialSum values count) (partialSum values (count + 1)) := by
  rw [partialSum]
  have included := add_le_add (le_refl (partialSum values count))
    (zero_le (values count))
  simpa only [add_zero] using included

public theorem partialSum_monotone (values : Nat → ENNReal)
    {first second : Nat} (included : first ≤ second) :
    le (partialSum values first) (partialSum values second) := by
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
        exact le_trans (induction before) (partialSum_step values second)

public theorem term_le_partialSum (values : Nat → ENNReal) (index : Nat) :
    le (values index) (partialSum values (index + 1)) := by
  rw [partialSum]
  have included := add_le_add (zero_le (partialSum values index))
    (le_refl (values index))
  simpa only [zero_add] using included

public theorem partialSum_le_tsum (values : Nat → ENNReal) (count : Nat) :
    le (partialSum values count) (tsum values) := by
  unfold tsum
  exact le_iSup (partialSum values) count

public theorem term_le_tsum (values : Nat → ENNReal) (index : Nat) :
    le (values index) (tsum values) :=
  le_trans (term_le_partialSum values index)
    (partialSum_le_tsum values (index + 1))

public theorem tsum_le {values : Nat → ENNReal} {upper : ENNReal}
    (partialUpper : ∀ count, le (partialSum values count) upper) :
    le (tsum values) upper := by
  unfold tsum
  exact iSup_le partialUpper

public theorem tsum_le_iff {values : Nat → ENNReal} {upper : ENNReal} :
    le (tsum values) upper ↔
      ∀ count, le (partialSum values count) upper := by
  constructor
  · intro totalUpper count
    exact le_trans (partialSum_le_tsum values count) totalUpper
  · exact tsum_le

public theorem tsum_least_upper_bound (values : Nat → ENNReal) :
    IsLeastUpperBound le
      (fun value => ∃ count, value = partialSum values count)
      (tsum values) := by
  constructor
  · rintro value ⟨count, equal⟩
    rw [equal]
    exact partialSum_le_tsum values count
  · intro upper upperBound
    apply tsum_le
    intro count
    exact upperBound (partialSum values count) ⟨count, rfl⟩

public theorem tsum_congr {left right : Nat → ENNReal}
    (equal : ∀ index, left index = right index) :
    tsum left = tsum right := by
  apply le_antisymm
  · apply tsum_le
    intro count
    rw [partialSum_congr equal count]
    exact partialSum_le_tsum right count
  · apply tsum_le
    intro count
    rw [partialSum_congr (fun index => (equal index).symm) count]
    exact partialSum_le_tsum left count

public theorem tsum_zero : tsum (fun _ => zero) = zero := by
  apply le_antisymm
  · apply tsum_le
    intro count
    rw [partialSum_zero]
    exact le_refl zero
  · exact zero_le _

public theorem tsum_le_tsum {left right : Nat → ENNReal}
    (included : ∀ index, le (left index) (right index)) :
    le (tsum left) (tsum right) := by
  apply tsum_le
  intro count
  exact le_trans (partialSum_mono included count)
    (partialSum_le_tsum right count)

@[expose] public def single (index : Nat) (value : ENNReal) :
    Nat → ENNReal :=
  fun current => if current = index then value else zero

public theorem partialSum_single (index : Nat) (value : ENNReal)
    (count : Nat) :
    partialSum (single index value) count =
      if index < count then value else zero := by
  induction count with
  | zero => simp [partialSum]
  | succ count induction =>
      rw [partialSum, induction]
      by_cases before : index < count
      · have different : count ≠ index := by omega
        have after : index < count + 1 := by omega
        simp [single, before, different, after, add_zero]
      · by_cases current : count = index
        · subst count
          simp [single, before, zero_add]
        · have after : ¬index < count + 1 := by omega
          simp [single, before, current, after, add_zero]

public theorem tsum_single (index : Nat) (value : ENNReal) :
    tsum (single index value) = value := by
  apply le_antisymm
  · apply tsum_le
    intro count
    rw [partialSum_single]
    split
    · exact le_refl value
    · exact zero_le value
  · have included := partialSum_le_tsum (single index value) (index + 1)
    rw [partialSum_single] at included
    simpa using included

public theorem tsum_eq_of_at_most_one_nonzero
    (values : Nat → ENNReal) (index : Nat)
    (zeroAway : ∀ current, current ≠ index → values current = zero) :
    tsum values = values index := by
  calc
    tsum values = tsum (single index (values index)) := by
      apply tsum_congr
      intro current
      by_cases equal : current = index
      · subst current
        simp [single]
      · simp [single, equal, zeroAway current equal]
    _ = values index := tsum_single index (values index)

public theorem tsum_eq_zero_iff {values : Nat → ENNReal} :
    tsum values = zero ↔ ∀ index, values index = zero := by
  constructor
  · intro totalZero index
    apply eq_zero_of_le_zero
    rw [← totalZero]
    exact term_le_tsum values index
  · intro allZero
    calc
      tsum values = tsum (fun _ => zero) :=
        tsum_congr allZero
      _ = zero := tsum_zero

end Problib.Real.ENNReal
