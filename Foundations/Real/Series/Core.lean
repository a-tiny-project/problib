module

public import Foundations.Real.Extended
import Std

set_option autoImplicit false

namespace Foundations.Real.ENNReal

@[expose] public def partialSum (values : Nat → ENNReal) : Nat → ENNReal
  | 0 => zero
  | count + 1 => add (partialSum values count) (values count)

@[expose] public noncomputable def tsum (values : Nat → ENNReal) : ENNReal :=
  iSup (partialSum values)

public theorem partialSumZero (count : Nat) :
    partialSum (fun _ => zero) count = zero := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [partialSum, induction, addZero]

public theorem partialSumCongr {left right : Nat → ENNReal}
    (equal : ∀ index, left index = right index) (count : Nat) :
    partialSum left count = partialSum right count := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [partialSum, partialSum, induction, equal count]

public theorem partialSumMono {left right : Nat → ENNReal}
    (included : ∀ index, le (left index) (right index)) (count : Nat) :
    le (partialSum left count) (partialSum right count) := by
  induction count with
  | zero => exact leRefl zero
  | succ count induction =>
      exact addLeAdd induction (included count)

public theorem partialSumStep (values : Nat → ENNReal) (count : Nat) :
    le (partialSum values count) (partialSum values (count + 1)) := by
  rw [partialSum]
  have included := addLeAdd (leRefl (partialSum values count))
    (zeroLe (values count))
  simpa only [addZero] using included

public theorem partialSumMonotone (values : Nat → ENNReal)
    {first second : Nat} (included : first ≤ second) :
    le (partialSum values first) (partialSum values second) := by
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
        exact leTrans (induction before) (partialSumStep values second)

public theorem termLePartialSum (values : Nat → ENNReal) (index : Nat) :
    le (values index) (partialSum values (index + 1)) := by
  rw [partialSum]
  have included := addLeAdd (zeroLe (partialSum values index))
    (leRefl (values index))
  simpa only [zeroAdd] using included

public theorem partialSumLeTsum (values : Nat → ENNReal) (count : Nat) :
    le (partialSum values count) (tsum values) := by
  unfold tsum
  exact leISup (partialSum values) count

public theorem termLeTsum (values : Nat → ENNReal) (index : Nat) :
    le (values index) (tsum values) :=
  leTrans (termLePartialSum values index)
    (partialSumLeTsum values (index + 1))

public theorem tsumLe {values : Nat → ENNReal} {upper : ENNReal}
    (partialUpper : ∀ count, le (partialSum values count) upper) :
    le (tsum values) upper := by
  unfold tsum
  exact iSupLe partialUpper

public theorem tsumLeIff {values : Nat → ENNReal} {upper : ENNReal} :
    le (tsum values) upper ↔
      ∀ count, le (partialSum values count) upper := by
  constructor
  · intro totalUpper count
    exact leTrans (partialSumLeTsum values count) totalUpper
  · exact tsumLe

public theorem tsumLeastUpperBound (values : Nat → ENNReal) :
    IsLeastUpperBound le
      (fun value => ∃ count, value = partialSum values count)
      (tsum values) := by
  constructor
  · rintro value ⟨count, equal⟩
    rw [equal]
    exact partialSumLeTsum values count
  · intro upper upperBound
    apply tsumLe
    intro count
    exact upperBound (partialSum values count) ⟨count, rfl⟩

public theorem tsumCongr {left right : Nat → ENNReal}
    (equal : ∀ index, left index = right index) :
    tsum left = tsum right := by
  apply leAntisymm
  · apply tsumLe
    intro count
    rw [partialSumCongr equal count]
    exact partialSumLeTsum right count
  · apply tsumLe
    intro count
    rw [partialSumCongr (fun index => (equal index).symm) count]
    exact partialSumLeTsum left count

public theorem tsumZero : tsum (fun _ => zero) = zero := by
  apply leAntisymm
  · apply tsumLe
    intro count
    rw [partialSumZero]
    exact leRefl zero
  · exact zeroLe _

public theorem tsumLeTsum {left right : Nat → ENNReal}
    (included : ∀ index, le (left index) (right index)) :
    le (tsum left) (tsum right) := by
  apply tsumLe
  intro count
  exact leTrans (partialSumMono included count)
    (partialSumLeTsum right count)

@[expose] public def single (index : Nat) (value : ENNReal) :
    Nat → ENNReal :=
  fun current => if current = index then value else zero

public theorem partialSumSingle (index : Nat) (value : ENNReal)
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
        simp [single, before, different, after, addZero]
      · by_cases current : count = index
        · subst count
          simp [single, before, zeroAdd]
        · have after : ¬index < count + 1 := by omega
          simp [single, before, current, after, addZero]

public theorem tsumSingle (index : Nat) (value : ENNReal) :
    tsum (single index value) = value := by
  apply leAntisymm
  · apply tsumLe
    intro count
    rw [partialSumSingle]
    split
    · exact leRefl value
    · exact zeroLe value
  · have included := partialSumLeTsum (single index value) (index + 1)
    rw [partialSumSingle] at included
    simpa using included

public theorem tsumEqOfAtMostOneNonzero
    (values : Nat → ENNReal) (index : Nat)
    (zeroAway : ∀ current, current ≠ index → values current = zero) :
    tsum values = values index := by
  calc
    tsum values = tsum (single index (values index)) := by
      apply tsumCongr
      intro current
      by_cases equal : current = index
      · subst current
        simp [single]
      · simp [single, equal, zeroAway current equal]
    _ = values index := tsumSingle index (values index)

public theorem tsumEqZeroIff {values : Nat → ENNReal} :
    tsum values = zero ↔ ∀ index, values index = zero := by
  constructor
  · intro totalZero index
    apply eqZeroOfLeZero
    rw [← totalZero]
    exact termLeTsum values index
  · intro allZero
    calc
      tsum values = tsum (fun _ => zero) :=
        tsumCongr allZero
      _ = zero := tsumZero

end Foundations.Real.ENNReal
