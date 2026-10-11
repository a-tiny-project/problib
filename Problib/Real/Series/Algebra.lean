module

public import Problib.Algebra.Sum
public import Problib.Real.Arithmetic
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

/-- The sequence `left, right, zero, zero, ...`, whose sum is `left + right`. -/
@[expose] public def pair (left right : ENNReal) : Nat → ENNReal
  | 0 => left
  | 1 => right
  | _ + 2 => zero

public theorem tsum_pair (left right : ENNReal) :
    tsum (pair left right) = add left right := by
  have equal : pair left right = fun index =>
      add (single 0 left index) (single 1 right index) := by
    funext index
    match index with
    | 0 => simp [pair, single, add_zero]
    | 1 => simp [pair, single, zero_add]
    | _ + 2 => simp [pair, single, zero_add]
  rw [equal, tsum_add, tsum_single, tsum_single]

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

universe u

/-- A finite sum is monotone in its terms. -/
public theorem listSum_map_mono {Index : Type u}
    (indices : List Index) (left right : Index → ENNReal)
    (included : ∀ index, le (left index) (right index)) :
    le (additiveLaws.listSum (indices.map left)) (additiveLaws.listSum (indices.map right)) := by
  induction indices with
  | nil => exact le_refl zero
  | cons index indices induction =>
      simp only [List.map, Problib.Algebra.AdditiveCommutativeMonoidLaws.listSum]
      exact add_le_add (included index) induction

/-- A finite sum of series is the series of finite sums. -/
public theorem listSum_map_tsum {Index : Type u}
    (indices : List Index) (values : Nat → Index → ENNReal) :
    additiveLaws.listSum (indices.map (fun index =>
      tsum (fun measureIndex => values measureIndex index))) =
      tsum (fun measureIndex => additiveLaws.listSum (indices.map (values measureIndex))) := by
  induction indices with
  | nil =>
      simp only [List.map, Problib.Algebra.AdditiveCommutativeMonoidLaws.listSum]
      exact tsum_zero.symm
  | cons index indices induction =>
      simp only [List.map, Problib.Algebra.AdditiveCommutativeMonoidLaws.listSum]
      rw [induction]
      exact (tsum_add
        (fun measureIndex => values measureIndex index)
        (fun measureIndex => additiveLaws.listSum (List.map (values measureIndex) indices))).symm

/-- A finite sum of increasing suprema is the supremum of the finite sums. -/
public theorem listSum_map_iSup {Index : Type u}
    (indices : List Index) (values : Nat → Index → ENNReal)
    (monotone : ∀ stage index, le (values stage index) (values (stage + 1) index)) :
    additiveLaws.listSum (indices.map fun index => iSup (fun stage => values stage index)) =
      iSup (fun stage => additiveLaws.listSum (indices.map (values stage))) := by
  induction indices with
  | nil =>
      simpa only [List.map, Problib.Algebra.AdditiveCommutativeMonoidLaws.listSum] using
        (iSup_const zero).symm
  | cons index indices induction =>
      simp only [List.map, Problib.Algebra.AdditiveCommutativeMonoidLaws.listSum]
      rw [induction]
      exact (iSup_diagonal_add
        (fun stage => values stage index)
        (fun stage => additiveLaws.listSum (indices.map (values stage)))
        (fun stage => monotone stage index)
        (fun stage => listSum_map_mono indices
          (values stage) (values (stage + 1))
          (monotone stage))).symm

/-- A finite sum of copies of one value is the count times the value. -/
public theorem listSum_map_const {Index : Type u} (indices : List Index) (value : ENNReal) :
    additiveLaws.listSum (indices.map fun _ => value) =
      mul (ofRat (indices.length : Rat) Rat.natCast_nonneg) value := by
  induction indices with
  | nil =>
      show zero = mul (ofRat 0 (by decide)) value
      rw [ofRat_zero, zero_mul]
  | cons index indices induction =>
      have count : ofRat ((indices.length + 1 : Nat) : Rat) Rat.natCast_nonneg =
          add (ofRat (indices.length : Rat) Rat.natCast_nonneg) one := by
        rw [← ofRat_one, ← ofRat_add]
        congr 1
        exact Rat.natCast_add _ _
      show add value (additiveLaws.listSum (indices.map fun _ => value)) =
        mul (ofRat ((indices.length + 1 : Nat) : Rat) Rat.natCast_nonneg) value
      rw [induction, count, mul_comm (add _ one) value,
        mul_add, mul_one, mul_comm value, add_comm value]

end Problib.Real.ENNReal

namespace Problib.Real.Construction.Dedekind

universe u

/-- A finite sum of copies of one real value is the count times the value. -/
public theorem listSum_map_const {Index : Type u} (indices : List Index)
    (value : selection.Carrier) :
    additiveLaws.listSum (indices.map fun _ => value) =
      mul (selection.ofRat (indices.length : Rat)) value := by
  induction indices with
  | nil =>
      show zero = mul (selection.ofRat 0) value
      rw [ofRat_zero, zero_mul]
  | cons index indices induction =>
      show add value (additiveLaws.listSum (indices.map fun _ => value)) =
        mul (selection.ofRat ((indices.length + 1 : Nat) : Rat)) value
      rw [induction, Rat.natCast_add, Rat.natCast_ofNat, ofRat_add, ofRat_one, add_mul, one_mul,
        add_comm]

/-- A finite sum of reals is monotone in its terms. -/
public theorem listSum_map_mono {Index : Type u}
    (indices : List Index) (left right : Index → selection.Carrier)
    (included : ∀ index, le (left index) (right index)) :
    le (additiveLaws.listSum (indices.map left)) (additiveLaws.listSum (indices.map right)) := by
  induction indices with
  | nil => exact le_refl zero
  | cons index indices induction => exact add_le_add (included index) induction

/-- The square of a scaled sum's distance from a scaled sum of centres expands
into one term per pair of entries. -/
public theorem listSum_centred_square {Index : Type u} (indices : List Index)
    (scale center : selection.Carrier) (values centres : Index → selection.Carrier)
    (unit : mul scale (additiveLaws.listSum (indices.map centres)) = center) :
    mul (sub (mul scale (additiveLaws.listSum (indices.map values))) center)
        (sub (mul scale (additiveLaws.listSum (indices.map values))) center) =
      mul scale (mul scale (additiveLaws.listSum (indices.map fun first =>
        additiveLaws.listSum (indices.map fun second =>
          mul (sub (values first) (centres first)) (sub (values second) (centres second)))))) := by
  have centred : sub (mul scale (additiveLaws.listSum (indices.map values))) center =
      mul scale (additiveLaws.listSum (indices.map fun index =>
        sub (values index) (centres index))) := by
    rw [← unit, ← mul_sub]
    congr 1
    simp only [sub_eq_add_neg]
    rw [additiveLaws.listSum_map_hom additiveLaws neg neg_zero neg_add]
    exact (additiveLaws.listSum_map_add indices values fun index => neg (centres index)).symm
  have square : mul
      (additiveLaws.listSum (indices.map fun index => sub (values index) (centres index)))
      (additiveLaws.listSum (indices.map fun index => sub (values index) (centres index))) =
      additiveLaws.listSum (indices.map fun first => additiveLaws.listSum (indices.map fun second =>
        mul (sub (values first) (centres first)) (sub (values second) (centres second)))) := by
    have left : ∀ (factor : selection.Carrier) (terms : Index → selection.Carrier),
        mul factor (additiveLaws.listSum (indices.map terms)) =
          additiveLaws.listSum (indices.map fun index => mul factor (terms index)) :=
      fun factor terms => additiveLaws.listSum_map_hom additiveLaws (mul factor) (mul_zero factor)
        (mul_add factor) indices terms
    rw [left]
    refine congrArg (fun terms => additiveLaws.listSum (indices.map terms))
      (funext fun first => ?_)
    rw [mul_comm, left]
  rw [centred, ← square, mul_assoc scale, mul_comm _ (mul scale _), mul_assoc scale]

end Problib.Real.Construction.Dedekind
