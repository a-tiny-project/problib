module

public import Problib.Real.Series.Algebra

set_option autoImplicit false

namespace Problib.Real.ENNReal

private noncomputable def dyadicError (value : NNReal) :
    Nat → ENNReal :=
  fun index => finite (NNReal.half (NNReal.dyadic value index))

private theorem dyadicError_positive {value : NNReal}
    (positive : NNReal.lt NNReal.zero value) (index : Nat) :
    lt zero (dyadicError value index) :=
  NNReal.half_positive (NNReal.dyadic_positive positive index)

private theorem partialSum_dyadicError_add_remainder (value : NNReal)
    (count : Nat) :
    add (partialSum (dyadicError value) count)
        (finite (NNReal.dyadic value count)) =
      finite value := by
  induction count with
  | zero =>
      simp only [partialSum, NNReal.dyadic, zero_add]
  | succ count induction =>
      rw [partialSum]
      change
        add
            (add (partialSum (dyadicError value) count)
              (finite (NNReal.half (NNReal.dyadic value count))))
            (finite (NNReal.half (NNReal.dyadic value count))) =
          finite value
      rw [add_assoc]
      have halves :
          add
              (finite (NNReal.half (NNReal.dyadic value count)))
              (finite (NNReal.half (NNReal.dyadic value count))) =
            finite (NNReal.dyadic value count) :=
        congrArg finite
          (NNReal.half_add_half (NNReal.dyadic value count))
      rw [halves, induction]

private theorem tsum_dyadicError_le (value : NNReal) :
    le (tsum (dyadicError value)) (finite value) := by
  apply tsum_le
  intro count
  have included := add_le_add
    (le_refl (partialSum (dyadicError value) count))
    (zero_le (finite (NNReal.dyadic value count)))
  rw [add_zero, partialSum_dyadicError_add_remainder] at included
  exact included

public theorem exists_positive_summable_error (epsilon : ENNReal)
    (finiteEpsilon : Finite epsilon) (positive : lt zero epsilon) :
    ∃ error : Nat → ENNReal,
      (∀ index, lt zero (error index)) ∧ le (tsum error) epsilon := by
  cases epsilon with
  | top => exact False.elim finiteEpsilon
  | finite value =>
      exact ⟨dyadicError value, dyadicError_positive positive,
        tsum_dyadicError_le value⟩

end Problib.Real.ENNReal
