module

public import Foundations.Real.Series.Algebra

set_option autoImplicit false

namespace Foundations.Real.ENNReal

private noncomputable def dyadicError (value : NNReal) :
    Nat → ENNReal :=
  fun index => finite (NNReal.half (NNReal.dyadic value index))

private theorem dyadicErrorPositive {value : NNReal}
    (positive : NNReal.lt NNReal.zero value) (index : Nat) :
    lt zero (dyadicError value index) :=
  NNReal.halfPositive (NNReal.dyadicPositive positive index)

private theorem partialSumDyadicErrorAddRemainder (value : NNReal)
    (count : Nat) :
    add (partialSum (dyadicError value) count)
        (finite (NNReal.dyadic value count)) =
      finite value := by
  induction count with
  | zero =>
      simp only [partialSum, NNReal.dyadic, zeroAdd]
  | succ count induction =>
      rw [partialSum]
      change
        add
            (add (partialSum (dyadicError value) count)
              (finite (NNReal.half (NNReal.dyadic value count))))
            (finite (NNReal.half (NNReal.dyadic value count))) =
          finite value
      rw [addAssoc]
      have halves :
          add
              (finite (NNReal.half (NNReal.dyadic value count)))
              (finite (NNReal.half (NNReal.dyadic value count))) =
            finite (NNReal.dyadic value count) :=
        congrArg finite
          (NNReal.halfAddHalf (NNReal.dyadic value count))
      rw [halves, induction]

private theorem tsumDyadicErrorLe (value : NNReal) :
    le (tsum (dyadicError value)) (finite value) := by
  apply tsumLe
  intro count
  have included := addLeAdd
    (leRefl (partialSum (dyadicError value) count))
    (zeroLe (finite (NNReal.dyadic value count)))
  rw [addZero, partialSumDyadicErrorAddRemainder] at included
  exact included

public theorem existsPositiveSummableError (epsilon : ENNReal)
    (finiteEpsilon : Finite epsilon) (positive : lt zero epsilon) :
    ∃ error : Nat → ENNReal,
      (∀ index, lt zero (error index)) ∧ le (tsum error) epsilon := by
  cases epsilon with
  | top => exact False.elim finiteEpsilon
  | finite value =>
      exact ⟨dyadicError value, dyadicErrorPositive positive,
        tsumDyadicErrorLe value⟩

end Foundations.Real.ENNReal
