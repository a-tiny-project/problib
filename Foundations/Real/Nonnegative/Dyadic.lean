module

public import Foundations.Real.Nonnegative.Finite

set_option autoImplicit false

namespace Foundations.Real.NNReal

/-- Halving any nonnegative real produces a smaller or equal value. -/
public theorem halfLe (value : NNReal) : le (half value) value := by
  have bound := addLeAddLeft (zeroLe (half value)) (half value)
  rw [addZero, halfAddHalf] at bound
  exact bound

/-- Halving a strictly positive nonnegative real produces a strictly smaller value. -/
public theorem halfLt {value : NNReal} (positive : lt zero value) :
    lt (half value) value := by
  have bound := (addLtAddLeftIff (shift := half value)).mpr (halfPositive positive)
  rw [addZero, halfAddHalf] at bound
  exact bound

/-- Iterated halving sequence starting at the given nonnegative real value. -/
@[expose] public noncomputable def dyadic (value : NNReal) : Nat → NNReal
  | 0 => value
  | index + 1 => half (dyadic value index)

/-- Every dyadic step of a strictly positive value remains strictly positive. -/
public theorem dyadicPositive {value : NNReal} (positive : lt zero value) (index : Nat) :
    lt zero (dyadic value index) := by
  induction index with
  | zero => exact positive
  | succ index induction => exact halfPositive induction

/-- Each successive step of the dyadic sequence is less than or equal to the previous step. -/
public theorem dyadicStep (value : NNReal) (index : Nat) :
    le (dyadic value (index + 1)) (dyadic value index) :=
  halfLe (dyadic value index)

/-- The dyadic halving sequence is antitone with respect to the index order. -/
public theorem dyadicAntitone (value : NNReal) {first second : Nat}
    (included : first ≤ second) : le (dyadic value second) (dyadic value first) := by
  induction second with
  | zero =>
      have equal : first = 0 := by omega
      rw [equal]
      exact leRefl _
  | succ second induction =>
      by_cases equal : first = second + 1
      · rw [equal]
        exact leRefl _
      · exact leTrans (dyadicStep value second) (induction (by omega))

end Foundations.Real.NNReal
