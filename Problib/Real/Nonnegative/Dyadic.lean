module

public import Problib.Real.Nonnegative.Finite

set_option autoImplicit false

namespace Problib.Real.NNReal

/-- Halving any nonnegative real produces a smaller or equal value. -/
public theorem half_le (value : NNReal) : le (half value) value := by
  have bound := add_le_add_left (zero_le (half value)) (half value)
  rw [add_zero, half_add_half] at bound
  exact bound

/-- Halving a strictly positive nonnegative real produces a strictly smaller value. -/
public theorem half_lt {value : NNReal} (positive : lt zero value) :
    lt (half value) value := by
  have bound := (add_lt_add_left_iff (shift := half value)).mpr (half_positive positive)
  rw [add_zero, half_add_half] at bound
  exact bound

/-- Iterated halving sequence starting at the given nonnegative real value. -/
@[expose] public noncomputable def dyadic (value : NNReal) : Nat → NNReal
  | 0 => value
  | index + 1 => half (dyadic value index)

/-- Every dyadic step of a strictly positive value remains strictly positive. -/
public theorem dyadic_positive {value : NNReal} (positive : lt zero value) (index : Nat) :
    lt zero (dyadic value index) := by
  induction index with
  | zero => exact positive
  | succ index induction => exact half_positive induction

/-- Each successive step of the dyadic sequence is less than or equal to the previous step. -/
public theorem dyadic_step (value : NNReal) (index : Nat) :
    le (dyadic value (index + 1)) (dyadic value index) :=
  half_le (dyadic value index)

/-- The dyadic halving sequence is antitone with respect to the index order. -/
public theorem dyadic_antitone (value : NNReal) {first second : Nat}
    (included : first ≤ second) : le (dyadic value second) (dyadic value first) := by
  induction second with
  | zero =>
      have equal : first = 0 := by omega
      rw [equal]
      exact le_refl _
  | succ second induction =>
      by_cases equal : first = second + 1
      · rw [equal]
        exact le_refl _
      · exact le_trans (dyadic_step value second) (induction (by omega))

end Problib.Real.NNReal
