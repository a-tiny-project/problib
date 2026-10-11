module

public import Problib.Real.Series.Algebra

set_option autoImplicit false

/-!
Countable series subtraction for extended-nonnegative sequences.

Termwise subtraction reconstructs the left series sum when right is dominated
termwise by left. Distributing subtraction across series summation requires
finite total right sum.
-/

namespace Problib.Real.ENNReal

/-- Reconstruct the sum of the left series from its termwise difference series
and right series. The premise requires right dominated termwise by left, with
no finiteness hypotheses. -/
public theorem tsum_sub_add {left right : Nat → ENNReal}
    (included : ∀ index, le (right index) (left index)) :
    add (tsum (fun index => sub (left index) (right index))) (tsum right) =
      tsum left := by
  rw [← tsum_add]
  exact tsum_congr (fun index => sub_add_cancel (included index))

/-- Distribute series summation over termwise subtraction. The premises
require right dominated termwise by left and finite total right sum. -/
public theorem tsum_sub {left right : Nat → ENNReal}
    (included : ∀ index, le (right index) (left index))
    (rightFinite : Finite (tsum right)) :
    tsum (fun index => sub (left index) (right index)) = sub (tsum left) (tsum right) := by
  have equal := congrArg (fun value => sub value (tsum right)) (tsum_sub_add included)
  rw [add_sub_cancel_right rightFinite] at equal
  exact equal

end Problib.Real.ENNReal
