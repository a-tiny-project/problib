module

public import Foundations.Real.Series.Algebra

set_option autoImplicit false

/-!
Countable series subtraction for extended-nonnegative sequences.

Termwise subtraction reconstructs the left series sum when right is dominated
termwise by left. Distributing subtraction across series summation requires
finite total right sum.
-/

namespace Foundations.Real.ENNReal

/-- Reconstruct the sum of the left series from its termwise difference series
and right series. The premise requires right dominated termwise by left, with
no finiteness hypotheses. -/
public theorem tsumSubAdd {left right : Nat → ENNReal}
    (included : ∀ index, le (right index) (left index)) :
    add (tsum (fun index => sub (left index) (right index))) (tsum right) =
      tsum left := by
  rw [← tsumAdd]
  exact tsumCongr (fun index => subAddCancel (included index))

/-- Distribute series summation over termwise subtraction. The premises
require right dominated termwise by left and finite total right sum. -/
public theorem tsumSub {left right : Nat → ENNReal}
    (included : ∀ index, le (right index) (left index))
    (rightFinite : Finite (tsum right)) :
    tsum (fun index => sub (left index) (right index)) = sub (tsum left) (tsum right) := by
  have equal := congrArg (fun value => sub value (tsum right)) (tsumSubAdd included)
  rw [addSubCancelRight rightFinite] at equal
  exact equal

end Foundations.Real.ENNReal
