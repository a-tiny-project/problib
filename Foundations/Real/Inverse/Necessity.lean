module

public import Foundations.Real.Inverse

set_option autoImplicit false

namespace Foundations.Real.Inverse.Necessity

open Foundations.Real.Construction.Dedekind

/-- Refutation of iterated division cancellation when the numerator is zero. -/
public theorem zero_numerator_does_not_cancel :
    div zero (div zero one) ≠ one := by
  rw [zeroDiv]
  exact fun equal => oneNeZero equal.symm

/-- Counterexample showing that nonnegativity of the lower denominator is not
enough to reverse reciprocal order. -/
public theorem nonnegative_is_insufficient_for_inverse_order :
    le zero one ∧ ¬le (inverse one) (inverse zero) := by
  refine ⟨oneNonnegative, ?_⟩
  rw [inverseOne, inverseZero]
  intro reversed
  exact oneNeZero (leAntisymm reversed oneNonnegative)

end Foundations.Real.Inverse.Necessity
