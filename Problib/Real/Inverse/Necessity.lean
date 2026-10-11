module

public import Problib.Real.Inverse

set_option autoImplicit false

namespace Problib.Real.Inverse.Necessity

open Problib.Real.Construction.Dedekind

/-- Refutation of iterated division cancellation when the numerator is zero. -/
public theorem zero_numerator_does_not_cancel :
    div zero (div zero one) ≠ one := by
  rw [zero_div]
  exact fun equal => one_ne_zero equal.symm

/-- Counterexample showing that nonnegativity of the lower denominator is not
enough to reverse reciprocal order. -/
public theorem nonnegative_is_insufficient_for_inverse_order :
    le zero one ∧ ¬le (inverse one) (inverse zero) := by
  refine ⟨one_nonnegative, ?_⟩
  rw [inverse_one, inverse_zero]
  intro reversed
  exact one_ne_zero (le_antisymm reversed one_nonnegative)

end Problib.Real.Inverse.Necessity
