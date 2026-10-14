module

public import Problib.Analysis.Real.Monotone

/-! A bounded derivative bounds increments.

If the derivative of a function stays within `bound` in magnitude on an open
interval, the function moves by at most `bound` times the distance between two
of its points. Both one-sided halves are `Monotone`'s theorem applied to the
function plus and minus `bound` times the identity, whose derivatives are
nonnegative. This is the one-variable mean value inequality that the
several-variable one reads along segments.
-/

set_option autoImplicit false

namespace Problib.Analysis.Real

open Problib.Real.Construction.Dedekind

noncomputable section

private theorem increment_ordered
    {function derivative : selection.Carrier → selection.Carrier}
    {lower upper bound : selection.Carrier}
    (differentiable : ∀ point, lt lower point → lt point upper →
      HasDerivative function point (derivative point))
    (bounded : ∀ point, lt lower point → lt point upper →
      le (abs (derivative point)) bound)
    {first second : selection.Carrier} (lowerFirst : lt lower first)
    (secondUpper : lt second upper) (ordered : le first second) :
    le (abs (sub (function second) (function first)))
      (mul bound (abs (sub second first))) := by
  have rising := le_of_hasDerivative_nonnegative
    (function := fun point => sub (mul bound point) (function point))
    (derivative := fun point => sub (mul bound one) (derivative point))
    (fun point lowerPoint pointUpper =>
      hasDerivative_sub (hasDerivative_smul bound (hasDerivative_identity point))
        (differentiable point lowerPoint pointUpper))
    (fun point lowerPoint pointUpper => by
      have := (abs_le.mp (bounded point lowerPoint pointUpper)).right
      real_grind)
    lowerFirst secondUpper ordered
  have falling := le_of_hasDerivative_nonnegative
    (function := fun point => add (mul bound point) (function point))
    (derivative := fun point => add (mul bound one) (derivative point))
    (fun point lowerPoint pointUpper =>
      hasDerivative_add (hasDerivative_smul bound (hasDerivative_identity point))
        (differentiable point lowerPoint pointUpper))
    (fun point lowerPoint pointUpper => by
      have := (abs_le.mp (bounded point lowerPoint pointUpper)).left
      real_grind)
    lowerFirst secondUpper ordered
  rw [abs_of_nonnegative (sub_nonnegative ordered)]
  apply abs_le.mpr
  constructor <;> real_grind

/-- A derivative bounded by `bound` on an open interval bounds the increment
between two of its points by `bound` times their distance. -/
public theorem abs_sub_le_of_hasDerivative_bound
    {function derivative : selection.Carrier → selection.Carrier}
    {lower upper bound : selection.Carrier}
    (differentiable : ∀ point, lt lower point → lt point upper →
      HasDerivative function point (derivative point))
    (bounded : ∀ point, lt lower point → lt point upper →
      le (abs (derivative point)) bound)
    {first second : selection.Carrier} (lowerFirst : lt lower first)
    (firstUpper : lt first upper) (lowerSecond : lt lower second)
    (secondUpper : lt second upper) :
    le (abs (sub (function second) (function first)))
      (mul bound (abs (sub second first))) := by
  rcases le_total first second with ordered | reverse
  · exact increment_ordered differentiable bounded lowerFirst secondUpper ordered
  · rw [abs_sub_comm (function second), abs_sub_comm second]
    exact increment_ordered differentiable bounded lowerSecond firstUpper reverse

end

end Problib.Analysis.Real
