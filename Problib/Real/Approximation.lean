module

public import Problib.Real.Inverse

set_option autoImplicit false

namespace Problib.Real.Construction.Dedekind

public theorem exists_positive_inverse_below
    {epsilon : selection.Carrier} (epsilonPositive : lt zero epsilon) :
    ∃ index : Nat,
      lt zero (selection.ofRat (index : Rat)) ∧
        lt (inverse (selection.ofRat (index : Rat))) epsilon := by
  rcases exists_nat_strict_upper (inverse epsilon) with
    ⟨index, inverseLess⟩
  have inversePositive := inverse_of_positive_positive epsilonPositive
  have embeddedPositive : lt zero (selection.ofRat (index : Rat)) := by
    exact ⟨le_trans inversePositive.left inverseLess.left, by
      intro nonpositive
      exact inverseLess.right (le_trans nonpositive inversePositive.left)⟩
  refine ⟨index, embeddedPositive, ?_⟩
  have reversed := inverse_lt_inverse_of_positive
    inversePositive embeddedPositive inverseLess
  simpa only [inverse_inverse] using reversed

end Problib.Real.Construction.Dedekind
