module

public import Foundations.Real.Inverse

set_option autoImplicit false

namespace Foundations.Real.Construction.Dedekind

public theorem existsPositiveInverseBelow
    {epsilon : selection.Carrier} (epsilonPositive : lt zero epsilon) :
    ∃ index : Nat,
      lt zero (selection.ofRat (index : Rat)) ∧
        lt (inverse (selection.ofRat (index : Rat))) epsilon := by
  rcases existsNatStrictUpper (inverse epsilon) with
    ⟨index, inverseLess⟩
  have inversePositive := inverseOfPositivePositive epsilonPositive
  have embeddedPositive : lt zero (selection.ofRat (index : Rat)) := by
    exact ⟨leTrans inversePositive.left inverseLess.left, by
      intro nonpositive
      exact inverseLess.right (leTrans nonpositive inversePositive.left)⟩
  refine ⟨index, embeddedPositive, ?_⟩
  have reversed := inverseLtInverseOfPositive
    inversePositive embeddedPositive inverseLess
  simpa only [inverseInverse] using reversed

end Foundations.Real.Construction.Dedekind
