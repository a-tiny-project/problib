module

public import Foundations.Measure.Additive.Core

set_option autoImplicit false

namespace Foundations.Measure.Measure

open Foundations.Real

universe u

variable {alpha : Type u} {space : Space alpha}

/-- Measure inequality on all measurable sets extends to all arbitrary sets
through the canonical countable-cover outer envelope from
`OuterMeasure.le_ofFunction`. -/
public theorem le_of_measurable_le {left right : Measure space}
    (included : ∀ set, space.Measurable set → ENNReal.le (left set) (right set))
    (set : Set alpha) : ENNReal.le (left set) (right set) := by
  classical
  apply OuterMeasure.le_ofFunction left.toOuterMeasure right.extendedContent
    right.extendedContent_empty
  intro region
  by_cases measurable : space.Measurable region
  · rw [right.extendedContent_apply_measurable measurable,
      ← right.apply_measurable measurable]
    exact included region measurable
  · unfold extendedContent
    rw [dif_neg measurable]
    exact ENNReal.leTop _

end Foundations.Measure.Measure
