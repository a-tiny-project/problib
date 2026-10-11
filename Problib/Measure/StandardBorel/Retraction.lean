module

public import Problib.Measure.Real.Order
public import Problib.Measure.StandardBorel.Real

set_option autoImplicit false

namespace Problib.Measure.StandardBorel

open Problib.Measure.Real (Carrier borel measurable_eq)

universe u

/-- Present a measurable space as standard Borel through a measurable real retraction. -/
@[expose] public noncomputable def ofRealLeftInverse {α : Type u} {source : Space α}
    (forward : α → Carrier) (inverse : Carrier → α)
    (inverseForward : ∀ value, inverse (forward value) = value)
    (forwardMeasurable : MeasurableMap source borel forward)
    (inverseMeasurable : MeasurableMap borel source inverse) :
    StandardBorel source := by
  have rangeEqual : Set.range forward = (fun value => forward (inverse value) = value) := by
    apply Set.ext
    intro value
    constructor
    · rintro ⟨input, equal⟩
      rw [← equal, inverseForward]
    · intro fixed
      exact ⟨inverse value, fixed⟩
  have rangeMeasurable : borel.Measurable (Set.range forward) := by
    rw [rangeEqual]
    exact measurable_eq (MeasurableMap.comp forwardMeasurable inverseMeasurable)
      (MeasurableMap.identity borel)
  exact ofEmbedding
    (MeasurableEmbedding.ofLeftInverse forward inverse inverseForward
      forwardMeasurable inverseMeasurable rangeMeasurable) real

end Problib.Measure.StandardBorel
