module

public import Foundations.Measure.Space

set_option autoImplicit false

namespace Foundations.Measure.Embedding.Necessity

/-- A measurable map admitting a measurable left inverse can have a nonmeasurable range. -/
public theorem measurable_leftInverse_does_not_force_measurable_range :
    MeasurableMap (Space.discrete Unit) (Space.indiscrete Bool) (fun _ => false) ∧
    MeasurableMap (Space.indiscrete Bool) (Space.discrete Unit) (fun _ => ()) ∧
    (∀ value : Unit, (fun _ : Bool => ()) ((fun _ : Unit => false) value) = value) ∧
    ¬(Space.indiscrete Bool).Measurable (Set.range (fun _ : Unit => false)) := by
  refine ⟨MeasurableMap.constant _ _ false, MeasurableMap.constant _ _ (), ?_, ?_⟩
  · intro value
    cases value
    rfl
  · intro measurable
    rcases (Space.indiscrete_measurable_iff _).mp measurable with empty | whole
    · have member : Set.range (fun _ : Unit => false) false := ⟨(), rfl⟩
      rw [empty] at member
      exact member
    · have member : Set.range (fun _ : Unit => false) true := by
        rw [whole]
        exact True.intro
      rcases member with ⟨value, equal⟩
      cases equal

end Foundations.Measure.Embedding.Necessity
