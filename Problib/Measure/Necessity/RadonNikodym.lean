module

public import Problib.Measure.Decomposition.RadonNikodym

set_option autoImplicit false

namespace Problib.Measure.Necessity.RadonNikodym

open Problib.Real

/-- Two finite Dirac measures on the discrete space of booleans witness that
Radon-Nikodym derivatives fail to exist without absolute continuity. -/
public theorem finite_without_absolute_continuity_no_derivative :
    ∃ target reference : Measure (Space.discrete Bool),
      Measure.IsFinite target ∧ Measure.IsFinite reference ∧
        ¬Nonempty (Measure.RadonNikodymDerivative target reference) := by
  refine ⟨Measure.dirac (Space.discrete Bool) false,
    Measure.dirac (Space.discrete Bool) true,
    Measure.IsFinite.dirac _ _, Measure.IsFinite.dirac _ _, ?_⟩
  rintro ⟨derivative⟩
  have zero := derivative.absolutelyContinuous (set := fun value => value = false)
    True.intro (Measure.dirac_apply_of_not_mem (Space.discrete Bool) true
      (set := fun value => value = false) True.intro (by decide))
  rw [Measure.dirac_apply_of_mem (Space.discrete Bool) false
    (set := fun value => value = false) True.intro rfl] at zero
  exact ENNReal.one_ne_zero zero

end Problib.Measure.Necessity.RadonNikodym
