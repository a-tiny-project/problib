module

public import Problib.Measure.Space

set_option autoImplicit false

namespace Problib.Measure

universe u

public section

/-- Generic Boolean indicator for a subset of an arbitrary type, using classical decidability. -/
@[expose] noncomputable def boolIndicator {alpha : Type u} (region : Set alpha) (input : alpha) : Bool :=
  @decide (region input) (Classical.propDecidable _)

/-- The Boolean indicator of any measurable set is a measurable map into discrete `Bool`. -/
theorem boolIndicator_measurable {alpha : Type u} {space : Space alpha}
    {region : Set alpha} (measurable : space.Measurable region) :
    MeasurableMap space (Space.discrete Bool) (boolIndicator region) := by
  classical
  intro event _
  have preimage : Set.preimage (boolIndicator region) event =
      Set.union (if event true then region else Set.empty)
        (if event false then Set.complement region else Set.empty) := by
    apply Set.ext
    intro input
    by_cases member : region input <;>
      by_cases includeTrue : event true <;>
      by_cases includeFalse : event false <;>
      simp [Set.preimage, Set.union, Set.complement, Set.empty,
        boolIndicator, member, includeTrue, includeFalse]
  rw [preimage]
  apply space.union
  · split
    · exact measurable
    · exact space.empty
  · split
    · exact space.complement measurable
    · exact space.empty

end

end Problib.Measure
