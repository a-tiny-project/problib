module

public import Foundations.Measure.Real.Generator
public import Foundations.Measure.Dynkin.Uniqueness
public import Foundations.Measure.Real.Continuity

set_option autoImplicit false

namespace Foundations.Measure.Real

open Foundations.Real
open Foundations.Real.Construction

public section

/-- Finite measures on `unitBorel` agreeing on all initial closed intervals are equal,
proved via Dynkin's π-λ theorem independently of uniform measure or quantile construction. -/
theorem finiteMeasure_ext_unitInitial {left right : Measure unitBorel}
    (leftFinite : Measure.IsFinite left) (rightFinite : Measure.IsFinite right)
    (agree : ∀ point, left (unitInitial point) = right (unitInitial point)) :
    left = right := by
  apply Measure.ext_of_generate unitInitials unitBorel_generatedInitials
    unitInitials_pi unitInitials_univ leftFinite rightFinite
  rintro set ⟨point, rfl⟩
  exact agree point

/-- Two finite measures on `unitBorel` with equal total mass are equal when
they agree on a countable right-dense family of initial intervals.
Thresholds need not follow the fixed rational basis.
The proof uses finite-measure right-continuity and π-λ uniqueness. -/
theorem finiteMeasure_ext_rightDense
    {left right : Measure unitBorel}
    (leftFinite : Measure.IsFinite left) (rightFinite : Measure.IsFinite right)
    (thresholds : Nat → UnitInterval)
    (dense : ∀ point next : UnitInterval, Dedekind.lt point.val next.val →
      ∃ index, Dedekind.lt point.val (thresholds index).val ∧
        Dedekind.le (thresholds index).val next.val)
    (total : left Set.univ = right Set.univ)
    (agree : ∀ index, left (unitInitial (thresholds index)) = right (unitInitial (thresholds index))) :
    left = right := by
  apply finiteMeasure_ext_unitInitial leftFinite rightFinite
  intro point
  apply ENNReal.leAntisymm
  · apply le_measure_unitInitial_of_rightDense rightFinite thresholds dense point
    · rw [← total]
      exact left.mono (Set.subset_univ _)
    · intro index above
      rw [← agree index]
      exact left.mono (fun _ member => Dedekind.leTrans member above.1)
  · apply le_measure_unitInitial_of_rightDense leftFinite thresholds dense point
    · rw [total]
      exact right.mono (Set.subset_univ _)
    · intro index above
      rw [agree index]
      exact right.mono (fun _ member => Dedekind.leTrans member above.1)


end

end Foundations.Measure.Real
