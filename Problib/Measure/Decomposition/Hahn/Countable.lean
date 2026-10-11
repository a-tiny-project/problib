module

public import Problib.Measure.Decomposition.Hahn.Score
public import Problib.Measure.Approximation.Countable
import Problib.Real.Extended.Approximation

set_option autoImplicit false

/-!
# Countable reduction of Hahn decomposition scores

Reduces the supremum Hahn score over all measurable sets to a countable supremum over
a countable generating algebra for finite measures, establishing approximation bounds.
-/

namespace Problib.Measure.Measure.Hahn

open Problib.Real

universe u

variable {α : Type u} {space : Space α}

/-- Hahn scores of two measurable sets differ by at most their symmetric difference distance
under the sum measure. -/
public theorem score_le_add_setDistance (left right : Measure space) {first second : Set α}
    (firstMeasurable : space.Measurable first) (secondMeasurable : space.Measurable second) :
    ENNReal.le (score left right first)
      (ENNReal.add (score left right second) ((Measure.add left right).setDistance first second)) := by
  have bound := ENNReal.add_le_add (left.le_add_setDistance first second)
    (right.le_add_setDistance (Set.complement first) (Set.complement second))
  rw [right.setDistance_complement, ENNReal.add_add_comm] at bound
  change ENNReal.le _ (ENNReal.add (score left right second)
    (Measure.add left right (Set.symmDiff first second)))
  rw [Measure.add_apply_measurable left right
    (Space.symmDiff_measurable firstMeasurable secondMeasurable)]
  exact bound

/-- The supremum Hahn score over all measurable sets coincides with the supremum over
any countable generating algebra for finite measures. -/
public theorem supremum_eq_iSup (algebra : Space.CountableAlgebra space)
    {left right : Measure space} (leftFinite : IsFinite left) (rightFinite : IsFinite right) :
    supremum left right = ENNReal.iSup (fun index => score left right (algebra.sets index)) := by
  apply ENNReal.le_antisymm
  · apply ENNReal.supremum_le
    rintro value ⟨region, measurable, rfl⟩
    apply ENNReal.le_of_forall_positive_le_add
    intro error positive
    cases error with
    | top =>
        rw [ENNReal.add_top]
        exact ENNReal.le_top _
    | finite epsilon =>
        rcases approximable_of_measurable (leftFinite.add rightFinite) algebra measurable
            epsilon positive with ⟨index, bound⟩
        exact ENNReal.le_trans (score_le_add_setDistance left right measurable
          (algebra.toCountableGenerator.measurable index))
          (ENNReal.add_le_add
            (ENNReal.le_iSup (fun index => score left right (algebra.sets index)) index) bound)
  · apply ENNReal.iSup_le
    intro index
    exact score_le_supremum left right (algebra.toCountableGenerator.measurable index)

/-- For any positive error bound, there exists a set in the countable generating algebra
whose Hahn score defect is within that error. -/
public theorem exists_index_defect_le (algebra : Space.CountableAlgebra space)
    {left right : Measure space} (leftFinite : IsFinite left) (rightFinite : IsFinite right)
    {error : ENNReal} (positive : ENNReal.lt ENNReal.zero error) :
    ∃ index, ENNReal.le (defect left right (algebra.sets index)) error := by
  have finite : ENNReal.Finite (ENNReal.iSup (fun index => score left right (algebra.sets index))) := by
    rw [← supremum_eq_iSup algebra leftFinite rightFinite]
    exact supremum_finite leftFinite rightFinite
  rcases ENNReal.exists_supremum_le_add
      (set := fun value => ∃ index, value = score left right (algebra.sets index))
      ⟨score left right (algebra.sets 0), 0, rfl⟩ finite positive with
    ⟨value, ⟨index, rfl⟩, bound⟩
  refine ⟨index, ENNReal.sub_le_iff_le_add.mpr ?_⟩
  rw [supremum_eq_iSup algebra leftFinite rightFinite, ENNReal.add_comm error]
  exact bound

end Problib.Measure.Measure.Hahn
