module

public import Foundations.Measure.Decomposition.Hahn.Score
public import Foundations.Measure.Approximation.Countable
import Foundations.Real.Extended.Approximation

set_option autoImplicit false

/-!
# Countable reduction of Hahn decomposition scores

Reduces the supremum Hahn score over all measurable sets to a countable supremum over
a countable generating algebra for finite measures, establishing approximation bounds.
-/

namespace Foundations.Measure.Measure.Hahn

open Foundations.Real

universe u

variable {α : Type u} {space : Space α}

/-- Hahn scores of two measurable sets differ by at most their symmetric difference distance
under the sum measure. -/
public theorem score_le_add_setDistance (left right : Measure space) {first second : Set α}
    (firstMeasurable : space.Measurable first) (secondMeasurable : space.Measurable second) :
    ENNReal.le (score left right first)
      (ENNReal.add (score left right second) ((Measure.add left right).setDistance first second)) := by
  have bound := ENNReal.addLeAdd (left.le_add_setDistance first second)
    (right.le_add_setDistance (Set.complement first) (Set.complement second))
  rw [right.setDistance_complement, ENNReal.addAddComm] at bound
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
  apply ENNReal.leAntisymm
  · apply ENNReal.supremumLe
    rintro value ⟨region, measurable, rfl⟩
    apply ENNReal.leOfForallPositiveLeAdd
    intro error positive
    cases error with
    | top =>
        rw [ENNReal.addTop]
        exact ENNReal.leTop _
    | finite epsilon =>
        rcases approximable_of_measurable (leftFinite.add rightFinite) algebra measurable
            epsilon positive with ⟨index, bound⟩
        exact ENNReal.leTrans (score_le_add_setDistance left right measurable
          (algebra.toCountableGenerator.measurable index))
          (ENNReal.addLeAdd
            (ENNReal.leISup (fun index => score left right (algebra.sets index)) index) bound)
  · apply ENNReal.iSupLe
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
  rcases ENNReal.existsSupremumLeAdd
      (set := fun value => ∃ index, value = score left right (algebra.sets index))
      ⟨score left right (algebra.sets 0), 0, rfl⟩ finite positive with
    ⟨value, ⟨index, rfl⟩, bound⟩
  refine ⟨index, ENNReal.subLeIffLeAdd.mpr ?_⟩
  rw [supremum_eq_iSup algebra leftFinite rightFinite, ENNReal.addComm error]
  exact bound

end Foundations.Measure.Measure.Hahn
