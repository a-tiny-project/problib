module

public import Problib.Measure.Additive.Partition
public import Problib.Measure.Additive.Finite

set_option autoImplicit false

/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Loic Simon

Adapted from Mathlib/MeasureTheory/Measure/Decomposition/Hahn.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny defines the score as left(region) + right(complement region) in ENNReal and
proves modularity and defect subadditivity.
-/

namespace Problib.Measure.Measure.Hahn

open Problib.Real

universe u

variable {alpha : Type u} {space : Space alpha}

/-- The extended-nonnegative score of a region for two measures.
The score sums the left measure on the region and the right measure on its
complement. -/
@[expose] public noncomputable def score (left right : Measure space) (region : Set alpha) :
    ENNReal :=
  ENNReal.add (left region) (right (Set.complement region))

/-- The least upper bound of the scores across all measurable regions. -/
@[expose] public noncomputable def supremum (left right : Measure space) : ENNReal :=
  ENNReal.supremum (fun value =>
    ∃ region, space.Measurable region ∧ value = score left right region)

/-- The deficit between the score supremum and the score of a given region. -/
@[expose] public noncomputable def defect (left right : Measure space) (region : Set alpha) :
    ENNReal :=
  ENNReal.sub (supremum left right) (score left right region)

/-- The score of any measurable region is bounded above by the score supremum. -/
public theorem score_le_supremum (left right : Measure space)
    {region : Set alpha} (measurable : space.Measurable region) :
    ENNReal.le (score left right region) (supremum left right) :=
  ENNReal.le_supremum ⟨region, measurable, rfl⟩

/-- The score of any region is finite whenever both measures are finite. -/
public theorem score_finite {left right : Measure space}
    (leftFinite : IsFinite left) (rightFinite : IsFinite right) (region : Set alpha) :
    ENNReal.Finite (score left right region) :=
  ENNReal.add_finite (leftFinite.apply region)
    (rightFinite.apply (Set.complement region))

/-- Taking the complement of a region swaps the roles of the two measures in the
score. -/
public theorem score_complement (left right : Measure space) (region : Set alpha) :
    score left right (Set.complement region) = score right left region := by
  unfold score
  rw [Set.complement_complement, ENNReal.add_comm]

/-- The score supremum is finite whenever both measures are finite. -/
public theorem supremum_finite {left right : Measure space}
    (leftFinite : IsFinite left) (rightFinite : IsFinite right) :
    ENNReal.Finite (supremum left right) := by
  apply ENNReal.finite_of_le (right := ENNReal.add (left Set.univ) (right Set.univ))
  · apply ENNReal.supremum_le
    rintro value ⟨region, _, rfl⟩
    exact ENNReal.add_le_add (left.mono (Set.subset_univ region))
      (right.mono (Set.subset_univ (Set.complement region)))
  · exact ENNReal.add_finite leftFinite.univ_finite rightFinite.univ_finite

/-- The score function is modular over pairs of measurable sets. -/
public theorem score_modular (left right : Measure space)
    {first second : Set alpha} (firstMeasurable : space.Measurable first)
    (secondMeasurable : space.Measurable second) :
    ENNReal.add (score left right first) (score left right second) =
      ENNReal.add (score left right (Set.union first second))
        (score left right (Set.inter first second)) := by
  unfold score
  rw [ENNReal.add_add_comm (left first) (right (Set.complement first))
    (left second) (right (Set.complement second)),
    ← left.union_add_inter firstMeasurable secondMeasurable,
    ← right.union_add_inter (space.complement firstMeasurable)
      (space.complement secondMeasurable),
    ← Set.complement_inter, ← Set.complement_union,
    ENNReal.add_comm (right (Set.complement (Set.inter first second)))
      (right (Set.complement (Set.union first second))), ENNReal.add_add_comm]

/-- The defect of an intersection of measurable sets is subadditive whenever
both measures are finite. -/
public theorem defect_inter_le {left right : Measure space}
    (leftFinite : IsFinite left) (rightFinite : IsFinite right)
    {first second : Set alpha} (firstMeasurable : space.Measurable first)
    (secondMeasurable : space.Measurable second) :
    ENNReal.le (defect left right (Set.inter first second))
      (ENNReal.add (defect left right first) (defect left right second)) := by
  apply ENNReal.sub_le_iff_le_add.mpr
  have comparison := ENNReal.add_le_add_right
    (score_le_supremum left right (space.union firstMeasurable secondMeasurable))
    (score left right (Set.inter first second))
  rw [← score_modular left right firstMeasurable secondMeasurable] at comparison
  have shifted := ENNReal.add_le_add_left comparison
    (ENNReal.add (defect left right first) (defect left right second))
  rw [ENNReal.add_add_comm (defect left right first) (defect left right second)
    (score left right first) (score left right second)] at shifted
  have firstCancel : ENNReal.add (defect left right first) (score left right first) =
      supremum left right := ENNReal.sub_add_cancel (score_le_supremum left right firstMeasurable)
  have secondCancel : ENNReal.add (defect left right second) (score left right second) =
      supremum left right := ENNReal.sub_add_cancel (score_le_supremum left right secondMeasurable)
  rw [firstCancel, secondCancel,
    ENNReal.add_comm (supremum left right) (score left right (Set.inter first second)),
    ← ENNReal.add_assoc] at shifted
  exact ENNReal.le_of_add_le_add_right_of_finite (supremum_finite leftFinite rightFinite) shifted

/-- For two finite measures and strictly positive error, some measurable region
has score defect bounded by that error. -/
public theorem exists_defect_le {left right : Measure space}
    (leftFinite : IsFinite left) (rightFinite : IsFinite right)
    {error : ENNReal} (positive : ENNReal.lt ENNReal.zero error) :
    ∃ region, space.Measurable region ∧ ENNReal.le (defect left right region) error := by
  rcases ENNReal.exists_supremum_le_add
    (set := fun value => ∃ region, space.Measurable region ∧ value = score left right region)
    ⟨score left right Set.empty, Set.empty, space.empty, rfl⟩
    (supremum_finite leftFinite rightFinite) positive with
    ⟨value, ⟨region, measurable, rfl⟩, included⟩
  refine ⟨region, measurable, ENNReal.sub_le_iff_le_add.mpr ?_⟩
  rw [ENNReal.add_comm error]
  exact included

end Problib.Measure.Measure.Hahn
