module

public import Foundations.Measure.Additive.Partition
public import Foundations.Measure.Additive.Finite

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

namespace Foundations.Measure.Measure.Hahn

open Foundations.Real

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
  ENNReal.leSupremum ⟨region, measurable, rfl⟩

/-- The score of any region is finite whenever both measures are finite. -/
public theorem score_finite {left right : Measure space}
    (leftFinite : IsFinite left) (rightFinite : IsFinite right) (region : Set alpha) :
    ENNReal.Finite (score left right region) :=
  ENNReal.addFinite (leftFinite.apply region)
    (rightFinite.apply (Set.complement region))

/-- Taking the complement of a region swaps the roles of the two measures in the
score. -/
public theorem score_complement (left right : Measure space) (region : Set alpha) :
    score left right (Set.complement region) = score right left region := by
  unfold score
  rw [Set.complement_complement, ENNReal.addComm]

/-- The score supremum is finite whenever both measures are finite. -/
public theorem supremum_finite {left right : Measure space}
    (leftFinite : IsFinite left) (rightFinite : IsFinite right) :
    ENNReal.Finite (supremum left right) := by
  apply ENNReal.finiteOfLe (right := ENNReal.add (left Set.univ) (right Set.univ))
  · apply ENNReal.supremumLe
    rintro value ⟨region, _, rfl⟩
    exact ENNReal.addLeAdd (left.mono (Set.subset_univ region))
      (right.mono (Set.subset_univ (Set.complement region)))
  · exact ENNReal.addFinite leftFinite.univFinite rightFinite.univFinite

/-- The score function is modular over pairs of measurable sets. -/
public theorem score_modular (left right : Measure space)
    {first second : Set alpha} (firstMeasurable : space.Measurable first)
    (secondMeasurable : space.Measurable second) :
    ENNReal.add (score left right first) (score left right second) =
      ENNReal.add (score left right (Set.union first second))
        (score left right (Set.inter first second)) := by
  unfold score
  rw [ENNReal.addAddComm (left first) (right (Set.complement first))
    (left second) (right (Set.complement second)),
    ← left.union_add_inter firstMeasurable secondMeasurable,
    ← right.union_add_inter (space.complement firstMeasurable)
      (space.complement secondMeasurable),
    ← Set.complement_inter, ← Set.complement_union,
    ENNReal.addComm (right (Set.complement (Set.inter first second)))
      (right (Set.complement (Set.union first second))), ENNReal.addAddComm]

/-- The defect of an intersection of measurable sets is subadditive whenever
both measures are finite. -/
public theorem defect_inter_le {left right : Measure space}
    (leftFinite : IsFinite left) (rightFinite : IsFinite right)
    {first second : Set alpha} (firstMeasurable : space.Measurable first)
    (secondMeasurable : space.Measurable second) :
    ENNReal.le (defect left right (Set.inter first second))
      (ENNReal.add (defect left right first) (defect left right second)) := by
  apply ENNReal.subLeIffLeAdd.mpr
  have comparison := ENNReal.addLeAddRight
    (score_le_supremum left right (space.union firstMeasurable secondMeasurable))
    (score left right (Set.inter first second))
  rw [← score_modular left right firstMeasurable secondMeasurable] at comparison
  have shifted := ENNReal.addLeAddLeft comparison
    (ENNReal.add (defect left right first) (defect left right second))
  rw [ENNReal.addAddComm (defect left right first) (defect left right second)
    (score left right first) (score left right second)] at shifted
  have firstCancel : ENNReal.add (defect left right first) (score left right first) =
      supremum left right := ENNReal.subAddCancel (score_le_supremum left right firstMeasurable)
  have secondCancel : ENNReal.add (defect left right second) (score left right second) =
      supremum left right := ENNReal.subAddCancel (score_le_supremum left right secondMeasurable)
  rw [firstCancel, secondCancel,
    ENNReal.addComm (supremum left right) (score left right (Set.inter first second)),
    ← ENNReal.addAssoc] at shifted
  exact ENNReal.leOfAddLeAddRightOfFinite (supremum_finite leftFinite rightFinite) shifted

/-- For two finite measures and strictly positive error, some measurable region
has score defect bounded by that error. -/
public theorem exists_defect_le {left right : Measure space}
    (leftFinite : IsFinite left) (rightFinite : IsFinite right)
    {error : ENNReal} (positive : ENNReal.lt ENNReal.zero error) :
    ∃ region, space.Measurable region ∧ ENNReal.le (defect left right region) error := by
  rcases ENNReal.existsSupremumLeAdd
    (set := fun value => ∃ region, space.Measurable region ∧ value = score left right region)
    ⟨score left right Set.empty, Set.empty, space.empty, rfl⟩
    (supremum_finite leftFinite rightFinite) positive with
    ⟨value, ⟨region, measurable, rfl⟩, included⟩
  refine ⟨region, measurable, ENNReal.subLeIffLeAdd.mpr ?_⟩
  rw [ENNReal.addComm error]
  exact included

end Foundations.Measure.Measure.Hahn
