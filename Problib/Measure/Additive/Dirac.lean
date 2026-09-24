module

public import Problib.Measure.Additive.Map

set_option autoImplicit false

/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Adapted from Mathlib/MeasureTheory/Measure/Dirac/Def.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.
-/

namespace Problib.Measure

open Problib.Real

universe u v

namespace Measure

variable {α : Type u} {β : Type v}
  {source : Space α} {target : Space β}

attribute [local instance] Classical.propDecidable

/-- Unit mass at one point. Its canonical outer envelope is used away from
measurable sets. -/
@[expose] public noncomputable def dirac
    (space : Space α) (point : α) : Measure space := by
  classical
  exact {
    content := fun set _ =>
      if set point then ENNReal.one else ENNReal.zero
    empty := by simp [Set.empty]
    content_iUnion_disjoint := by
      intro sets _ pairwise
      by_cases member : Set.iUnion sets point
      · rcases member with ⟨index, indexMember⟩
        have zeroAway : ∀ current, current ≠ index →
            (if sets current point then ENNReal.one else ENNReal.zero) =
              ENNReal.zero := by
          intro current different
          apply if_neg
          intro currentMember
          exact pairwise current index different currentMember indexMember
        rw [if_pos ⟨index, indexMember⟩,
          ENNReal.tsum_eq_of_at_most_one_nonzero
            (fun current =>
              if sets current point then ENNReal.one else ENNReal.zero)
            index zeroAway,
          if_pos indexMember]
      · have allZero : ∀ index,
            (if sets index point then ENNReal.one else ENNReal.zero) =
              ENNReal.zero := by
          intro index
          apply if_neg
          exact fun indexMember => member ⟨index, indexMember⟩
        rw [if_neg member, ENNReal.tsum_eq_zero_iff.mpr allZero]
  }

@[simp] public theorem dirac_apply (space : Space α) (point : α)
    {set : Set α} (setMeasurable : space.Measurable set) :
    (dirac space point) set =
      if set point then ENNReal.one else ENNReal.zero := by
  classical
  rw [(dirac space point).apply_measurable setMeasurable]
  unfold dirac
  rfl

public theorem dirac_apply_of_mem (space : Space α) (point : α)
    {set : Set α} (setMeasurable : space.Measurable set)
    (member : set point) : (dirac space point) set = ENNReal.one := by
  rw [dirac_apply space point setMeasurable, if_pos member]

public theorem dirac_apply_of_not_mem (space : Space α) (point : α)
    {set : Set α} (setMeasurable : space.Measurable set)
    (notMember : ¬set point) :
    (dirac space point) set = ENNReal.zero := by
  rw [dirac_apply space point setMeasurable, if_neg notMember]

@[simp] public theorem dirac_apply_univ (space : Space α) (point : α) :
    (dirac space point) Set.univ = ENNReal.one := by
  rw [dirac_apply space point space.univ]
  simp [Set.univ]

public theorem map_dirac (function : α → β)
    (measurable : MeasurableMap source target function) (point : α) :
    (dirac source point).map function measurable =
    dirac target (function point) := by
  apply Measure.ext
  intro set setMeasurable
  rw [(dirac source point).map_apply function measurable setMeasurable,
    dirac_apply source point (measurable setMeasurable),
    dirac_apply target (function point) setMeasurable]
  unfold Set.preimage
  rfl

end Measure

end Problib.Measure
