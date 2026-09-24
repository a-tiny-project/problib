module

public import Problib.Measure.Additive.Algebra
public import Problib.Measure.Additive.Order
public import Problib.Measure.Additive.Restrict

set_option autoImplicit false

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Adapted from Mathlib/MeasureTheory/Measure/Map.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.
-/

namespace Problib.Measure

open Problib.Real

universe u v w

namespace Measure

variable {α : Type u} {β : Type v} {γ : Type w}
  {source : Space α} {middle : Space β} {target : Space γ}

/-- Push a measure forward along an explicitly measurable map. -/
@[expose] public def map (measure : Measure source) (function : α → β)
    (measurable : MeasurableMap source middle function) : Measure middle where
  content := fun set setMeasurable =>
    measure.content (Set.preimage function set) (measurable setMeasurable)
  empty := by
    simpa only [Set.preimage_empty] using measure.empty
  content_iUnion_disjoint := by
    intro sets setsMeasurable pairwise
    have preimagesMeasurable : ∀ index,
        source.Measurable (Set.preimage function (sets index)) :=
      fun index => measurable (setsMeasurable index)
    have preimagesPairwise : Set.PairwiseDisjoint
        (fun index => Set.preimage function (sets index)) := by
      intro first second different value firstMember secondMember
      exact pairwise first second different firstMember secondMember
    simpa only [Set.preimage_iUnion] using
      measure.content_iUnion_disjoint
        (fun index => Set.preimage function (sets index))
        preimagesMeasurable preimagesPairwise

@[simp] public theorem map_apply (measure : Measure source)
    (function : α → β)
    (functionMeasurable : MeasurableMap source middle function)
    {set : Set β} (setMeasurable : middle.Measurable set) :
    (measure.map function functionMeasurable) set =
      measure (Set.preimage function set) := by
  rw [(measure.map function functionMeasurable).apply_measurable setMeasurable,
    measure.apply_measurable (functionMeasurable setMeasurable)]
  rfl

@[simp] public theorem map_id (measure : Measure source) :
    measure.map (fun value => value) (MeasurableMap.identity source) =
      measure := by
  apply Measure.ext
  intro set setMeasurable
  rw [measure.map_apply (fun value => value)
    (MeasurableMap.identity source) setMeasurable]
  rfl

/-- Preserve measure domination under pushforward along a measurable map. -/
public theorem map_le_map {left right : Measure source}
    (included : ∀ set, source.Measurable set → ENNReal.le (left set) (right set))
    (function : α → β) (measurable : MeasurableMap source middle function)
    (set : Set β) :
    ENNReal.le ((left.map function measurable) set) ((right.map function measurable) set) := by
  apply le_of_measurable_le _ set
  intro region regionMeasurable
  rw [left.map_apply function measurable regionMeasurable,
    right.map_apply function measurable regionMeasurable]
  exact included _ (measurable regionMeasurable)

public theorem map_comp (measure : Measure source)
    (before : α → β) (after : β → γ)
    (beforeMeasurable : MeasurableMap source middle before)
    (afterMeasurable : MeasurableMap middle target after) :
    (measure.map before beforeMeasurable).map after afterMeasurable =
      measure.map (fun value => after (before value))
        (MeasurableMap.comp afterMeasurable beforeMeasurable) := by
  apply Measure.ext
  intro set setMeasurable
  rw [(measure.map before beforeMeasurable).map_apply after
      afterMeasurable setMeasurable,
    measure.map_apply before beforeMeasurable
      (afterMeasurable setMeasurable),
    measure.map_apply (fun value => after (before value))
      (MeasurableMap.comp afterMeasurable beforeMeasurable) setMeasurable]
  rfl

@[simp] public theorem map_zero (function : α → β)
    (measurable : MeasurableMap source middle function) :
    (zero source).map function measurable = zero middle := by
  apply Measure.ext
  intro set setMeasurable
  rw [(zero source).map_apply function measurable setMeasurable,
    zero_apply, zero_apply]

public theorem map_add (left right : Measure source)
    (function : α → β)
    (measurable : MeasurableMap source middle function) :
    (add left right).map function measurable =
      add (left.map function measurable) (right.map function measurable) := by
  apply Measure.ext
  intro set setMeasurable
  rw [(add left right).map_apply function measurable setMeasurable,
    add_apply_measurable left right (measurable setMeasurable),
    add_apply_measurable (left.map function measurable)
      (right.map function measurable) setMeasurable,
    left.map_apply function measurable setMeasurable,
    right.map_apply function measurable setMeasurable]

public theorem map_smul (factor : ENNReal) (measure : Measure source)
    (function : α → β)
    (measurable : MeasurableMap source middle function) :
    (smul factor measure).map function measurable =
      smul factor (measure.map function measurable) := by
  apply Measure.ext
  intro set setMeasurable
  rw [(smul factor measure).map_apply function measurable setMeasurable,
    smul_apply_measurable factor measure (measurable setMeasurable),
    smul_apply_measurable factor (measure.map function measurable)
      setMeasurable,
    measure.map_apply function measurable setMeasurable]


/-- Pushforward commutes with restriction along the inverse image of a measurable region. -/
public theorem map_restrict (measure : Measure source) (function : α → β)
    (measurable : MeasurableMap source middle function) {region : Set β}
    (regionMeasurable : middle.Measurable region) :
    (measure.restrict (Set.preimage function region)).map function measurable =
      (measure.map function measurable).restrict region := by
  apply Measure.ext
  intro set setMeasurable
  rw [Measure.map_apply _ _ _ setMeasurable,
    Measure.restrict_apply _ _ (measurable setMeasurable),
    Measure.restrict_apply _ _ setMeasurable,
    Measure.map_apply _ _ _ (middle.inter setMeasurable regionMeasurable)]
  rfl

end Measure

end Problib.Measure
