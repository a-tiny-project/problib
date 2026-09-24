module

public import Problib.Measure.Additive.Core

set_option autoImplicit false

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Adapted from Mathlib/MeasureTheory/Measure/Basic.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.
-/

namespace Problib.Measure

open Problib.Real

universe u

namespace Measure

variable {α : Type u} {space : Space α}

/-- The measure with zero content on every measurable set. -/
@[expose] public def zero (space : Space α) : Measure space where
  content := fun _ _ => ENNReal.zero
  empty := rfl
  content_iUnion_disjoint := by
    intro _ _ _
    exact ENNReal.tsum_zero.symm

public instance : Zero (Measure space) where
  zero := zero space

@[simp] public theorem zero_apply (set : Set α) :
    (zero space) set = ENNReal.zero := by
  apply ENNReal.eq_zero_of_le_zero
  have bound := (zero space).mono (Set.subset_univ set)
  have univZero : (zero space) Set.univ = ENNReal.zero := by
    rw [(zero space).apply_measurable space.univ]
    rfl
  rw [univZero] at bound
  exact bound

/-- Equate a measure to zero when the total mass of the universal set
vanishes. -/
public theorem eq_zero_iff_univ_eq_zero (measure : Measure space) :
    measure = zero space ↔ measure Set.univ = ENNReal.zero := by
  constructor
  · intro equal
    rw [equal, zero_apply]
  · intro totalZero
    apply Measure.ext
    intro set measurable
    rw [zero_apply]
    apply ENNReal.eq_zero_of_le_zero
    have bound := measure.mono (Set.subset_univ set)
    rw [totalZero] at bound
    exact bound

/-- Pointwise addition on measurable content. -/
@[expose] public def add (left right : Measure space) : Measure space where
  content := fun set measurable => ENNReal.add
    (left.content set measurable) (right.content set measurable)
  empty := by
    rw [left.empty, right.empty, ENNReal.add_zero]
  content_iUnion_disjoint := by
    intro sets measurable disjoint
    rw [left.content_iUnion_disjoint sets measurable disjoint,
      right.content_iUnion_disjoint sets measurable disjoint,
      ENNReal.tsum_add]

public instance : Add (Measure space) where
  add := add

@[simp] public theorem add_apply_measurable (left right : Measure space)
    {set : Set α} (measurable : space.Measurable set) :
    (add left right) set = ENNReal.add (left set) (right set) := by
  rw [(add left right).apply_measurable measurable,
    left.apply_measurable measurable, right.apply_measurable measurable]
  rfl

@[simp] public theorem zero_add (measure : Measure space) :
    add (zero space) measure = measure := by
  apply Measure.ext
  intro set measurable
  rw [add_apply_measurable (zero space) measure measurable,
    zero_apply, ENNReal.zero_add]

@[simp] public theorem add_zero (measure : Measure space) :
    add measure (zero space) = measure := by
  apply Measure.ext
  intro set measurable
  rw [add_apply_measurable measure (zero space) measurable,
    zero_apply, ENNReal.add_zero]

public theorem add_comm (left right : Measure space) :
    add left right = add right left := by
  apply Measure.ext
  intro set measurable
  rw [add_apply_measurable left right measurable,
    add_apply_measurable right left measurable, ENNReal.add_comm]

public theorem add_assoc (first second third : Measure space) :
    add (add first second) third = add first (add second third) := by
  apply Measure.ext
  intro set measurable
  rw [add_apply_measurable (add first second) third measurable,
    add_apply_measurable first second measurable,
    add_apply_measurable first (add second third) measurable,
    add_apply_measurable second third measurable, ENNReal.add_assoc]

/-- Scale measurable content by an extended nonnegative real. -/
@[expose] public noncomputable def smul (factor : ENNReal)
    (measure : Measure space) : Measure space where
  content := fun set measurable => ENNReal.mul factor
    (measure.content set measurable)
  empty := by
    rw [measure.empty, ENNReal.mul_zero]
  content_iUnion_disjoint := by
    intro sets measurable disjoint
    rw [measure.content_iUnion_disjoint sets measurable disjoint,
      ENNReal.tsum_mul_left]

public noncomputable instance : SMul ENNReal (Measure space) where
  smul := smul

@[simp] public theorem smul_apply_measurable (factor : ENNReal)
    (measure : Measure space) {set : Set α}
    (measurable : space.Measurable set) :
    (smul factor measure) set = ENNReal.mul factor (measure set) := by
  rw [(smul factor measure).apply_measurable measurable,
    measure.apply_measurable measurable]
  rfl

@[simp] public theorem zero_smul (measure : Measure space) :
    smul ENNReal.zero measure = zero space := by
  apply Measure.ext
  intro set measurable
  rw [smul_apply_measurable ENNReal.zero measure measurable,
    zero_apply, ENNReal.zero_mul]

@[simp] public theorem one_smul (measure : Measure space) :
    smul ENNReal.one measure = measure := by
  apply Measure.ext
  intro set measurable
  rw [smul_apply_measurable ENNReal.one measure measurable,
    ENNReal.one_mul]

public theorem smul_add (factor : ENNReal) (left right : Measure space) :
    smul factor (add left right) =
      add (smul factor left) (smul factor right) := by
  apply Measure.ext
  intro set measurable
  rw [smul_apply_measurable factor (add left right) measurable,
    add_apply_measurable left right measurable,
    add_apply_measurable (smul factor left) (smul factor right) measurable,
    smul_apply_measurable factor left measurable,
    smul_apply_measurable factor right measurable, ENNReal.mul_add]

public theorem smul_smul (first second : ENNReal)
    (measure : Measure space) :
    smul first (smul second measure) =
      smul (ENNReal.mul first second) measure := by
  apply Measure.ext
  intro set measurable
  rw [smul_apply_measurable first (smul second measure) measurable,
    smul_apply_measurable second measure measurable,
    smul_apply_measurable (ENNReal.mul first second) measure measurable,
    ENNReal.mul_assoc]

end Measure

end Problib.Measure
