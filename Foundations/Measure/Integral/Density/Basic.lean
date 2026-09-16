module

public import Foundations.Measure.Integral.Lebesgue.Measure

set_option autoImplicit false

/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl

Adapted from Mathlib/MeasureTheory/Measure/WithDensity.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.
-/

namespace Foundations.Measure

open Foundations.Real

universe u

namespace Measure

variable {alpha : Type u} {space : Space alpha}

/-- The measure whose mass on a measurable set is the lower integral of the
density over that set. No measurability premise is needed for construction. -/
@[expose] public noncomputable def withDensity (measure : Measure space)
    (density : alpha → ENNReal) : Measure space where
  content := fun set _ => lintegral (measure.restrict set) density
  empty := by
    rw [measure.restrict_empty, lintegral_zero_measure]
  content_iUnion_disjoint := by
    intro sets measurable pairwise
    rw [measure.restrict_iUnion sets measurable pairwise,
      lintegral_sum_measure]

@[simp] public theorem withDensity_apply (measure : Measure space)
    (density : alpha → ENNReal) {set : Set alpha}
    (setMeasurable : space.Measurable set) :
    (measure.withDensity density) set =
      lintegral (measure.restrict set) density := by
  rw [(measure.withDensity density).apply_measurable setMeasurable]
  rfl

/-- An explicit reconstruction statement for a density relative to a base
measure. -/
@[expose] public def IsDensity (candidate base : Measure space)
    (density : alpha → ENNReal) : Prop :=
  candidate = base.withDensity density

public theorem isDensity_withDensity (base : Measure space)
    (density : alpha → ENNReal) :
    IsDensity (base.withDensity density) base density :=
  rfl

public theorem IsDensity.eq_withDensity {candidate base : Measure space}
    {density : alpha → ENNReal}
    (isDensity : IsDensity candidate base density) :
    candidate = base.withDensity density :=
  isDensity

public theorem IsDensity.apply {candidate base : Measure space}
    {density : alpha → ENNReal}
    (isDensity : IsDensity candidate base density)
    {set : Set alpha} (setMeasurable : space.Measurable set) :
    candidate set = lintegral (base.restrict set) density := by
  rw [isDensity, base.withDensity_apply density setMeasurable]

public theorem IsDensity.ext {left right base : Measure space}
    {density : alpha → ENNReal}
    (leftDensity : IsDensity left base density)
    (rightDensity : IsDensity right base density) :
    left = right :=
  leftDensity.trans rightDensity.symm

public theorem withDensity_ext {base : Measure space}
    {left right : alpha → ENNReal}
    (equal : ∀ set (_ : space.Measurable set),
      lintegral (base.restrict set) left =
        lintegral (base.restrict set) right) :
    base.withDensity left = base.withDensity right := by
  apply Measure.ext
  intro set setMeasurable
  rw [base.withDensity_apply left setMeasurable,
    base.withDensity_apply right setMeasurable]
  exact equal set setMeasurable

end Measure

end Foundations.Measure
