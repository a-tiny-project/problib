module

public import Problib.Measure.Product
public import Problib.Measure.Dynkin.Basic

set_option autoImplicit false

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Adapted from Mathlib/MeasureTheory/Measure/Prod.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

-/

namespace Problib.Measure

universe u v

namespace Space

variable {alpha : Type u} {beta : Type v}

/-- Measurable rectangles form a pi-system. -/
public theorem rectangle_piSystem (source : Space alpha)
    (target : Space beta) : PiSystem (Rectangle source target) := by
  rintro left right
    ⟨leftSet, leftTarget, leftMeasurable, leftTargetMeasurable, rfl⟩
    ⟨rightSet, rightTarget, rightMeasurable,
      rightTargetMeasurable, rfl⟩
  refine ⟨Set.inter leftSet rightSet,
    Set.inter leftTarget rightTarget,
    source.inter leftMeasurable rightMeasurable,
    target.inter leftTargetMeasurable rightTargetMeasurable, ?_⟩
  apply Set.ext
  intro value
  exact ⟨
    fun member => ⟨⟨member.1.1, member.2.1⟩,
      ⟨member.1.2, member.2.2⟩⟩,
    fun member => ⟨⟨member.1.1, member.2.1⟩,
      ⟨member.1.2, member.2.2⟩⟩⟩

/-- The universe is a measurable rectangle. -/
public theorem rectangle_contains_univ (source : Space alpha)
    (target : Space beta) : Rectangle source target Set.univ := by
  refine ⟨Set.univ, Set.univ, source.univ, target.univ, ?_⟩
  apply Set.ext
  intro value
  exact ⟨fun _ => ⟨True.intro, True.intro⟩, fun _ => True.intro⟩

end Space

end Problib.Measure
