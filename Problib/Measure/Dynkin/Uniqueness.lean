module

public import Problib.Measure.Additive.Finite
public import Problib.Measure.Dynkin.PiLambda

set_option autoImplicit false

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Copyright (c) 2021 Martin Zinkevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Martin Zinkevich, Rémy Degenne

Adapted from Mathlib/MeasureTheory/PiSystem.lean and
Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny uses explicit finite-measure premises and unconditional pi-systems.
-/

namespace Problib.Measure

open Problib.Real

universe u

variable {α : Type u}

public section

namespace Measure

variable {space : Space α}

private theorem union_complement (set : Set α) :
    Set.union set (Set.complement set) = Set.univ := by
  classical
  apply Set.ext
  intro value
  constructor
  · intro member
    exact True.intro
  · intro _
    by_cases member : set value
    · exact Or.inl member
    · exact Or.inr member

private theorem disjoint_complement (set : Set α) :
    Set.Disjoint set (Set.complement set) :=
  fun {_} member absent => absent member

private def equalitySystem (left right : Measure space)
    (leftFinite : IsFinite left) (rightFinite : IsFinite right)
    (totalEqual : left Set.univ = right Set.univ) : DynkinSystem α where
  Contains set := space.Measurable set ∧ left set = right set
  empty := ⟨space.empty, by rw [left.empty_apply, right.empty_apply]⟩
  complement := by
    intro set property
    have setMeasurable := property.1
    have complementMeasurable := space.complement setMeasurable
    refine ⟨complementMeasurable, ?_⟩
    have leftPartition := left.union_disjoint setMeasurable
      complementMeasurable (disjoint_complement set)
    have rightPartition := right.union_disjoint setMeasurable
      complementMeasurable (disjoint_complement set)
    rw [union_complement set] at leftPartition rightPartition
    have leftSetFinite : ENNReal.Finite (left set) :=
      ENNReal.finite_of_le (left.mono (Set.subset_univ set)) leftFinite.univ_finite
    have rightSetFinite : ENNReal.Finite (right set) :=
      ENNReal.finite_of_le (right.mono (Set.subset_univ set)) rightFinite.univ_finite
    calc
      left (Set.complement set) =
          ENNReal.sub (left Set.univ) (left set) := by
        rw [leftPartition, ENNReal.add_sub_cancel_left leftSetFinite]
      _ = ENNReal.sub (right Set.univ) (right set) := by
        rw [totalEqual, property.2]
      _ = right (Set.complement set) := by
        rw [rightPartition, ENNReal.add_sub_cancel_left rightSetFinite]
  iUnion := by
    intro sets disjoint properties
    let measurable : ∀ index, space.Measurable (sets index) :=
      fun index => (properties index).1
    refine ⟨space.iUnion measurable, ?_⟩
    calc
      left (Set.iUnion sets) =
          ENNReal.tsum (fun index => left (sets index)) :=
        left.iUnion_disjoint sets measurable disjoint
      _ = ENNReal.tsum (fun index => right (sets index)) := by
        apply ENNReal.tsum_congr
        intro index
        exact (properties index).2
      _ = right (Set.iUnion sets) :=
        (right.iUnion_disjoint sets measurable disjoint).symm

/-- Finite measures agreeing on a generating pi-system containing `univ`
agree on the whole measurable space. -/
theorem ext_of_generate {left right : Measure space}
    (generator : Set (Set α))
    (generates : space = Space.generated generator)
    (pi : PiSystem generator)
    (containsUniv : generator Set.univ)
    (leftFinite : IsFinite left) (rightFinite : IsFinite right)
    (agree : ∀ set, generator set → left set = right set) :
    left = right := by
  have totalEqual : left Set.univ = right Set.univ :=
    agree Set.univ containsUniv
  apply Measure.ext
  intro set setMeasurable
  have generatedMeasurable :
      (Space.generated generator).Measurable set := by
    rw [← generates]
    exact setMeasurable
  have generatedContains :
      (DynkinSystem.generated generator).Contains set :=
    (DynkinSystem.pi_lambda pi).mp generatedMeasurable
  have equalityContains := DynkinSystem.generated_minimal
    (equalitySystem left right leftFinite rightFinite totalEqual) (by
      intro basic basicMember
      refine ⟨?_, agree basic basicMember⟩
      rw [generates]
      exact Space.generated_contains basicMember) generatedContains
  exact equalityContains.2

end Measure

end

end Problib.Measure
