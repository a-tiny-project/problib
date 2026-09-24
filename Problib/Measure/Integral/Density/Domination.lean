module

public import Problib.Measure.Integral.Density.Algebra
public import Problib.Measure.Additive.Finite
public import Problib.Measure.Additive.Partition
public import Problib.Real.Series.Cofinality

set_option autoImplicit false

/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying

Adapted from Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Candidate dominated densities and total weighted mass maximization guide the
construction without signed measures.
-/

namespace Problib.Measure.Measure

open Problib.Real

universe u

variable {alpha : Type u} {space : Space alpha}

/-- A measurable density whose weighted reference measure does not exceed the
target measure on measurable sets. -/
public structure IsSubdensity (target reference : Measure space) (density : alpha → ENNReal) : Prop where
  measurable : ENNRealMeasurable space density
  bound : ∀ set, space.Measurable set → ENNReal.le ((reference.withDensity density) set) (target set)

namespace IsSubdensity

variable {target reference : Measure space} {left right : alpha → ENNReal}

/-- The constant zero density is a subdensity for any target and reference
measures. -/
public theorem zero (target reference : Measure space) :
    IsSubdensity target reference (fun _ => ENNReal.zero) := by
  refine ⟨ENNRealMeasurable.constant space ENNReal.zero, ?_⟩
  intro set _
  rw [reference.withDensity_zero, Measure.zero_apply]
  exact ENNReal.zero_le _

/-- Pointwise maximum of two subdensities is a subdensity. -/
public theorem max (leftBound : IsSubdensity target reference left)
    (rightBound : IsSubdensity target reference right) :
    IsSubdensity target reference (fun value => ENNReal.max (left value) (right value)) := by
  refine ⟨leftBound.measurable.max rightBound.measurable, ?_⟩
  intro set measurable
  let region := fun value => ENNReal.le (left value) (right value)
  have regionMeasurable : space.Measurable region :=
    leftBound.measurable.le_set rightBound.measurable
  rw [reference.withDensity_max leftBound.measurable rightBound.measurable,
    Measure.add_apply_measurable _ _ measurable,
    reference.withDensity_restrict right regionMeasurable,
    reference.withDensity_restrict left (space.complement regionMeasurable),
    (reference.withDensity right).restrict_apply region measurable,
    (reference.withDensity left).restrict_apply (Set.complement region) measurable,
    ← target.inter_add_difference set regionMeasurable]
  exact ENNReal.add_le_add
    (rightBound.bound _ (space.inter measurable regionMeasurable))
    (leftBound.bound _ (space.inter measurable (space.complement regionMeasurable)))

/-- Prefix maximum of a sequence of subdensities preserves the subdensity
property at every stage. -/
public theorem prefixMax {densities : Nat → alpha → ENNReal}
    (bounds : ∀ index, IsSubdensity target reference (densities index)) (stage : Nat) :
    IsSubdensity target reference
      (fun value => ENNReal.prefixMax (fun index => densities index value) stage) := by
  induction stage with
  | zero => exact bounds 0
  | succ stage induction => exact max induction (bounds (stage + 1))

/-- Countable pointwise supremum of an arbitrary sequence of subdensities is a
subdensity.

The proof evaluates through prefix maxima and needs no monotonicity premise on the
input sequence. -/
public theorem iSup {densities : Nat → alpha → ENNReal}
    (bounds : ∀ index, IsSubdensity target reference (densities index)) :
    IsSubdensity target reference
      (fun value => ENNReal.iSup (fun index => densities index value)) := by
  refine ⟨ENNRealMeasurable.iSup (fun index => (bounds index).measurable), ?_⟩
  intro set measurable
  have equal : (fun value => ENNReal.iSup (fun index => densities index value)) =
      (fun value => ENNReal.iSup
        (fun stage => ENNReal.prefixMax (fun index => densities index value) stage)) := by
    funext value
    exact (ENNReal.iSup_prefixMax _).symm
  rw [equal, reference.withDensity_iSup_apply _ (fun stage => (prefixMax bounds stage).measurable)
    (fun stage value => ENNReal.prefixMax_step _ stage) measurable]
  exact ENNReal.iSup_le (fun stage => (prefixMax bounds stage).bound set measurable)

/-- A subdensity against a finite target measure produces a finite weighted
reference measure. -/
public theorem to_finite {density : alpha → ENNReal}
    (bound : IsSubdensity target reference density) (targetFinite : IsFinite target) :
    IsFinite (reference.withDensity density) :=
  IsFinite.of_le targetFinite (bound.bound Set.univ space.univ)

/-- A subdensity achieving maximal total weighted mass on the universal set
exists without finiteness premises.

The theorem guarantees maximal weighted total mass over candidate subdensities.
The theorem does not guarantee a pointwise greatest density or greatest measure.
Infinite total mass can make this total mass comparison uninformative.
Finiteness enters in the residual contradiction. -/
public theorem exists_maximizer (target reference : Measure space) :
    ∃ density, IsSubdensity target reference density ∧
      ∀ other, IsSubdensity target reference other →
        ENNReal.le ((reference.withDensity other) Set.univ)
          ((reference.withDensity density) Set.univ) := by
  classical
  let values := fun mass => ∃ density, IsSubdensity target reference density ∧
    (reference.withDensity density) Set.univ = mass
  have nonempty : ∃ mass, values mass :=
    ⟨_, (fun _ => ENNReal.zero), zero target reference, rfl⟩
  rcases ENNReal.exists_sequence_supremum nonempty with ⟨masses, members, supremum⟩
  let densities := fun index => Classical.choose (members index)
  have bounds : ∀ index, IsSubdensity target reference (densities index) :=
    fun index => (Classical.choose_spec (members index)).1
  have totals : ∀ index, (reference.withDensity (densities index)) Set.univ = masses index :=
    fun index => (Classical.choose_spec (members index)).2
  let density := fun value => ENNReal.iSup (fun index => densities index value)
  refine ⟨density, iSup bounds, ?_⟩
  intro other otherBound
  have upper : ENNReal.le ((reference.withDensity other) Set.univ) (ENNReal.supremum values) :=
    ENNReal.le_supremum ⟨other, otherBound, rfl⟩
  rw [← supremum] at upper
  apply ENNReal.le_trans upper
  apply ENNReal.iSup_le
  intro index
  rw [← totals index, reference.withDensity_apply _ space.univ,
    reference.withDensity_apply _ space.univ]
  exact lintegral_mono _ (fun value => ENNReal.le_iSup (fun index => densities index value) index)

end IsSubdensity

end Problib.Measure.Measure
