module

public import Problib.Measure.Additive.Finite
public import Problib.Measure.Additive.Sum
public import Problib.Measure.Set.Family

set_option autoImplicit false

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Adapted from Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny keeps decompositions as constructive data instead of typeclasses.
-/

namespace Problib.Measure

open Problib.Real

universe u v

namespace Measure

variable {alpha : Type u} {space : Space alpha}

/-- A countable measurable cover whose pieces have finite mass. -/
public structure FiniteCover (measure : Measure space) : Type u where
  sets : Nat → Set alpha
  measurable : ∀ index, space.Measurable (sets index)
  finite : ∀ index, ENNReal.Finite (measure (sets index))
  cover : Set.iUnion sets = Set.univ

/-- A countable measurable cover whose pieces have finite mass and are pairwise
disjoint. -/
public structure DisjointFiniteCover (measure : Measure space) extends FiniteCover measure where
  pairwise : Set.PairwiseDisjoint sets

/-- Restricting a measure to any piece in a finite cover produces a finite
measure. -/
public theorem FiniteCover.restrict_finite {measure : Measure space}
    (cover : FiniteCover measure) (index : Nat) : IsFinite (measure.restrict (cover.sets index)) := by
  constructor
  rw [measure.restrict_apply_univ]
  exact cover.finite index

/-- Increasing finite-mass measurable sets spanning the whole space. -/
public structure SigmaFinite (measure : Measure space) : Type u where
  sets : Nat → Set alpha
  measurable : ∀ index, space.Measurable (sets index)
  monotone : Set.MonotoneFamily sets
  finite : ∀ index, ENNReal.Finite (measure (sets index))
  cover : Set.iUnion sets = Set.univ

/-- A measure presented as a countable sum of finite measures. -/
public structure SFinite (measure : Measure space) : Type u where
  components : Nat → Measure space
  finite : ∀ index, IsFinite (components index)
  sum_eq : Measure.sum components = measure

namespace SigmaFinite

/-- Construct a sigma-finite witness for a dominated measure.
The construction uses the exhausting sequence from the reference measure. -/
public def of_le {left right : Measure space} (finite : SigmaFinite right)
    (included : ∀ set, space.Measurable set → ENNReal.le (left set) (right set)) :
    SigmaFinite left where
  sets := finite.sets
  measurable := finite.measurable
  monotone := finite.monotone
  finite := fun index => ENNReal.finite_of_le
    (included (finite.sets index) (finite.measurable index)) (finite.finite index)
  cover := finite.cover

/-- Every sigma-finite measure admits a disjoint finite cover through disjointed
difference sets. -/
public noncomputable def disjointCover {measure : Measure space}
    (finite : SigmaFinite measure) : DisjointFiniteCover measure where
  sets := Set.disjointed finite.sets
  measurable := space.disjointed_measurable finite.measurable
  finite := fun index => ENNReal.finite_of_le
    (measure.mono (Set.disjointed_subset finite.sets index)) (finite.finite index)
  cover := (Set.iUnion_disjointed finite.sets).trans finite.cover
  pairwise := Set.disjointed_pairwise finite.sets

private theorem prefix_finite {measure : Measure space}
    (cover : FiniteCover measure) :
    ∀ count, ENNReal.Finite (measure (Set.prefixUnion cover.sets count)) := by
  intro count
  induction count with
  | zero =>
      rw [Set.prefixUnion_zero, measure.empty_apply]
      exact True.intro
  | succ count induction =>
      apply ENNReal.finite_of_le (measure.union_le
        (Set.prefixUnion cover.sets count) (cover.sets count))
      exact ENNReal.add_finite induction (cover.finite count)

/-- Normalize an arbitrary finite-mass cover to increasing prefix unions. -/
public noncomputable def ofCover {measure : Measure space}
    (cover : FiniteCover measure) : SigmaFinite measure where
  sets := Set.prefixUnion cover.sets
  measurable := space.prefixUnion_measurable cover.measurable
  monotone := Set.prefixUnion_monotone cover.sets
  finite := prefix_finite cover
  cover := (Set.iUnion_prefixUnion cover.sets).trans cover.cover

/-- Every finite measure is sigma-finite. -/
public def ofFinite {measure : Measure space}
    (finite : IsFinite measure) : SigmaFinite measure where
  sets := fun _ => Set.univ
  measurable := fun _ => space.univ
  monotone := by
    intro first second firstSecond value member
    exact True.intro
  finite := fun _ => finite.univ_finite
  cover := by
    apply Set.ext
    intro value
    exact ⟨fun _ => True.intro, fun _ => ⟨0, True.intro⟩⟩

/-- Restricting a sigma-finite measure to an arbitrary region preserves
sigma-finiteness without requiring region measurability. -/
public def restrict {measure : Measure space} (finite : SigmaFinite measure)
    (region : Set alpha) : SigmaFinite (measure.restrict region) where
  sets := finite.sets
  measurable := finite.measurable
  monotone := finite.monotone
  finite := fun index => ENNReal.finite_of_le
    (measure.restrict_le region (finite.sets index)) (finite.finite index)
  cover := finite.cover

end SigmaFinite

namespace SFinite

private def singletonComponents (measure : Measure space) :
    Nat → Measure space
  | 0 => measure
  | _ + 1 => Measure.zero space

/-- A finite measure is a one-component s-finite measure. -/
public noncomputable def ofFinite {measure : Measure space}
    (finite : IsFinite measure) : SFinite measure where
  components := singletonComponents measure
  finite := by
    intro index
    cases index with
    | zero => exact finite
    | succ index => exact IsFinite.zero space
  sum_eq := by
    apply Measure.ext
    intro set setMeasurable
    rw [Measure.sum_apply (singletonComponents measure) setMeasurable]
    exact ENNReal.tsum_eq_of_at_most_one_nonzero
      (fun index => singletonComponents measure index set) 0 (by
        intro index different
        cases index with
        | zero => exact False.elim (different rfl)
        | succ index => exact Measure.zero_apply set)

/-- The zero measure is s-finite. -/
public noncomputable def zero (space : Space alpha) :
    SFinite (Measure.zero space) :=
  ofFinite (IsFinite.zero space)

/-- S-finite measures are closed under addition. -/
public noncomputable def add {left right : Measure space}
    (leftFinite : SFinite left) (rightFinite : SFinite right) :
    SFinite (Measure.add left right) where
  components := fun index => Measure.add
    (leftFinite.components index) (rightFinite.components index)
  finite := fun index => IsFinite.add
    (leftFinite.finite index) (rightFinite.finite index)
  sum_eq := by
    rw [Measure.sum_add, leftFinite.sum_eq, rightFinite.sum_eq]

/-- A countable sum of s-finite measures is s-finite. -/
public noncomputable def sum (measures : Nat → Measure space)
    (finite : ∀ index, SFinite (measures index)) :
    SFinite (Measure.sum measures) where
  components := Measure.flatten
    (fun row column => (finite row).components column)
  finite := by
    intro index
    exact (finite (Countable.Pair.decode index).1).finite
      (Countable.Pair.decode index).2
  sum_eq := by
    rw [Measure.sum_double]
    apply congrArg Measure.sum
    funext row
    exact (finite row).sum_eq

/-- Measurable pushforward preserves s-finiteness. -/
public noncomputable def map {beta : Type v} {target : Space beta}
    {measure : Measure space} (finite : SFinite measure)
    (function : alpha → beta)
    (measurable : MeasurableMap space target function) :
    SFinite (measure.map function measurable) where
  components := fun index =>
    (finite.components index).map function measurable
  finite := fun index =>
    (finite.finite index).map function measurable
  sum_eq := by
    rw [← Measure.map_sum, finite.sum_eq]

/-- Restriction to a measurable region preserves s-finiteness. -/
public noncomputable def restrict {measure : Measure space}
    (finite : SFinite measure) {region : Set alpha}
    (regionMeasurable : space.Measurable region) :
    SFinite (measure.restrict region) where
  components := fun index => finite.components index |>.restrict region
  finite := fun index => (finite.finite index).restrict region
  sum_eq := by
    rw [← Measure.restrict_sum finite.components regionMeasurable,
      finite.sum_eq]

/-- Scaling by a finite factor preserves s-finiteness. -/
public noncomputable def smul {measure : Measure space}
    (finite : SFinite measure) (factor : ENNReal)
    (factorFinite : ENNReal.Finite factor) :
    SFinite (Measure.smul factor measure) where
  components := fun index => Measure.smul factor (finite.components index)
  finite := fun index =>
    (finite.finite index).smul factor factorFinite
  sum_eq := by
    apply Measure.ext
    intro set setMeasurable
    rw [Measure.sum_apply
        (fun index => Measure.smul factor (finite.components index))
        setMeasurable,
      Measure.smul_apply_measurable factor measure setMeasurable]
    calc
      ENNReal.tsum
          (fun index => Measure.smul factor (finite.components index) set) =
          ENNReal.tsum
            (fun index => ENNReal.mul factor (finite.components index set)) := by
        apply ENNReal.tsum_congr
        intro index
        exact Measure.smul_apply_measurable factor
          (finite.components index) setMeasurable
      _ = ENNReal.mul factor
          (ENNReal.tsum (fun index => finite.components index set)) :=
        ENNReal.tsum_mul_left factor
          (fun index => finite.components index set)
      _ = ENNReal.mul factor (Measure.sum finite.components set) := by
        rw [Measure.sum_apply finite.components setMeasurable]
      _ = ENNReal.mul factor (measure set) := by
        rw [finite.sum_eq]

end SFinite

/-- Increasing finite-mass spanning sets induce a disjoint finite-measure
decomposition. -/
public noncomputable def SigmaFinite.toSFinite {measure : Measure space}
    (finite : SigmaFinite measure) : SFinite measure := by
  let cover := finite.disjointCover
  refine {
    components := fun index => measure.restrict (cover.sets index)
    finite := cover.toFiniteCover.restrict_finite
    sum_eq := ?_
  }
  calc
    Measure.sum (fun index => measure.restrict (cover.sets index)) =
        measure.restrict (Set.iUnion cover.sets) :=
      (Measure.restrict_iUnion measure cover.sets cover.measurable cover.pairwise).symm
    _ = measure.restrict Set.univ := by
      rw [cover.cover]
    _ = measure := measure.restrict_univ

end Measure

end Problib.Measure
