module

public import Problib.Measure.Decomposition.Hahn.Basic
public import Problib.Measure.Decomposition.Hahn.Limit

set_option autoImplicit false

/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Loic Simon

Adapted from Mathlib/MeasureTheory/Measure/Decomposition/Hahn.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny proves existence of the Hahn decomposition from score maximizers.
-/

namespace Problib.Measure.Measure

open Problib.Real

universe u

variable {alpha : Type u} {space : Space alpha}

/-- A measurable region maximizing the Hahn score is positive for the signed
measure difference `left - right`. -/
public theorem Hahn.positive_of_maximal {left right : Measure space}
    (leftFinite : IsFinite left) (rightFinite : IsFinite right)
    {region : Set alpha} (regionMeasurable : space.Measurable region)
    (maximal : ∀ other, space.Measurable other →
      ENNReal.le (Hahn.score left right other) (Hahn.score left right region)) :
    ∀ {set}, space.Measurable set → Set.Subset set region →
      ENNReal.le (right set) (left set) := by
  intro set setMeasurable included
  have intersection : Set.inter region set = set := by
    apply Set.ext
    intro value
    exact ⟨fun member => member.2, fun member => ⟨included member, member⟩⟩
  have partition := left.inter_add_difference region setMeasurable
  rw [intersection, ENNReal.add_comm (left set)] at partition
  have disjoint : Set.Disjoint (Set.complement region) set :=
    fun {_} outside member => outside (included member)
  have unionMass := right.union_disjoint (space.complement regionMeasurable)
    setMeasurable disjoint
  have gain :
      ENNReal.add (Hahn.score left right (Set.difference region set)) (left set) =
        ENNReal.add (Hahn.score left right region) (right set) := by
    unfold Hahn.score
    rw [Set.complement_difference, unionMass,
      ← ENNReal.add_assoc (left (Set.difference region set))
        (right (Set.complement region)) (right set),
      ENNReal.add_right_comm _ (right set) (left set),
      ENNReal.add_right_comm (left (Set.difference region set))
        (right (Set.complement region)) (left set), partition]
  have comparison := ENNReal.add_le_add_right
    (maximal (Set.difference region set) (space.difference regionMeasurable setMeasurable))
    (left set)
  rw [gain] at comparison
  exact ENNReal.le_of_add_le_add_left_of_finite (Hahn.score_finite leftFinite rightFinite region)
    comparison

/-- Constructs a Hahn decomposition from any measurable region maximizing the Hahn
score between two finite measures. -/
@[expose] public def HahnDecomposition.ofMaximal {left right : Measure space}
    (leftFinite : IsFinite left) (rightFinite : IsFinite right)
    (region : Set alpha) (measurable : space.Measurable region)
    (maximal : ∀ other, space.Measurable other →
      ENNReal.le (Hahn.score left right other) (Hahn.score left right region)) :
    HahnDecomposition left right := by
  refine {
    region := region
    measurable := measurable
    positive := Hahn.positive_of_maximal leftFinite rightFinite measurable maximal
    negative := ?_
  }
  apply Hahn.positive_of_maximal rightFinite leftFinite (space.complement measurable)
  intro other otherMeasurable
  have comparison := maximal (Set.complement other) (space.complement otherMeasurable)
  rw [Hahn.score_complement] at comparison
  rw [Hahn.score_complement]
  exact comparison

/-- For any two finite measures, there exists a Hahn decomposition separating
the space into regions where each measure dominates the other. -/
public theorem exists_hahnDecomposition {left right : Measure space}
    (leftFinite : IsFinite left) (rightFinite : IsFinite right) :
    Nonempty (HahnDecomposition left right) := by
  rcases Hahn.exists_maximizer leftFinite rightFinite with ⟨region, measurable, maximal⟩
  exact ⟨HahnDecomposition.ofMaximal leftFinite rightFinite region measurable maximal⟩

/-- Selects a Hahn decomposition certificate for two finite measures. -/
public noncomputable def HahnDecomposition.ofFinite {left right : Measure space}
    (leftFinite : IsFinite left) (rightFinite : IsFinite right) :
    HahnDecomposition left right :=
  Classical.choice (exists_hahnDecomposition leftFinite rightFinite)

end Problib.Measure.Measure
