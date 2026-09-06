module

public import Foundations.Measure.Additive.Core

set_option autoImplicit false

/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Loic Simon

Adapted from Mathlib/MeasureTheory/Measure/Decomposition/Hahn.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny uses an extended-nonnegative-real score instead of signed real measure
subtraction.
-/

namespace Foundations.Measure.Measure

open Foundations.Real

universe u

variable {alpha : Type u} {space : Space alpha}

/-- A certificate that a measurable region compares two measures.
The left measure dominates on the region, and the right measure dominates on its
complement. -/
public structure HahnDecomposition (left right : Measure space) where
  region : Set alpha
  measurable : space.Measurable region
  positive : ∀ {set}, space.Measurable set → Set.Subset set region →
    ENNReal.le (right set) (left set)
  negative : ∀ {set}, space.Measurable set → Set.Subset set (Set.complement region) →
    ENNReal.le (left set) (right set)

/-- Reverses the measures in a Hahn decomposition by taking the complement of
the dominating region. -/
@[expose] public def HahnDecomposition.complement {left right : Measure space}
    (decomposition : HahnDecomposition left right) : HahnDecomposition right left where
  region := Set.complement decomposition.region
  measurable := space.complement decomposition.measurable
  positive := decomposition.negative
  negative := by
    intro set measurable included
    rw [Set.complement_complement] at included
    exact decomposition.positive measurable included

end Foundations.Measure.Measure
