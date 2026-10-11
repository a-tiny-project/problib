module

public import Problib.Measure.Kernel.Basic
public import Problib.Measure.Decomposition.Hahn.Basic
public import Problib.Measure.Product

set_option autoImplicit false

/-!
# Kernel Hahn decompositions

Defines jointly measurable Hahn decompositions between two transition kernels,
ensuring fiberwise positive and negative sets with product-measurable graph.
-/

namespace Problib.Measure.Kernel

open Problib.Real

universe u v

variable {α : Type u} {β : Type v} {source : Space α} {target : Space β}

/-- A jointly measurable Hahn decomposition of two transition kernels.
It divides the target space for each input into positive and negative regions
with a product-measurable indicator relation. -/
public structure HahnDecomposition (left right : Kernel source target) where
  region : α → Set β
  measurable : (Space.product source target).Measurable (fun pair => region pair.1 pair.2)
  positive : ∀ input, ∀ {set}, target.Measurable set → Set.Subset set (region input) →
    ENNReal.le (right input set) (left input set)
  negative : ∀ input, ∀ {set}, target.Measurable set → Set.Subset set (Set.complement (region input)) →
    ENNReal.le (left input set) (right input set)

namespace HahnDecomposition

variable {left right : Kernel source target}

/-- Fiberwise specialization of a kernel Hahn decomposition to a measure Hahn decomposition. -/
@[expose] public def fiber (decomposition : HahnDecomposition left right) (input : α) :
    Measure.HahnDecomposition (left input) (right input) where
  region := decomposition.region input
  measurable := (Space.pair_measurable (MeasurableMap.constant target source input)
    (MeasurableMap.identity target)) decomposition.measurable
  positive := decomposition.positive input
  negative := decomposition.negative input

/-- Dual Hahn decomposition exchanging left and right kernels by taking the complement region. -/
@[expose] public def complement (decomposition : HahnDecomposition left right) :
    HahnDecomposition right left where
  region := fun input => Set.complement (decomposition.region input)
  measurable := (Space.product source target).complement decomposition.measurable
  positive := decomposition.negative
  negative := by
    intro input set measurable included
    rw [Set.complement_complement] at included
    exact decomposition.positive input measurable included

end HahnDecomposition

end Problib.Measure.Kernel
