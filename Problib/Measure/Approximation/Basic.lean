module

public import Problib.Measure.Additive.Core
public import Problib.Measure.Space.Algebra
public import Problib.Measure.Set.Difference
import Problib.Real.Nonnegative.Dyadic

set_option autoImplicit false

/-!
# Measure approximation by symmetric difference

Defines the symmetric difference extended pseudometric `setDistance` induced by
a measure. `Approximable` defines approximation within arbitrary positive error
by elements of any countable family.
-/

namespace Problib.Measure

open Problib.Real

universe u

variable {α : Type u} {space : Space α}

/-- Symmetric difference of two measurable sets is measurable. -/
public theorem Space.symmDiff_measurable {left right : Set α}
    (leftMeasurable : space.Measurable left) (rightMeasurable : space.Measurable right) :
    space.Measurable (Set.symmDiff left right) :=
  space.union (space.difference leftMeasurable rightMeasurable)
    (space.difference rightMeasurable leftMeasurable)

namespace Measure

/-- Extended pseudometric on sets defined by the measure of their symmetric difference: $\mu(A \mathbin{\Delta} B)$.
The distance takes values in `ENNReal` and can be infinite. -/
@[expose] public noncomputable def setDistance (measure : Measure space) (left right : Set α) :
    ENNReal := measure (Set.symmDiff left right)

/-- Distance from any set to itself is zero. -/
public theorem setDistance_self (measure : Measure space) (set : Set α) :
    measure.setDistance set set = ENNReal.zero := by
  rw [setDistance, Set.symmDiff_self, measure.empty_apply]

/-- Symmetric difference distance is symmetric. -/
public theorem setDistance_comm (measure : Measure space) (left right : Set α) :
    measure.setDistance left right = measure.setDistance right left := by
  rw [setDistance, Set.symmDiff_comm]
  rfl

/-- Complementation preserves symmetric difference distance. -/
public theorem setDistance_complement (measure : Measure space) (left right : Set α) :
    measure.setDistance (Set.complement left) (Set.complement right) =
      measure.setDistance left right := by
  rw [setDistance, Set.symmDiff_complement]
  rfl

/-- Triangle inequality for symmetric difference distance. -/
public theorem setDistance_triangle (measure : Measure space) (first middle last : Set α) :
    ENNReal.le (measure.setDistance first last)
      (ENNReal.add (measure.setDistance first middle) (measure.setDistance middle last)) :=
  ENNReal.le_trans (measure.mono (Set.symmDiff_triangle first middle last))
    (measure.union_le _ _)

/-- Subadditivity of symmetric difference distance across binary unions. -/
public theorem setDistance_union (measure : Measure space) (first second left right : Set α) :
    ENNReal.le (measure.setDistance (Set.union first second) (Set.union left right))
      (ENNReal.add (measure.setDistance first left) (measure.setDistance second right)) :=
  ENNReal.le_trans (measure.mono (Set.symmDiff_union first second left right))
    (measure.union_le _ _)

/-- Upper bound on the measure of a set by another set's measure plus their distance. -/
public theorem le_add_setDistance (measure : Measure space) (left right : Set α) :
    ENNReal.le (measure left) (ENNReal.add (measure right) (measure.setDistance left right)) :=
  ENNReal.le_trans (measure.mono (Set.subset_union_symmDiff left right)) (measure.union_le _ _)

/-- Predicate asserting that a region can be approximated within arbitrary $\varepsilon > 0$
in measure distance by members of a countable family. -/
@[expose] public def Approximable (measure : Measure space) (family : Nat → Set α)
    (region : Set α) : Prop :=
  ∀ epsilon : NNReal, NNReal.lt NNReal.zero epsilon →
    ∃ index, ENNReal.le (measure.setDistance region (family index)) (ENNReal.finite epsilon)

namespace Approximable

variable {measure : Measure space} {algebra : Space.CountableAlgebra space}

/-- Any member of the family is trivially approximable by itself. -/
public theorem member (family : Nat → Set α) (index : Nat) :
    measure.Approximable family (family index) := by
  intro epsilon _
  refine ⟨index, ?_⟩
  rw [setDistance_self]
  exact ENNReal.zero_le _

/-- The empty set is approximable by an algebra. -/
public theorem empty : measure.Approximable algebra.sets Set.empty := by
  rcases algebra.empty with ⟨index, equal⟩
  rw [← equal]
  exact member algebra.sets index

/-- Complements of approximable sets are approximable. -/
public theorem complement {region : Set α}
    (approximation : measure.Approximable algebra.sets region) :
    measure.Approximable algebra.sets (Set.complement region) := by
  intro epsilon positive
  rcases approximation epsilon positive with ⟨index, bound⟩
  rcases algebra.complement index with ⟨other, equal⟩
  refine ⟨other, ?_⟩
  rw [equal, setDistance_complement]
  exact bound

/-- Binary unions of approximable sets are approximable. -/
public theorem union {left right : Set α}
    (leftApproximation : measure.Approximable algebra.sets left)
    (rightApproximation : measure.Approximable algebra.sets right) :
    measure.Approximable algebra.sets (Set.union left right) := by
  intro epsilon positive
  have halfPositive := NNReal.half_positive positive
  rcases leftApproximation (NNReal.half epsilon) halfPositive with ⟨first, firstBound⟩
  rcases rightApproximation (NNReal.half epsilon) halfPositive with ⟨second, secondBound⟩
  rcases algebra.union first second with ⟨index, equal⟩
  refine ⟨index, ?_⟩
  rw [equal]
  have bound := ENNReal.le_trans (measure.setDistance_union left right _ _)
    (ENNReal.add_le_add firstBound secondBound)
  have halves : ENNReal.add (ENNReal.finite (NNReal.half epsilon))
      (ENNReal.finite (NNReal.half epsilon)) = ENNReal.finite epsilon :=
    congrArg ENNReal.finite (NNReal.half_add_half epsilon)
  rw [halves] at bound
  exact bound

/-- Finite prefix unions of approximable sets are approximable. -/
public theorem prefixUnion (sets : Nat → Set α)
    (approximation : ∀ index, measure.Approximable algebra.sets (sets index)) (count : Nat) :
    measure.Approximable algebra.sets (Set.prefixUnion sets count) := by
  induction count with
  | zero => exact empty
  | succ count induction => exact induction.union (approximation count)

end Approximable

end Measure

end Problib.Measure
