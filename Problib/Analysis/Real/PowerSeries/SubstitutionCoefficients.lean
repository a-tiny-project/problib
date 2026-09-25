module

public import Problib.Analysis.Real.PowerSeries.SubstitutionMonomial

/-! Finite coefficients of a formal multivariate substitution. An outer
multiindex of degree greater than the requested source degree cannot
contribute when every inner series has zero constant coefficient. -/

set_option autoImplicit false

namespace Problib.Analysis.Real.PowerSeries

open Problib.Real.Construction.Dedekind

noncomputable section

private instance : Std.Associative (α := selection.Carrier) add :=
  ⟨fun left middle right => add_assoc left middle right⟩

@[expose] public def outerIndicesThrough (target degreeBound : Nat) :
    List (MultiIndex.carrier target) :=
  (List.range (degreeBound + 1)).flatMap
    (MultiIndex.degreeShell target)

public theorem mem_outerIndicesThrough {target : Nat}
    (index : MultiIndex.carrier target) (degreeBound : Nat)
    (included : MultiIndex.degree target index ≤ degreeBound) :
    index ∈ outerIndicesThrough target degreeBound := by
  apply List.mem_flatMap.mpr
  exact ⟨MultiIndex.degree target index,
    List.mem_range.mpr (by omega),
    MultiIndex.mem_degreeShell target index⟩

@[expose] public noncomputable def substitutionCoefficientThrough
    {source target : Nat}
    (outer : MultiIndex.carrier target → selection.Carrier)
    (inner : Fin target → Convergent source)
    (radius : selection.Carrier) (positive : lt zero radius)
    (below : ∀ coordinate, le radius (inner coordinate).radius)
    (degreeBound : Nat) (index : MultiIndex.carrier source) :
    selection.Carrier :=
  (outerIndicesThrough target degreeBound).foldr
    (fun outerIndex total =>
      add (mul (outer outerIndex)
        ((seriesMonomialWithin inner radius positive below
          outerIndex).coefficients index)) total) zero

@[expose] public noncomputable def substitutionCoefficients
    {source target : Nat}
    (outer : MultiIndex.carrier target → selection.Carrier)
    (inner : Fin target → Convergent source)
    (radius : selection.Carrier) (positive : lt zero radius)
    (below : ∀ coordinate, le radius (inner coordinate).radius) :
    MultiIndex.carrier source → selection.Carrier :=
  fun index => substitutionCoefficientThrough outer inner radius positive
    below (MultiIndex.degree source index) index

private theorem foldr_zero_terms {α : Type}
    (indices : List α) (term : α → selection.Carrier)
    (zeroTerm : ∀ index, index ∈ indices → term index = zero)
    (initial : selection.Carrier) :
    indices.foldr (fun index total => add (term index) total) initial =
      initial := by
  induction indices with
  | nil => rfl
  | cons index rest induction =>
      rw [List.foldr_cons, zeroTerm index List.mem_cons_self, zero_add]
      exact induction (fun later member => zeroTerm later
        (List.mem_cons_of_mem index member))

private theorem outer_shell_coefficients_zero
    {source target degreeValue sourceDegree : Nat}
    (outer : MultiIndex.carrier target → selection.Carrier)
    (inner : Fin target → Convergent source)
    (radius : selection.Carrier) (positive : lt zero radius)
    (below : ∀ coordinate, le radius (inner coordinate).radius)
    (zeroConstant : ∀ coordinate, (inner coordinate).coefficients
      (MultiIndex.zeroIndex source) = zero)
    (index : MultiIndex.carrier source)
    (degreeAbove : sourceDegree < degreeValue)
    (indexDegree : MultiIndex.degree source index = sourceDegree) :
    ∀ outerIndex,
      outerIndex ∈ MultiIndex.degreeShell target degreeValue →
      mul (outer outerIndex)
        ((seriesMonomialWithin inner radius positive below
          outerIndex).coefficients index) = zero := by
  intro outerIndex member
  have vanish := seriesMonomialWithin_order inner radius positive below
    zeroConstant outerIndex
  have belowDegree : MultiIndex.degree source index <
      MultiIndex.degree target outerIndex := by
    rw [indexDegree, MultiIndex.degree_of_mem_shell member]
    exact degreeAbove
  rw [vanish index belowDegree, mul_zero]

public theorem substitutionCoefficientThrough_succ_stable
    {source target degreeValue : Nat}
    (outer : MultiIndex.carrier target → selection.Carrier)
    (inner : Fin target → Convergent source)
    (radius : selection.Carrier) (positive : lt zero radius)
    (below : ∀ coordinate, le radius (inner coordinate).radius)
    (zeroConstant : ∀ coordinate, (inner coordinate).coefficients
      (MultiIndex.zeroIndex source) = zero)
    (index : MultiIndex.carrier source)
    (degreeBelow : MultiIndex.degree source index ≤ degreeValue) :
    substitutionCoefficientThrough outer inner radius positive below
      (degreeValue + 1) index =
    substitutionCoefficientThrough outer inner radius positive below
      degreeValue index := by
  unfold substitutionCoefficientThrough outerIndicesThrough
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
  rw [List.foldr_append]
  have zeroShell := outer_shell_coefficients_zero
    (degreeValue := degreeValue + 1)
    (sourceDegree := MultiIndex.degree source index)
    outer inner radius positive below zeroConstant index
    (by omega) rfl
  rw [foldr_zero_terms _ _ zeroShell]

public theorem substitutionCoefficientThrough_stable
    {source target : Nat}
    (outer : MultiIndex.carrier target → selection.Carrier)
    (inner : Fin target → Convergent source)
    (radius : selection.Carrier) (positive : lt zero radius)
    (below : ∀ coordinate, le radius (inner coordinate).radius)
    (zeroConstant : ∀ coordinate, (inner coordinate).coefficients
      (MultiIndex.zeroIndex source) = zero)
    (index : MultiIndex.carrier source)
    (degreeBound : Nat)
    (included : MultiIndex.degree source index ≤ degreeBound) :
    substitutionCoefficientThrough outer inner radius positive below
      degreeBound index =
    substitutionCoefficients outer inner radius positive below index := by
  obtain ⟨extra, equal⟩ := Nat.exists_eq_add_of_le included
  subst degreeBound
  induction extra with
  | zero => rfl
  | succ extra induction =>
      rw [Nat.add_succ,
        substitutionCoefficientThrough_succ_stable outer inner radius
          positive below zeroConstant index (by omega)]
      exact induction (by omega)

end

end Problib.Analysis.Real.PowerSeries
