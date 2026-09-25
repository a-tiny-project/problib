module

public import Problib.Analysis.Real.PowerSeries.SubstitutionComposition
public import Problib.Measure.Space

/-! Sets cut out by finitely many analytic nonpositive constraints on one open
Euclidean domain. The domain is part of the witness, not an implicit ambient
space. -/

set_option autoImplicit false

namespace Problib.Analysis.PAP

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real.PowerSeries
open Problib.Measure

/-- A finite system of analytic inequalities on a common open domain. -/
@[expose] public def AnalyticSet {dimension : Nat}
    (points : Set (Problib.Analysis.Real.FiniteVector.carrier dimension)) : Prop :=
  ∃ (region : Set (Problib.Analysis.Real.FiniteVector.carrier dimension))
    (constraints : List
      (Problib.Analysis.Real.FiniteVector.carrier dimension → selection.Carrier)),
    Problib.Analysis.Real.FiniteVector.IsOpen region ∧
    (∀ constraint, constraint ∈ constraints → AnalyticOn region constraint) ∧
    ∀ point, points point ↔
      region point ∧ ∀ constraint, constraint ∈ constraints →
        le (constraint point) zero

/-- The entire Euclidean carrier uses an empty list of constraints. -/
public theorem analytic_set_univ (dimension : Nat) :
    AnalyticSet (Set.univ : Set
      (Problib.Analysis.Real.FiniteVector.carrier dimension)) := by
  refine ⟨Set.univ, [],
    Problib.Analysis.Real.FiniteVector.is_open_univ dimension, ?_, ?_⟩
  · intro constraint member
    exact False.elim (List.not_mem_nil member)
  · intro point
    simp [Set.univ]

/-- The empty carrier is represented by the empty open domain. -/
public theorem analytic_set_empty (dimension : Nat) :
    AnalyticSet (Set.empty : Set
      (Problib.Analysis.Real.FiniteVector.carrier dimension)) := by
  refine ⟨Set.empty, [],
    Problib.Analysis.Real.FiniteVector.is_open_empty dimension, ?_, ?_⟩
  · intro constraint member
    exact False.elim (List.not_mem_nil member)
  · intro point
    simp [Set.empty]

/-- An open domain is analytic with no inequalities. -/
public theorem analytic_set_open {dimension : Nat}
    {region : Set (Problib.Analysis.Real.FiniteVector.carrier dimension)}
    (openRegion : Problib.Analysis.Real.FiniteVector.IsOpen region) :
    AnalyticSet region := by
  refine ⟨region, [], openRegion, ?_, ?_⟩
  · intro constraint member
    exact False.elim (List.not_mem_nil member)
  · intro point
    constructor
    · intro member
      exact ⟨member, fun constraint impossible =>
        False.elim (List.not_mem_nil impossible)⟩
    · exact fun member => member.1

/-- An analytic nonpositive inequality restricted to its open domain. -/
public theorem analytic_set_sublevel {dimension : Nat}
    {region : Set (Problib.Analysis.Real.FiniteVector.carrier dimension)}
    {function : Problib.Analysis.Real.FiniteVector.carrier dimension →
      selection.Carrier}
    (analytic : AnalyticOn region function) :
    AnalyticSet (fun point => region point ∧ le (function point) zero) := by
  refine ⟨region, [function], analytic.left, ?_, ?_⟩
  · intro constraint member
    have equal : constraint = function := by
      simpa only [List.mem_singleton] using member
    subst constraint
    exact analytic
  · intro point
    constructor
    · rintro ⟨inRegion, bound⟩
      exact ⟨inRegion, fun constraint member => by
        have equal : constraint = function := by
          simpa only [List.mem_singleton] using member
        subst constraint
        exact bound⟩
    · rintro ⟨inRegion, bounds⟩
      exact ⟨inRegion, bounds function (List.mem_singleton.mpr rfl)⟩

/-- Finite conjunction of analytic constraints is analytic. -/
public theorem analytic_set_inter {dimension : Nat}
    {left right : Set (Problib.Analysis.Real.FiniteVector.carrier dimension)}
    (leftAnalytic : AnalyticSet left) (rightAnalytic : AnalyticSet right) :
    AnalyticSet (Set.inter left right) := by
  rcases leftAnalytic with ⟨leftRegion, leftConstraints,
    leftOpen, leftAnalytic, leftCharacterization⟩
  rcases rightAnalytic with ⟨rightRegion, rightConstraints,
    rightOpen, rightAnalytic, rightCharacterization⟩
  let region : Set (Problib.Analysis.Real.FiniteVector.carrier dimension) :=
    Set.inter leftRegion rightRegion
  refine ⟨region, leftConstraints ++ rightConstraints,
    Problib.Analysis.Real.FiniteVector.is_open_inter leftOpen rightOpen,
    ?_, ?_⟩
  · intro constraint member
    rcases List.mem_append.mp member with leftMember | rightMember
    · exact analytic_on_open_subset
        (leftAnalytic constraint leftMember)
        (Problib.Analysis.Real.FiniteVector.is_open_inter leftOpen rightOpen)
        (fun _ inside => inside.left)
    · exact analytic_on_open_subset
        (rightAnalytic constraint rightMember)
        (Problib.Analysis.Real.FiniteVector.is_open_inter leftOpen rightOpen)
        (fun _ inside => inside.right)
  · intro point
    change (left point ∧ right point) ↔
      (region point ∧ ∀ constraint,
        constraint ∈ leftConstraints ++ rightConstraints →
          le (constraint point) zero)
    rw [leftCharacterization point, rightCharacterization point]
    constructor
    · rintro ⟨⟨inLeft, leftBounds⟩, inRight, rightBounds⟩
      refine ⟨⟨inLeft, inRight⟩, ?_⟩
      intro constraint member
      rcases List.mem_append.mp member with leftMember | rightMember
      · exact leftBounds constraint leftMember
      · exact rightBounds constraint rightMember
    · rintro ⟨⟨inLeft, inRight⟩, bounds⟩
      refine ⟨⟨inLeft, ?_⟩, inRight, ?_⟩
      · intro constraint member
        exact bounds constraint (List.mem_append.mpr (Or.inl member))
      · intro constraint member
        exact bounds constraint (List.mem_append.mpr (Or.inr member))

/-- Pulling analytic inequalities back through an analytic vector map preserves
an analytic set. The open domain is the preimage of the target domain within
the source domain. -/
public theorem analytic_set_preimage {source target : Nat}
    {sourceRegion : Set (Problib.Analysis.Real.FiniteVector.carrier source)}
    {points : Set (Problib.Analysis.Real.FiniteVector.carrier target)}
    {function : Problib.Analysis.Real.FiniteVector.carrier source →
      Problib.Analysis.Real.FiniteVector.carrier target}
    (sourceOpen : Problib.Analysis.Real.FiniteVector.IsOpen sourceRegion)
    (functionAnalytic : AnalyticVectorOn sourceRegion function)
    (pointsAnalytic : AnalyticSet points) :
    AnalyticSet (fun point => sourceRegion point ∧ points (function point)) := by
  rcases pointsAnalytic with ⟨targetRegion, constraints,
    targetOpen, constraintsAnalytic, characterization⟩
  let region : Set (Problib.Analysis.Real.FiniteVector.carrier source) :=
    fun point => sourceRegion point ∧ targetRegion (function point)
  have regionOpen := analytic_vector_preimage_open
    sourceOpen targetOpen functionAnalytic
  let pulled := constraints.map (fun constraint point => constraint (function point))
  refine ⟨region, pulled, regionOpen, ?_, ?_⟩
  · intro pulledConstraint member
    rcases List.mem_map.mp member with ⟨constraint, inConstraints, equal⟩
    subst pulledConstraint
    exact analytic_on_comp_preimage sourceOpen functionAnalytic
      (constraintsAnalytic constraint inConstraints)
  · intro point
    change (sourceRegion point ∧ points (function point)) ↔
      (region point ∧ ∀ constraint,
        constraint ∈ pulled → le (constraint point) zero)
    rw [characterization (function point)]
    constructor
    · rintro ⟨inSource, inTarget, bounds⟩
      refine ⟨⟨inSource, inTarget⟩, ?_⟩
      intro constraint member
      rcases List.mem_map.mp member with ⟨original, inConstraints, equal⟩
      subst constraint
      exact bounds original inConstraints
    · rintro ⟨⟨inSource, inTarget⟩, bounds⟩
      refine ⟨inSource, inTarget, ?_⟩
      intro constraint member
      exact bounds (fun point => constraint (function point))
        (List.mem_map.mpr ⟨constraint, member, rfl⟩)

end Problib.Analysis.PAP
