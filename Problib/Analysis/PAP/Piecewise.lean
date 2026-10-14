module

public import Problib.Analysis.PAP.Representation

/-! PAP maps with one or two analytic pieces.

A scalar operation is usually analytic on its whole domain, or analytic on
each side of one analytic cut. These constructors build its representation
from the named pieces directly, with no disjoint refinement, so each piece a
theorem names is a piece of the representation.
-/

set_option autoImplicit false

namespace Problib.Analysis.PAP

open Problib.Measure
open Problib.Analysis.Real.FiniteVector
open Problib.Analysis.Real.PowerSeries

public theorem analytic_set_congr {dimension : Nat}
    {first second : Set (carrier dimension)}
    (same : ∀ point, first point ↔ second point)
    (analytic : AnalyticSet first) : AnalyticSet second := by
  have equal : first = second := funext fun point => propext (same point)
  exact equal ▸ analytic

public theorem c_analytic_congr {dimension : Nat}
    {first second : Set (carrier dimension)}
    (same : ∀ point, first point ↔ second point)
    (analytic : CAnalytic first) : CAnalytic second := by
  have equal : first = second := funext fun point => propext (same point)
  exact equal ▸ analytic

/-- Two named sets, then nothing. -/
@[expose] public def twoSets {α : Type} (first second : Set α) : Nat → Set α
  | 0 => first
  | 1 => second
  | _ + 2 => Set.empty

/-- Two named values, then the first again. -/
@[expose] public def twoValues {α : Type} (first second : α) : Nat → α
  | 1 => second
  | _ => first

/-- A representation from two disjoint analytic pieces covering the domain,
each with an analytic witness on an open neighborhood. -/
public def PAPRepresentation.split {source target : Nat}
    {domain first second firstRegion secondRegion : Set (carrier source)}
    {function firstWitness secondWitness : carrier source → carrier target}
    (firstAnalytic : AnalyticSet first) (secondAnalytic : AnalyticSet second)
    (disjoint : Set.Disjoint first second)
    (cover : ∀ point, domain point ↔ first point ∨ second point)
    (firstOpen : IsOpen firstRegion) (secondOpen : IsOpen secondRegion)
    (firstInside : Set.Subset first firstRegion)
    (secondInside : Set.Subset second secondRegion)
    (firstWitnessAnalytic : AnalyticVectorOn firstRegion firstWitness)
    (secondWitnessAnalytic : AnalyticVectorOn secondRegion secondWitness)
    (firstAgrees : ∀ point, first point → function point = firstWitness point)
    (secondAgrees : ∀ point, second point →
      function point = secondWitness point) :
    PAPRepresentation domain function where
  pieces := twoSets first second
  analytic := fun
    | 0 => firstAnalytic
    | 1 => secondAnalytic
    | _ + 2 => analytic_set_empty source
  pairwise := by
    intro left right different point inLeft inRight
    match left, right, inLeft, inRight with
    | 0, 1, inLeft, inRight => exact disjoint inLeft inRight
    | 1, 0, inLeft, inRight => exact disjoint inRight inLeft
    | 0, 0, _, _ => exact different rfl
    | 1, 1, _, _ => exact different rfl
    | _ + 2, _, inLeft, _ => exact inLeft
    | 0, _ + 2, _, inRight => exact inRight
    | 1, _ + 2, _, inRight => exact inRight
  cover := by
    funext point
    apply propext
    rw [cover point]
    constructor
    · rintro (inFirst | inSecond)
      · exact ⟨0, inFirst⟩
      · exact ⟨1, inSecond⟩
    · rintro ⟨index, member⟩
      match index, member with
      | 0, member => exact Or.inl member
      | 1, member => exact Or.inr member
      | _ + 2, member => exact False.elim member
  regions := twoValues firstRegion secondRegion
  open_regions := fun
    | 1 => secondOpen
    | 0 => firstOpen
    | _ + 2 => firstOpen
  witnesses := twoValues firstWitness secondWitness
  analytic_witnesses := fun
    | 1 => secondWitnessAnalytic
    | 0 => firstWitnessAnalytic
    | _ + 2 => firstWitnessAnalytic
  pieces_in_regions := fun
    | 0 => firstInside
    | 1 => secondInside
    | _ + 2 => fun _ member => False.elim member
  agrees := fun
    | 0 => firstAgrees
    | 1 => secondAgrees
    | _ + 2 => fun _ member => False.elim member

/-- A representation from one analytic piece with one analytic witness on an
open neighborhood. -/
public def PAPRepresentation.single {source target : Nat}
    {domain region : Set (carrier source)}
    {function witness : carrier source → carrier target}
    (domainAnalytic : AnalyticSet domain) (regionOpen : IsOpen region)
    (inside : Set.Subset domain region)
    (witnessAnalytic : AnalyticVectorOn region witness)
    (agrees : ∀ point, domain point → function point = witness point) :
    PAPRepresentation domain function :=
  PAPRepresentation.split domainAnalytic (analytic_set_empty source)
    (fun _ _ member => member)
    (fun _ => ⟨Or.inl, fun either => either.elim id False.elim⟩)
    regionOpen regionOpen inside (fun _ member => False.elim member)
    witnessAnalytic witnessAnalytic agrees
    (fun _ member => False.elim member)

/-- A partial map from its values on a c-analytic domain and a representation
of any total map that agrees with them there. -/
@[expose] public noncomputable def PartialPAP.ofRepresentation
    {source target : Nat} {domain : Set (carrier source)}
    {function : carrier source → carrier target}
    (domainAnalytic : CAnalytic domain)
    (values : {point : carrier source // domain point} → carrier target)
    (representation : PAPRepresentation domain function)
    (agrees : ∀ point, values point = function point.val) :
    PartialPAP source target where
  domain := domain
  values := values
  c_analytic_domain := domainAnalytic
  representation := representation.congrOnDomain (by
    intro point member
    classical
    simp only [totalizeValues, dite_eq_left member]
    exact (agrees ⟨point, member⟩).symm)


/-- A total analytic map, as a partial PAP map defined everywhere. -/
@[expose] public noncomputable def PartialPAP.ofAnalytic {source target : Nat}
    (function : carrier source → carrier target)
    (analytic : AnalyticVectorOn (Set.univ : Set (carrier source)) function) :
    PartialPAP source target :=
  PartialPAP.ofRepresentation (c_analytic_of_analytic (analytic_set_univ source))
    (fun point => function point.val)
    (PAPRepresentation.single (analytic_set_univ source) (is_open_univ source)
      (fun _ member => member) analytic (fun _ _ => rfl))
    (fun _ => rfl)

public theorem PartialPAP.ofAnalytic_domain {source target : Nat}
    (function : carrier source → carrier target)
    (analytic : AnalyticVectorOn (Set.univ : Set (carrier source)) function)
    (point : carrier source) : (PartialPAP.ofAnalytic function analytic).domain point :=
  True.intro

public theorem PartialPAP.ofAnalytic_totalize {source target : Nat}
    (function : carrier source → carrier target)
    (analytic : AnalyticVectorOn (Set.univ : Set (carrier source)) function)
    (point : carrier source) :
    (PartialPAP.ofAnalytic function analytic).totalize point = function point :=
  PartialPAP.totalize_on_domain _ True.intro

end Problib.Analysis.PAP
