module

public import Problib.Analysis.PAP.Representation

set_option autoImplicit false

namespace Problib.Analysis.PAP

open Problib.Measure
open Problib.Analysis.Real.FiniteVector
open Problib.Analysis.Real.PowerSeries

/-- Concatenate finite vectors without changing either coordinate block. -/
@[expose] public def pairVector {left right : Nat}
    (first : carrier left) (second : carrier right) : carrier (left + right) :=
  fun coordinate => Fin.addCases (fun index => first index)
    (fun index => second index) coordinate

/-- Pair two PAP representations on their common domain. -/
public def PAPRepresentation.pair {source left right : Nat}
    {firstDomain secondDomain : Set (carrier source)}
    {firstFunction : carrier source → carrier left}
    {secondFunction : carrier source → carrier right}
    (first : PAPRepresentation firstDomain firstFunction)
    (second : PAPRepresentation secondDomain secondFunction) :
    PAPRepresentation (Set.inter firstDomain secondDomain)
      (fun point => pairVector (firstFunction point) (secondFunction point)) := by
  let pieces (index : Nat) : Set (carrier source) :=
    Set.inter (first.pieces (Problib.Countable.Pair.decode index).1)
      (second.pieces (Problib.Countable.Pair.decode index).2)
  let regions (index : Nat) : Set (carrier source) :=
    Set.inter (first.regions (Problib.Countable.Pair.decode index).1)
      (second.regions (Problib.Countable.Pair.decode index).2)
  let witnesses (index : Nat) (point : carrier source) : carrier (left + right) :=
    pairVector
      (first.witnesses (Problib.Countable.Pair.decode index).1 point)
      (second.witnesses (Problib.Countable.Pair.decode index).2 point)
  refine {
    pieces := pieces
    analytic := ?_
    pairwise := ?_
    cover := ?_
    regions := regions
    open_regions := ?_
    witnesses := witnesses
    analytic_witnesses := ?_
    pieces_in_regions := ?_
    agrees := ?_
  }
  · intro index
    exact analytic_set_inter (first.analytic _) (second.analytic _)
  · intro firstIndex secondIndex different point firstMember secondMember
    let firstPair := Problib.Countable.Pair.decode firstIndex
    let secondPair := Problib.Countable.Pair.decode secondIndex
    have pairDifferent : firstPair ≠ secondPair := by
      intro equal
      apply different
      have := congrArg Problib.Countable.Pair.encode equal
      simpa only [firstPair, secondPair,
        Problib.Countable.Pair.encode_decode] using this
    by_cases leftDifferent : firstPair.1 = secondPair.1
    · have rightDifferent : firstPair.2 ≠ secondPair.2 :=
        fun rightEqual => pairDifferent (Prod.ext leftDifferent rightEqual)
      exact second.pairwise firstPair.2 secondPair.2 rightDifferent
        firstMember.2 secondMember.2
    · exact first.pairwise firstPair.1 secondPair.1 leftDifferent
        firstMember.1 secondMember.1
  · apply Set.ext
    intro point
    rw [first.cover, second.cover]
    constructor
    · rintro ⟨⟨firstIndex, firstMember⟩, ⟨secondIndex, secondMember⟩⟩
      exact ⟨Problib.Countable.Pair.encode (firstIndex, secondIndex), by
        simpa only [pieces, Problib.Countable.Pair.decode_encode, Set.inter] using
          (show first.pieces firstIndex point ∧ second.pieces secondIndex point from
            ⟨firstMember, secondMember⟩)⟩
    · rintro ⟨index, member⟩
      exact ⟨⟨(Problib.Countable.Pair.decode index).1, member.1⟩,
        ⟨(Problib.Countable.Pair.decode index).2, member.2⟩⟩
  · intro index
    exact is_open_inter (first.open_regions _) (second.open_regions _)
  · intro index coordinate
    refine Fin.addCases ?_ ?_ coordinate
    · intro leftCoordinate
      simp only [witnesses, pairVector, Fin.addCases_left]
      change AnalyticOn
        (fun point => first.regions (Problib.Countable.Pair.decode index).1 point ∧
          second.regions (Problib.Countable.Pair.decode index).2 point)
        (fun point => first.witnesses
          (Problib.Countable.Pair.decode index).1 point leftCoordinate)
      exact analytic_on_open_subset
        (first.analytic_witnesses _ leftCoordinate)
        (is_open_inter (first.open_regions _) (second.open_regions _))
        (fun _ member => member.1)
    · intro rightCoordinate
      simp only [witnesses, pairVector, Fin.addCases_right]
      change AnalyticOn
        (fun point => first.regions (Problib.Countable.Pair.decode index).1 point ∧
          second.regions (Problib.Countable.Pair.decode index).2 point)
        (fun point => second.witnesses
          (Problib.Countable.Pair.decode index).2 point rightCoordinate)
      exact analytic_on_open_subset
        (second.analytic_witnesses _ rightCoordinate)
        (is_open_inter (first.open_regions _) (second.open_regions _))
        (fun _ member => member.2)
  · intro index point member
    exact ⟨first.pieces_in_regions _ member.1,
      second.pieces_in_regions _ member.2⟩
  · intro index point member
    change pairVector (firstFunction point) (secondFunction point) =
      pairVector
        (first.witnesses (Problib.Countable.Pair.decode index).1 point)
        (second.witnesses (Problib.Countable.Pair.decode index).2 point)
    rw [first.agrees _ point member.1, second.agrees _ point member.2]

/-- Pair partial maps, retaining only inputs on which both are defined. -/
public noncomputable def PartialPAP.pair {source left right : Nat}
    (first : PartialPAP source left) (second : PartialPAP source right) :
    PartialPAP source (left + right) := by
  let domain := Set.inter first.domain second.domain
  let values : {point : carrier source // domain point} → carrier (left + right) :=
    fun point => pairVector
      (first.values ⟨point.val, point.property.1⟩)
      (second.values ⟨point.val, point.property.2⟩)
  have domainAnalytic : CAnalytic domain :=
    c_analytic_inter first.c_analytic_domain second.c_analytic_domain
  have paired : PAPRepresentation domain
      (fun point => pairVector (first.totalize point) (second.totalize point)) :=
    first.representation.pair second.representation
  have same (point : carrier source) (member : domain point) :
      pairVector (first.totalize point) (second.totalize point) =
        totalizeValues domain values point := by
    classical
    simp only [totalizeValues, dif_pos member, values]
    rw [first.totalize_on_domain member.1,
      second.totalize_on_domain member.2]
  exact {
    domain := domain
    values := values
    c_analytic_domain := domainAnalytic
    representation := paired.congrOnDomain same
  }

/-- Postcomposition by a globally analytic vector map preserves the chosen
partition and transforms each local witness by analytic composition. -/
public def PAPRepresentation.postcompose {source middle target : Nat}
    {domain : Set (carrier source)}
    {function : carrier source → carrier middle}
    (representation : PAPRepresentation domain function)
    (after : carrier middle → carrier target)
    (afterAnalytic : AnalyticVectorOn (Set.univ : Set (carrier middle)) after) :
    PAPRepresentation domain (fun point => after (function point)) where
  pieces := representation.pieces
  analytic := representation.analytic
  pairwise := representation.pairwise
  cover := representation.cover
  regions := representation.regions
  open_regions := representation.open_regions
  witnesses := fun index point => after (representation.witnesses index point)
  analytic_witnesses := by
    intro index coordinate
    exact analytic_on_comp (representation.open_regions index)
      (representation.analytic_witnesses index)
      (afterAnalytic coordinate) (fun _ _ => True.intro)
  pieces_in_regions := representation.pieces_in_regions
  agrees := by
    intro index point member
    exact congrArg after (representation.agrees index point member)

/-- Apply a total analytic map to the values of a partial PAP map. -/
public noncomputable def PartialPAP.postcompose {source middle target : Nat}
    (map : PartialPAP source middle)
    (after : carrier middle → carrier target)
    (afterAnalytic : AnalyticVectorOn (Set.univ : Set (carrier middle)) after) :
    PartialPAP source target := by
  let values : {point : carrier source // map.domain point} → carrier target :=
    fun point => after (map.values point)
  have represented : PAPRepresentation map.domain
      (fun point => after (map.totalize point)) :=
    map.representation.postcompose after afterAnalytic
  have same (point : carrier source) (member : map.domain point) :
      after (map.totalize point) =
        totalizeValues map.domain values point := by
    classical
    simp only [totalizeValues, dif_pos member, values]
    rw [map.totalize_on_domain member]
  exact {
    domain := map.domain
    values := values
    c_analytic_domain := map.c_analytic_domain
    representation := represented.congrOnDomain same
  }

@[expose] public def leftVector {left right : Nat} :
    carrier (left + right) → carrier left :=
  fun vector coordinate => vector (Fin.castAdd right coordinate)

@[expose] public def rightVector {left right : Nat} :
    carrier (left + right) → carrier right :=
  fun vector coordinate => vector (Fin.natAdd left coordinate)

public theorem leftVector_analytic (left right : Nat) :
    AnalyticVectorOn (Set.univ : Set (carrier (left + right)))
      (leftVector (left := left) (right := right)) := by
  intro coordinate
  exact analytic_on_coordinate (is_open_univ (left + right))
    (Fin.castAdd right coordinate)

public theorem rightVector_analytic (left right : Nat) :
    AnalyticVectorOn (Set.univ : Set (carrier (left + right)))
      (rightVector (left := left) (right := right)) := by
  intro coordinate
  exact analytic_on_coordinate (is_open_univ (left + right))
    (Fin.natAdd left coordinate)

public noncomputable def PartialPAP.left {source left right : Nat}
    (map : PartialPAP source (left + right)) : PartialPAP source left :=
  map.postcompose (leftVector (left := left) (right := right))
    (leftVector_analytic left right)

public noncomputable def PartialPAP.right {source left right : Nat}
    (map : PartialPAP source (left + right)) : PartialPAP source right :=
  map.postcompose (rightVector (left := left) (right := right))
    (rightVector_analytic left right)

end Problib.Analysis.PAP
