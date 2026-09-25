module

public import Problib.Analysis.PAP.CAnalytic

set_option autoImplicit false

namespace Problib.Analysis.PAP

open Problib.Measure
open Problib.Analysis.Real.FiniteVector
open Problib.Analysis.Real.PowerSeries

/-- A chosen analytic partition and analytic vector witness for each piece.
The map is specified only by its agreement with witnesses on the domain. -/
public structure PAPRepresentation {source target : Nat}
    (domain : Set (carrier source))
    (function : carrier source → carrier target) where
  pieces : Nat → Set (carrier source)
  analytic : ∀ index, AnalyticSet (pieces index)
  pairwise : Set.PairwiseDisjoint pieces
  cover : domain = Set.iUnion pieces
  regions : Nat → Set (carrier source)
  open_regions : ∀ index, IsOpen (regions index)
  witnesses : Nat → carrier source → carrier target
  analytic_witnesses : ∀ index, AnalyticVectorOn (regions index) (witnesses index)
  pieces_in_regions : ∀ index, Set.Subset (pieces index) (regions index)
  agrees : ∀ index point, pieces index point →
    function point = witnesses index point

/-- Extend a domain-indexed map by zero for use in representation laws. -/
@[expose] public noncomputable def totalizeValues {source target : Nat}
    (domain : Set (carrier source))
    (values : {point : carrier source // domain point} → carrier target) :
    carrier source → carrier target := by
  classical
  exact fun point => if member : domain point then values ⟨point, member⟩
    else zeroVector target

/-- A partial map stores values on its domain, with a chosen PAP representation.
`totalize` below is only a derived convenience for stating the witness law. -/
public structure PartialPAP (source target : Nat) where
  domain : Set (carrier source)
  values : {point : carrier source // domain point} → carrier target
  c_analytic_domain : CAnalytic domain
  representation : PAPRepresentation domain (totalizeValues domain values)

namespace PartialPAP

/-- Derived total extension, zero outside the partial domain. -/
@[expose] public noncomputable def totalize {source target : Nat} (map : PartialPAP source target) :
    carrier source → carrier target :=
  totalizeValues map.domain map.values

public theorem totalize_on_domain {source target : Nat}
    (map : PartialPAP source target) {point : carrier source}
    (member : map.domain point) :
    map.totalize point = map.values ⟨point, member⟩ := by
  classical
  simp only [totalize, totalizeValues, dif_pos member]

end PartialPAP

/-- Pulling a c-analytic set back through a PAP map gives a c-analytic
subset of its domain. -/
public theorem pap_preimage_c_analytic {source target : Nat}
    {domain : Set (carrier source)}
    {function : carrier source → carrier target}
    (representation : PAPRepresentation domain function)
    {points : Set (carrier target)} (pointsAnalytic : CAnalytic points) :
    CAnalytic (fun point => domain point ∧ points (function point)) := by
  let pulled (index : Nat) : Set (carrier source) :=
    fun point => representation.pieces index point ∧ points (function point)
  have each (index : Nat) : CAnalytic (pulled index) := by
    let localPull : Set (carrier source) :=
      fun point => representation.regions index point ∧
        points (representation.witnesses index point)
    have localAnalytic : CAnalytic localPull :=
      c_analytic_preimage (representation.open_regions index)
        (representation.analytic_witnesses index) pointsAnalytic
    have intersectAnalytic := c_analytic_inter
      (c_analytic_of_analytic (representation.analytic index)) localAnalytic
    have equal : pulled index = Set.inter (representation.pieces index) localPull := by
      apply Set.ext
      intro point
      change (representation.pieces index point ∧ points (function point)) ↔
        representation.pieces index point ∧
          (representation.regions index point ∧
            points (representation.witnesses index point))
      constructor
      · rintro ⟨piece, belongs⟩
        exact ⟨piece, representation.pieces_in_regions index piece,
          (representation.agrees index point piece) ▸ belongs⟩
      · rintro ⟨piece, _, belongs⟩
        exact ⟨piece, (representation.agrees index point piece).symm ▸ belongs⟩
    rw [equal]
    exact intersectAnalytic
  have unionAnalytic := c_analytic_iUnion each
  have equal : (fun point => domain point ∧ points (function point)) =
      Set.iUnion pulled := by
    apply Set.ext
    intro point
    constructor
    · rintro ⟨inDomain, inPoints⟩
      rw [representation.cover] at inDomain
      rcases inDomain with ⟨index, inPiece⟩
      exact ⟨index, inPiece, inPoints⟩
    · rintro ⟨index, inPiece, inPoints⟩
      exact ⟨by rw [representation.cover]; exact ⟨index, inPiece⟩,
        inPoints⟩
  rw [equal]
  exact unionAnalytic

/-- Compose two chosen PAP representations. The pieces are indexed by Cantor
pairs, and each witness is an analytic composition on the pulled-back open
region. -/
public noncomputable def PAPRepresentation.comp {source middle target : Nat}
    {innerDomain : Set (carrier source)}
    {outerDomain : Set (carrier middle)}
    {innerFunction : carrier source → carrier middle}
    {outerFunction : carrier middle → carrier target}
    (inner : PAPRepresentation innerDomain innerFunction)
    (outer : PAPRepresentation outerDomain outerFunction) :
    PAPRepresentation
      (fun point => innerDomain point ∧ outerDomain (innerFunction point))
      (fun point => outerFunction (innerFunction point)) := by
  let pieces (index : Nat) : Set (carrier source) :=
    fun point => inner.pieces (Problib.Countable.Pair.decode index).1 point ∧
      outer.pieces (Problib.Countable.Pair.decode index).2 (innerFunction point)
  let regions (index : Nat) : Set (carrier source) :=
    fun point => inner.regions (Problib.Countable.Pair.decode index).1 point ∧
      outer.regions (Problib.Countable.Pair.decode index).2
        (inner.witnesses (Problib.Countable.Pair.decode index).1 point)
  let witnesses (index : Nat) (point : carrier source) : carrier target :=
    outer.witnesses (Problib.Countable.Pair.decode index).2
      (inner.witnesses (Problib.Countable.Pair.decode index).1 point)
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
    let first := (Problib.Countable.Pair.decode index).1
    let second := (Problib.Countable.Pair.decode index).2
    let pulled : Set (carrier source) := fun point =>
      inner.regions first point ∧ outer.pieces second (inner.witnesses first point)
    have pulledAnalytic : AnalyticSet pulled :=
      analytic_set_preimage (inner.open_regions first)
        (inner.analytic_witnesses first) (outer.analytic second)
    have intersectAnalytic := analytic_set_inter (inner.analytic first) pulledAnalytic
    have equal : pieces index = Set.inter (inner.pieces first) pulled := by
      apply Set.ext
      intro point
      change (inner.pieces first point ∧ outer.pieces second (innerFunction point)) ↔
        (inner.pieces first point ∧
          (inner.regions first point ∧
            outer.pieces second (inner.witnesses first point)))
      constructor
      · rintro ⟨inFirst, inSecond⟩
        exact ⟨inFirst, inner.pieces_in_regions first inFirst,
          (inner.agrees first point inFirst) ▸ inSecond⟩
      · rintro ⟨inFirst, _, inSecond⟩
        exact ⟨inFirst, (inner.agrees first point inFirst).symm ▸ inSecond⟩
    rw [equal]
    exact intersectAnalytic
  · intro first second different point inFirst inSecond
    let firstPair := Problib.Countable.Pair.decode first
    let secondPair := Problib.Countable.Pair.decode second
    have pairDifferent : firstPair ≠ secondPair := by
      intro equal
      apply different
      have := congrArg Problib.Countable.Pair.encode equal
      simpa only [firstPair, secondPair,
        Problib.Countable.Pair.encode_decode] using this
    have split : firstPair.1 ≠ secondPair.1 ∨ firstPair.2 ≠ secondPair.2 := by
      by_cases firstDifferent : firstPair.1 = secondPair.1
      · exact Or.inr (fun secondEqual => pairDifferent (Prod.ext firstDifferent secondEqual))
      · exact Or.inl firstDifferent
    rcases split with firstDifferent | secondDifferent
    · exact inner.pairwise firstPair.1 secondPair.1 firstDifferent inFirst.1 inSecond.1
    · exact outer.pairwise firstPair.2 secondPair.2 secondDifferent
        inFirst.2 inSecond.2
  · apply Set.ext
    intro point
    constructor
    · rintro ⟨inInner, inOuter⟩
      rw [inner.cover] at inInner
      rw [outer.cover] at inOuter
      rcases inInner with ⟨first, inFirst⟩
      rcases inOuter with ⟨second, inSecond⟩
      exact ⟨Problib.Countable.Pair.encode (first, second), by
        simpa only [pieces, Problib.Countable.Pair.decode_encode] using
          (show inner.pieces first point ∧
            outer.pieces second (innerFunction point) from ⟨inFirst, inSecond⟩)⟩
    · rintro ⟨index, inPiece⟩
      constructor
      · rw [inner.cover]
        exact ⟨(Problib.Countable.Pair.decode index).1, inPiece.1⟩
      · rw [outer.cover]
        exact ⟨(Problib.Countable.Pair.decode index).2, inPiece.2⟩
  · intro index
    exact analytic_vector_preimage_open
      (inner.open_regions _) (outer.open_regions _)
      (inner.analytic_witnesses _)
  · intro index coordinate
    exact analytic_on_comp_preimage
      (inner.open_regions _) (inner.analytic_witnesses _)
      (outer.analytic_witnesses _ coordinate)
  · intro index point member
    refine ⟨inner.pieces_in_regions _ member.1, ?_⟩
    exact (inner.agrees _ point member.1) ▸
      outer.pieces_in_regions _ member.2
  · intro index point member
    have innerEqual := inner.agrees _ point member.1
    have outerEqual := outer.agrees _ (innerFunction point) member.2
    change outerFunction (innerFunction point) =
      outer.witnesses (Problib.Countable.Pair.decode index).2
        (inner.witnesses (Problib.Countable.Pair.decode index).1 point)
    rw [outerEqual, innerEqual]

/-- Change a representation's total extension when the two functions agree
on its domain. -/
public def PAPRepresentation.congrOnDomain {source target : Nat}
    {domain : Set (carrier source)}
    {first second : carrier source → carrier target}
    (representation : PAPRepresentation domain first)
    (equal : ∀ point, domain point → first point = second point) :
    PAPRepresentation domain second where
  pieces := representation.pieces
  analytic := representation.analytic
  pairwise := representation.pairwise
  cover := representation.cover
  regions := representation.regions
  open_regions := representation.open_regions
  witnesses := representation.witnesses
  analytic_witnesses := representation.analytic_witnesses
  pieces_in_regions := representation.pieces_in_regions
  agrees := by
    intro index point member
    have inDomain : domain point := by
      rw [representation.cover]
      exact ⟨index, member⟩
    exact (equal point inDomain).symm.trans
      (representation.agrees index point member)

/-- Composition of partial PAP maps, with the outer map evaluated only where
the inner value lies in its domain. -/
public noncomputable def PartialPAP.comp {source middle target : Nat}
    (inner : PartialPAP source middle)
    (outer : PartialPAP middle target) : PartialPAP source target := by
  let domain : Set (carrier source) := fun point =>
    inner.domain point ∧ outer.domain (inner.totalize point)
  let values : {point : carrier source // domain point} → carrier target :=
    fun point => outer.values ⟨inner.totalize point.val, point.property.2⟩
  have domainAnalytic : CAnalytic domain :=
    pap_preimage_c_analytic inner.representation outer.c_analytic_domain
  have composed : PAPRepresentation domain
      (fun point => outer.totalize (inner.totalize point)) :=
    inner.representation.comp outer.representation
  have same (point : carrier source) (member : domain point) :
      (fun point => outer.totalize (inner.totalize point)) point =
        totalizeValues domain values point := by
    classical
    simp only [totalizeValues, dif_pos member, values]
    exact outer.totalize_on_domain member.2
  exact {
    domain := domain
    values := values
    c_analytic_domain := domainAnalytic
    representation := composed.congrOnDomain same
  }

end Problib.Analysis.PAP
