module

public import Problib.Analysis.PAP.Disjoint

set_option autoImplicit false

namespace Problib.Analysis.PAP

open Problib.Measure
open Problib.Analysis.Real.FiniteVector
open Problib.Analysis.Real.PowerSeries

/-- Restrict a chosen representation to a c-analytic set by intersecting its
pieces with a disjoint analytic refinement of the set. -/
public noncomputable def PAPRepresentation.restrict {source target : Nat}
    {domain : Set (carrier source)}
    {function : carrier source → carrier target}
    (representation : PAPRepresentation domain function)
    {subset : Set (carrier source)} (subsetAnalytic : CAnalytic subset) :
    PAPRepresentation (Set.inter domain subset) function := by
  classical
  let refinement := Classical.choose (c_analytic_disjoint_refinement subsetAnalytic)
  rcases Classical.choose_spec (c_analytic_disjoint_refinement subsetAnalytic) with
    ⟨refinementAnalytic, refinementPairwise, refinementCover⟩
  let pieces (code : Nat) : Set (carrier source) :=
    Set.inter
      (representation.pieces (Problib.Countable.Pair.decode code).1)
      (refinement (Problib.Countable.Pair.decode code).2)
  let regions (code : Nat) : Set (carrier source) :=
    representation.regions (Problib.Countable.Pair.decode code).1
  let witnesses (code : Nat) : carrier source → carrier target :=
    representation.witnesses (Problib.Countable.Pair.decode code).1
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
  · intro code
    exact analytic_set_inter (representation.analytic _)
      (refinementAnalytic _)
  · intro first second different point inFirst inSecond
    let firstPair := Problib.Countable.Pair.decode first
    let secondPair := Problib.Countable.Pair.decode second
    have pairsDifferent : firstPair ≠ secondPair := by
      intro equal
      apply different
      have := congrArg Problib.Countable.Pair.encode equal
      simpa only [firstPair, secondPair,
        Problib.Countable.Pair.encode_decode] using this
    by_cases firstDifferent : firstPair.1 = secondPair.1
    · have secondDifferent : firstPair.2 ≠ secondPair.2 :=
        fun same => pairsDifferent (Prod.ext firstDifferent same)
      exact refinementPairwise firstPair.2 secondPair.2 secondDifferent
        inFirst.2 inSecond.2
    · exact representation.pairwise firstPair.1 secondPair.1
        firstDifferent inFirst.1 inSecond.1
  · apply Set.ext
    intro point
    rw [representation.cover, refinementCover]
    constructor
    · rintro ⟨⟨first, inFirst⟩, ⟨second, inSecond⟩⟩
      exact ⟨Problib.Countable.Pair.encode (first, second), by
        simpa only [pieces, Problib.Countable.Pair.decode_encode, Set.inter]
          using (show representation.pieces first point ∧ refinement second point
            from ⟨inFirst, inSecond⟩)⟩
    · rintro ⟨code, inPiece⟩
      exact ⟨⟨(Problib.Countable.Pair.decode code).1, inPiece.1⟩,
        ⟨(Problib.Countable.Pair.decode code).2, inPiece.2⟩⟩
  · intro code
    exact representation.open_regions _
  · intro code
    exact representation.analytic_witnesses _
  · intro code point member
    exact representation.pieces_in_regions _ member.1
  · intro code point member
    exact representation.agrees _ point member.1

/-- Restrict a partial PAP map to any c-analytic subset of its source. -/
public noncomputable def PartialPAP.restrict {source target : Nat}
    (map : PartialPAP source target)
    {subset : Set (carrier source)} (subsetAnalytic : CAnalytic subset) :
    PartialPAP source target := by
  let domain := Set.inter map.domain subset
  let values : {point : carrier source // domain point} → carrier target :=
    fun point => map.values ⟨point.val, point.property.1⟩
  have domainAnalytic := c_analytic_inter map.c_analytic_domain subsetAnalytic
  have represented : PAPRepresentation domain map.totalize :=
    map.representation.restrict subsetAnalytic
  have same (point : carrier source) (member : domain point) :
      map.totalize point = totalizeValues domain values point := by
    classical
    simp only [totalizeValues, dif_pos member, values]
    exact map.totalize_on_domain member.1
  exact {
    domain := domain
    values := values
    c_analytic_domain := domainAnalytic
    representation := represented.congrOnDomain same
  }

/-- Inclusion of a c-analytic subset is a partial PAP identity map. -/
public noncomputable def PartialPAP.inclusion {dimension : Nat}
    {subset : Set (carrier dimension)} (subsetAnalytic : CAnalytic subset) :
    PartialPAP dimension dimension := by
  classical
  let pieces := Classical.choose (c_analytic_disjoint_refinement subsetAnalytic)
  rcases Classical.choose_spec (c_analytic_disjoint_refinement subsetAnalytic) with
    ⟨eachAnalytic, pairwise, cover⟩
  let values : {point : carrier dimension // subset point} → carrier dimension :=
    fun point => point.val
  have represented : PAPRepresentation subset (totalizeValues subset values) := by
    refine {
      pieces := pieces
      analytic := eachAnalytic
      pairwise := pairwise
      cover := cover
      regions := fun _ => Set.univ
      open_regions := fun _ => is_open_univ dimension
      witnesses := fun _ point => point
      analytic_witnesses := ?_
      pieces_in_regions := ?_
      agrees := ?_
    }
    · intro index coordinate
      exact analytic_on_coordinate (is_open_univ dimension) coordinate
    · intro index point member
      exact True.intro
    · intro index point member
      have inSubset : subset point := by
        rw [cover]
        exact ⟨index, member⟩
      simp only [totalizeValues, dif_pos inSubset, values]
  exact {
    domain := subset
    values := values
    c_analytic_domain := subsetAnalytic
    representation := represented
  }

end Problib.Analysis.PAP
