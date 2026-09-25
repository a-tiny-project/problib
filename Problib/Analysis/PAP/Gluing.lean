module

public import Problib.Analysis.PAP.Restriction

set_option autoImplicit false

namespace Problib.Analysis.PAP

open Problib.Measure
open Problib.Analysis.Real.FiniteVector

/-- Glue PAP representations over pairwise-disjoint domains. Each local
representation retains its analytic witnesses; Cantor pairing flattens the
domain and piece indices. -/
public def PAPRepresentation.glue {source target : Nat}
    {domains : Nat → Set (carrier source)}
    {functions : Nat → carrier source → carrier target}
    (representations : ∀ index,
      PAPRepresentation (domains index) (functions index))
    (domainsPairwise : Set.PairwiseDisjoint domains)
    (glued : carrier source → carrier target)
    (gluedAgrees : ∀ index point, domains index point →
      glued point = functions index point) :
    PAPRepresentation (Set.iUnion domains) glued := by
  let pieces (code : Nat) : Set (carrier source) :=
    (representations (Problib.Countable.Pair.decode code).1).pieces
      (Problib.Countable.Pair.decode code).2
  let regions (code : Nat) : Set (carrier source) :=
    (representations (Problib.Countable.Pair.decode code).1).regions
      (Problib.Countable.Pair.decode code).2
  let witnesses (code : Nat) : carrier source → carrier target :=
    (representations (Problib.Countable.Pair.decode code).1).witnesses
      (Problib.Countable.Pair.decode code).2
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
    exact (representations _).analytic _
  · intro first second different point inFirst inSecond
    let firstPair := Problib.Countable.Pair.decode first
    let secondPair := Problib.Countable.Pair.decode second
    have pairsDifferent : firstPair ≠ secondPair := by
      intro equal
      apply different
      have := congrArg Problib.Countable.Pair.encode equal
      simpa only [firstPair, secondPair,
        Problib.Countable.Pair.encode_decode] using this
    by_cases firstIndexEqual : firstPair.1 = secondPair.1
    · have secondIndexDifferent : firstPair.2 ≠ secondPair.2 :=
        fun same => pairsDifferent (Prod.ext firstIndexEqual same)
      have samePieces : (representations firstPair.1).pieces =
          (representations secondPair.1).pieces :=
        congrArg (fun index => (representations index).pieces) firstIndexEqual
      have secondMember :
          (representations firstPair.1).pieces secondPair.2 point := by
        rw [samePieces]
        exact inSecond
      exact (representations firstPair.1).pairwise
        firstPair.2 secondPair.2 secondIndexDifferent
        inFirst secondMember
    · have inFirstDomain : domains firstPair.1 point := by
        rw [(representations firstPair.1).cover]
        exact ⟨firstPair.2, inFirst⟩
      have inSecondDomain : domains secondPair.1 point := by
        rw [(representations secondPair.1).cover]
        exact ⟨secondPair.2, inSecond⟩
      exact domainsPairwise firstPair.1 secondPair.1 firstIndexEqual
        inFirstDomain inSecondDomain
  · apply Set.ext
    intro point
    constructor
    · rintro ⟨index, inDomain⟩
      rw [(representations index).cover] at inDomain
      rcases inDomain with ⟨piece, inPiece⟩
      exact ⟨Problib.Countable.Pair.encode (index, piece), by
        change (representations
          (Problib.Countable.Pair.decode
            (Problib.Countable.Pair.encode (index, piece))).1).pieces
          (Problib.Countable.Pair.decode
            (Problib.Countable.Pair.encode (index, piece))).2 point
        rw [Problib.Countable.Pair.decode_encode]
        exact inPiece⟩
    · rintro ⟨code, inPiece⟩
      let pair := Problib.Countable.Pair.decode code
      refine ⟨pair.1, ?_⟩
      rw [(representations pair.1).cover]
      exact ⟨pair.2, inPiece⟩
  · intro code
    exact (representations _).open_regions _
  · intro code
    exact (representations _).analytic_witnesses _
  · intro code point member
    exact (representations _).pieces_in_regions _ member
  · intro code point member
    let pair := Problib.Countable.Pair.decode code
    have inDomain : domains pair.1 point := by
      rw [(representations pair.1).cover]
      exact ⟨pair.2, member⟩
    exact (gluedAgrees pair.1 point inDomain).trans
      ((representations pair.1).agrees pair.2 point member)

/-- Countable gluing of partial PAP maps over disjoint c-analytic domains. -/
public noncomputable def PartialPAP.glue {source target : Nat}
    (maps : Nat → PartialPAP source target)
    (domainsPairwise : Set.PairwiseDisjoint (fun index => (maps index).domain)) :
    PartialPAP source target := by
  classical
  let domains : Nat → Set (carrier source) := fun index => (maps index).domain
  let domain := Set.iUnion domains
  let selected (point : carrier source) (member : domain point) : Nat :=
    Classical.choose member
  have selectedMember (point : carrier source) (member : domain point) :
      (maps (selected point member)).domain point :=
    Classical.choose_spec member
  let values : {point : carrier source // domain point} → carrier target :=
    fun point => (maps (selected point.val point.property)).values
      ⟨point.val, selectedMember point.val point.property⟩
  have domainAnalytic : CAnalytic domain :=
    c_analytic_iUnion (fun index => (maps index).c_analytic_domain)
  have eachAgrees (index : Nat) (point : carrier source)
      (member : domains index point) :
      totalizeValues domain values point = (maps index).totalize point := by
    have inUnion : domain point := ⟨index, member⟩
    have selectedEqual : selected point inUnion = index := by
      by_cases equal : selected point inUnion = index
      · exact equal
      · have chosenMember := selectedMember point inUnion
        exact False.elim (domainsPairwise _ _ equal chosenMember member)
    simp only [totalizeValues, dif_pos inUnion, values]
    change (maps (selected point inUnion)).values
      ⟨point, selectedMember point inUnion⟩ = (maps index).totalize point
    cases selectedEqual
    exact ((maps (selected point inUnion)).totalize_on_domain
      (selectedMember point inUnion)).symm
  have represented : PAPRepresentation domain (totalizeValues domain values) :=
    PAPRepresentation.glue (fun index => (maps index).representation)
      domainsPairwise (totalizeValues domain values) eachAgrees
  exact {
    domain := domain
    values := values
    c_analytic_domain := domainAnalytic
    representation := represented
  }

end Problib.Analysis.PAP
