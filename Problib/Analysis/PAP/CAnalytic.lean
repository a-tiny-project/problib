module

public import Problib.Analysis.PAP.AnalyticSet
public import Problib.Countable.Bijection

set_option autoImplicit false

namespace Problib.Analysis.PAP

open Problib.Measure
open Problib.Analysis.Real.FiniteVector

/-- A countable union of analytic sets. -/
@[expose] public def CAnalytic {dimension : Nat}
    (points : Set (carrier dimension)) : Prop :=
  ∃ pieces : Nat → Set (carrier dimension),
    (∀ index, AnalyticSet (pieces index)) ∧ points = Set.iUnion pieces

public theorem c_analytic_of_analytic {dimension : Nat}
    {points : Set (carrier dimension)} (analytic : AnalyticSet points) :
    CAnalytic points := by
  let pieces : Nat → Set (carrier dimension) := fun index =>
    if index = 0 then points else Set.empty
  refine ⟨pieces, ?_, ?_⟩
  · intro index
    by_cases zero : index = 0
    · simp only [pieces, if_pos zero]
      exact analytic
    · simp only [pieces, if_neg zero]
      exact analytic_set_empty dimension
  · apply Set.ext
    intro point
    constructor
    · intro member
      exact ⟨0, (show pieces 0 point from member)⟩
    · rintro ⟨index, member⟩
      by_cases zero : index = 0
      · simpa only [pieces, if_pos zero] using member
      · have impossible : False := by
          simp only [pieces, if_neg zero, Set.empty] at member
        exact False.elim impossible

public theorem c_analytic_iUnion {dimension : Nat}
    {sets : Nat → Set (carrier dimension)}
    (analytic : ∀ index, CAnalytic (sets index)) :
    CAnalytic (Set.iUnion sets) := by
  classical
  let witnesses : ∀ index, ∃ pieces : Nat → Set (carrier dimension),
      (∀ piece, AnalyticSet (pieces piece)) ∧
        sets index = Set.iUnion pieces := analytic
  let pieces (index : Nat) := Classical.choose (witnesses index)
  have piecesAnalytic (index piece : Nat) : AnalyticSet (pieces index piece) :=
    (Classical.choose_spec (witnesses index)).1 piece
  have piecesCover (index : Nat) : sets index = Set.iUnion (pieces index) :=
    (Classical.choose_spec (witnesses index)).2
  let flattened (index : Nat) : Set (carrier dimension) :=
    pieces (Problib.Countable.Pair.decode index).1
      (Problib.Countable.Pair.decode index).2
  refine ⟨flattened, ?_, ?_⟩
  · intro index
    exact piecesAnalytic _ _
  · apply Set.ext
    intro point
    constructor
    · rintro ⟨index, member⟩
      rw [piecesCover index] at member
      rcases member with ⟨piece, inPiece⟩
      exact ⟨Problib.Countable.Pair.encode (index, piece), by
        simpa only [flattened, Problib.Countable.Pair.decode_encode] using inPiece⟩
    · rintro ⟨index, member⟩
      let pair := Problib.Countable.Pair.decode index
      exact ⟨pair.1, by
        rw [piecesCover pair.1]
        exact ⟨pair.2, member⟩⟩

public theorem c_analytic_inter {dimension : Nat}
    {left right : Set (carrier dimension)}
    (leftAnalytic : CAnalytic left) (rightAnalytic : CAnalytic right) :
    CAnalytic (Set.inter left right) := by
  rcases leftAnalytic with ⟨leftPieces, leftEach, leftCover⟩
  rcases rightAnalytic with ⟨rightPieces, rightEach, rightCover⟩
  let pieces (index : Nat) : Set (carrier dimension) :=
    Set.inter (leftPieces (Problib.Countable.Pair.decode index).1)
      (rightPieces (Problib.Countable.Pair.decode index).2)
  refine ⟨pieces, ?_, ?_⟩
  · intro index
    exact analytic_set_inter (leftEach _) (rightEach _)
  · apply Set.ext
    intro point
    rw [leftCover, rightCover]
    constructor
    · rintro ⟨⟨leftIndex, inLeft⟩, ⟨rightIndex, inRight⟩⟩
      exact ⟨Problib.Countable.Pair.encode (leftIndex, rightIndex), by
        simpa only [pieces, Problib.Countable.Pair.decode_encode, Set.inter] using
          (show leftPieces leftIndex point ∧ rightPieces rightIndex point from
            ⟨inLeft, inRight⟩)⟩
    · rintro ⟨index, member⟩
      exact ⟨⟨(Problib.Countable.Pair.decode index).1, member.1⟩,
        ⟨(Problib.Countable.Pair.decode index).2, member.2⟩⟩

public theorem c_analytic_preimage {source target : Nat}
    {sourceRegion : Set (carrier source)} {points : Set (carrier target)}
    {function : carrier source → carrier target}
    (sourceOpen : IsOpen sourceRegion)
    (functionAnalytic : Problib.Analysis.Real.PowerSeries.AnalyticVectorOn
      sourceRegion function)
    (pointsAnalytic : CAnalytic points) :
    CAnalytic (fun point => sourceRegion point ∧ points (function point)) := by
  rcases pointsAnalytic with ⟨pieces, eachAnalytic, cover⟩
  let pulled (index : Nat) : Set (carrier source) :=
    fun point => sourceRegion point ∧ pieces index (function point)
  refine ⟨pulled, fun index =>
    analytic_set_preimage sourceOpen functionAnalytic (eachAnalytic index), ?_⟩
  apply Set.ext
  intro point
  change (sourceRegion point ∧ points (function point)) ↔
    ∃ index, sourceRegion point ∧ pieces index (function point)
  rw [cover]
  constructor
  · rintro ⟨inSource, index, inPiece⟩
    exact ⟨index, inSource, inPiece⟩
  · rintro ⟨index, inSource, inPiece⟩
    exact ⟨inSource, index, inPiece⟩

end Problib.Analysis.PAP
