module

public import Problib.Analysis.PAP.Boxes
public import Problib.Analysis.PAP.Measurable

set_option autoImplicit false

namespace Problib.Analysis.PAP

open Problib.Measure
open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real.FiniteVector
open Problib.Analysis.Real.PowerSeries

@[expose] public def listUnion {α : Type}
    (pieces : List (Set α)) : Set α :=
  fun point => ∃ piece, piece ∈ pieces ∧ piece point

public theorem listUnion_cons {α : Type} (head : Set α)
    (tail : List (Set α)) (point : α) :
    listUnion (head :: tail) point ↔ head point ∨ listUnion tail point := by
  constructor
  · rintro ⟨piece, member, inside⟩
    rcases List.mem_cons.mp member with equal | inTail
    · subst piece
      exact Or.inl inside
    · exact Or.inr ⟨piece, inTail, inside⟩
  · intro member
    rcases member with inside | ⟨piece, inTail, inside⟩
    · exact ⟨head, List.mem_cons_self, inside⟩
    · exact ⟨piece, List.mem_cons_of_mem head inTail, inside⟩

public theorem listUnion_map_inter {α : Type}
    (guard : Set α) (pieces : List (Set α)) (point : α) :
    listUnion (pieces.map (Set.inter guard)) point ↔
      guard point ∧ listUnion pieces point := by
  constructor
  · rintro ⟨piece, member, inside⟩
    rcases List.mem_map.mp member with ⟨original, originalMember, equal⟩
    subst piece
    exact ⟨inside.1, original, originalMember, inside.2⟩
  · rintro ⟨inGuard, original, originalMember, inside⟩
    exact ⟨Set.inter guard original,
      List.mem_map.mpr ⟨original, originalMember, rfl⟩,
      inGuard, inside⟩

public theorem listUnion_append {α : Type}
    (first second : List (Set α)) (point : α) :
    listUnion (first ++ second) point ↔
      listUnion first point ∨ listUnion second point := by
  constructor
  · rintro ⟨piece, member, inside⟩
    rcases List.mem_append.mp member with inFirst | inSecond
    · exact Or.inl ⟨piece, inFirst, inside⟩
    · exact Or.inr ⟨piece, inSecond, inside⟩
  · intro member
    rcases member with ⟨piece, inFirst, inside⟩ | ⟨piece, inSecond, inside⟩
    · exact ⟨piece, List.mem_append.mpr (Or.inl inFirst), inside⟩
    · exact ⟨piece, List.mem_append.mpr (Or.inr inSecond), inside⟩

/-- First failed analytic inequality, in list order. The first case fails
the head inequality; later cases satisfy it before failing a later one. -/
@[expose] public def failureCases {dimension : Nat}
    (region : Set (carrier dimension)) :
    List (carrier dimension → selection.Carrier) →
      List (Set (carrier dimension))
  | [] => []
  | constraint :: rest =>
      (fun point => region point ∧ lt zero (constraint point)) ::
        (failureCases region rest).map
          (Set.inter (fun point => region point ∧
            le (constraint point) zero))

public theorem failureCases_analytic {dimension : Nat}
    {region : Set (carrier dimension)}
    (constraints : List (carrier dimension → selection.Carrier))
    (analytic : ∀ constraint, constraint ∈ constraints →
      AnalyticOn region constraint) :
    ∀ piece, piece ∈ failureCases region constraints → AnalyticSet piece := by
  induction constraints with
  | nil =>
      intro piece member
      exact False.elim (List.not_mem_nil member)
  | cons head rest induction =>
      intro piece member
      rcases List.mem_cons.mp member with headEqual | inTail
      · subst piece
        exact analytic_set_open
          (analytic_superlevel_open (analytic head List.mem_cons_self) zero)
      · rcases List.mem_map.mp inTail with ⟨original, inRest, equal⟩
        subst piece
        exact analytic_set_inter
          (analytic_set_sublevel (analytic head List.mem_cons_self))
          (induction (fun constraint inRest =>
            analytic constraint (List.mem_cons_of_mem head inRest))
            original inRest)

/-- The first-failure cases partition exactly the failed constraints, within
their common open domain. -/
public theorem failureCases_cover {dimension : Nat}
    (region : Set (carrier dimension))
    (constraints : List (carrier dimension → selection.Carrier))
    (point : carrier dimension) :
    listUnion (failureCases region constraints) point ↔
      region point ∧ ¬∀ constraint, constraint ∈ constraints →
        le (constraint point) zero := by
  induction constraints with
  | nil =>
      constructor
      · rintro ⟨piece, member, _⟩
        exact False.elim (List.not_mem_nil member)
      · rintro ⟨_, fails⟩
        exact False.elim (fails (fun constraint impossible =>
          False.elim (List.not_mem_nil impossible)))
  | cons head rest induction =>
      rw [failureCases, listUnion_cons,
        listUnion_map_inter, induction]
      constructor
      · intro member
        rcases member with failedHead | ⟨satisfiedHead, failedRest⟩
        · refine ⟨failedHead.1, ?_⟩
          intro all
          exact failedHead.2.2 (all head List.mem_cons_self)
        · refine ⟨satisfiedHead.1, ?_⟩
          intro all
          apply failedRest.2
          intro constraint inRest
          exact all constraint (List.mem_cons_of_mem head inRest)
      · rintro ⟨inRegion, fails⟩
        by_cases nonpositive : le (head point) zero
        · right
          refine ⟨⟨inRegion, nonpositive⟩, inRegion, ?_⟩
          intro allRest
          apply fails
          intro constraint member
          rcases List.mem_cons.mp member with equal | inRest
          · subst constraint
            exact nonpositive
          · exact allRest constraint inRest
        · left
          exact ⟨inRegion, lt_of_not_le nonpositive⟩

public theorem failureCases_pairwise {dimension : Nat}
    {region : Set (carrier dimension)}
    (constraints : List (carrier dimension → selection.Carrier)) :
    List.Pairwise Set.Disjoint (failureCases region constraints) := by
  induction constraints with
  | nil => exact List.Pairwise.nil
  | cons head rest induction =>
      apply List.Pairwise.cons
      · intro piece member point inHead inPiece
        rcases List.mem_map.mp member with ⟨original, _, equal⟩
        subst piece
        exact inHead.2.2 inPiece.1.2
      · apply List.Pairwise.map (R := Set.Disjoint) (S := Set.Disjoint)
          (fun piece => Set.inter
            (fun point => region point ∧ le (head point) zero) piece)
        · intro first second disjoint point firstMember secondMember
          exact disjoint firstMember.2 secondMember.2
        · exact induction

/-- The complement of a boxed analytic piece has a finite disjoint analytic
partition: first failed box face, then first failed local inequality. -/
public theorem boxed_complement_partition {dimension : Nat}
    {points : Set (carrier dimension)}
    (boxed : BoxedAnalytic points) :
    ∃ pieces : List (Set (carrier dimension)),
      (∀ piece, piece ∈ pieces → AnalyticSet piece) ∧
      List.Pairwise Set.Disjoint pieces ∧
      ∀ point, listUnion pieces point ↔ ¬points point := by
  by_cases active : boxed.active
  · let box := closedBox boxed.lower boxed.upper
    let exterior := failureCases (Set.univ : Set (carrier dimension))
      (boxConstraints boxed.lower boxed.upper)
    let interior := (failureCases boxed.region boxed.constraints).map
      (Set.inter box)
    refine ⟨exterior ++ interior, ?_, ?_, ?_⟩
    · intro piece member
      rcases List.mem_append.mp member with outside | inside
      · exact failureCases_analytic _
          (boxConstraints_analytic boxed.lower boxed.upper) piece outside
      · rcases List.mem_map.mp inside with ⟨original, originalMember, equal⟩
        subst piece
        exact analytic_set_inter
          (closedBox_analytic boxed.lower boxed.upper)
          (failureCases_analytic _ boxed.analytic_constraints
            original originalMember)
    · apply List.pairwise_append.mpr
      refine ⟨failureCases_pairwise _, ?_, ?_⟩
      · apply List.Pairwise.map (R := Set.Disjoint) (S := Set.Disjoint)
            (Set.inter box)
        · intro first second disjoint point firstMember secondMember
          exact disjoint firstMember.2 secondMember.2
        · exact failureCases_pairwise _
      · intro first firstMember second secondMember point inFirst inSecond
        have outside := (failureCases_cover Set.univ
          (boxConstraints boxed.lower boxed.upper) point).mp
            ⟨first, firstMember, inFirst⟩
        rcases List.mem_map.mp secondMember with
          ⟨original, _, equal⟩
        subst second
        have insideBox : box point := inSecond.1
        exact outside.2
          ((boxConstraints_character boxed.lower boxed.upper point).mp
            insideBox)
    · intro point
      rw [listUnion_append, failureCases_cover,
        listUnion_map_inter, failureCases_cover]
      change
        ((True ∧ ¬∀ constraint,
            constraint ∈ boxConstraints boxed.lower boxed.upper →
              le (constraint point) zero) ∨
          (box point ∧ boxed.region point ∧
            ¬∀ constraint, constraint ∈ boxed.constraints →
              le (constraint point) zero)) ↔ ¬points point
      rw [boxed.character point]
      constructor
      · intro case
        rcases case with outside | inside
        · intro member
          exact outside.2
            ((boxConstraints_character boxed.lower boxed.upper point).mp
              member.2.1)
        · intro member
          exact inside.2.2 member.2.2
      · intro outside
        by_cases inBox : box point
        · right
          refine ⟨inBox, boxed.box_inside active inBox, ?_⟩
          intro all
          exact outside ⟨active, inBox, all⟩
        · left
          exact ⟨True.intro, fun all => inBox
            ((boxConstraints_character boxed.lower boxed.upper point).mpr
              all)⟩
  · refine ⟨[Set.univ], ?_, ?_, ?_⟩
    · intro piece member
      have equal : piece = Set.univ := by
        simpa only [List.mem_singleton] using member
      subst piece
      exact analytic_set_univ dimension
    · exact List.pairwise_singleton _ _
    · intro point
      constructor
      · intro _ member
        exact active ((boxed.character point).mp member).1
      · intro _
        exact ⟨Set.univ, List.mem_singleton.mpr rfl, True.intro⟩

/-- A finite disjoint partition of a set into analytic pieces. -/
public structure FiniteAnalyticPartition {dimension : Nat}
    (target : Set (carrier dimension)) where
  pieces : List (Set (carrier dimension))
  analytic : ∀ piece, piece ∈ pieces → AnalyticSet piece
  pairwise : List.Pairwise Set.Disjoint pieces
  cover : ∀ point, listUnion pieces point ↔ target point

public def partitionSingle {dimension : Nat}
    {target : Set (carrier dimension)} (analytic : AnalyticSet target) :
    FiniteAnalyticPartition target where
  pieces := [target]
  analytic := by
    intro piece member
    have equal : piece = target := by
      simpa only [List.mem_singleton] using member
    subst piece
    exact analytic
  pairwise := List.pairwise_singleton _ _
  cover := by
    intro point
    constructor
    · rintro ⟨piece, member, inside⟩
      have equal : piece = target := by
        simpa only [List.mem_singleton] using member
      exact equal ▸ inside
    · intro inside
      exact ⟨target, List.mem_singleton.mpr rfl, inside⟩

/-- Subtract a boxed analytic set from one analytic set. The complement
partition makes the resulting pieces disjoint without a recursive choice of
overlapping c-analytic witnesses. -/
public noncomputable def partitionDifference {dimension : Nat}
    {target removed : Set (carrier dimension)}
    (analytic : AnalyticSet target)
    (boxed : BoxedAnalytic removed) :
    FiniteAnalyticPartition (Set.difference target removed) := by
  classical
  let complementPieces := Classical.choose (boxed_complement_partition boxed)
  rcases Classical.choose_spec (boxed_complement_partition boxed) with
    ⟨eachAnalytic, pairwise, complementCover⟩
  let pieces := complementPieces.map (Set.inter target)
  refine {
    pieces := pieces
    analytic := ?_
    pairwise := ?_
    cover := ?_
  }
  · intro piece member
    rcases List.mem_map.mp member with ⟨original, inComplement, equal⟩
    subst piece
    exact analytic_set_inter analytic (eachAnalytic original inComplement)
  · apply List.Pairwise.map (R := Set.Disjoint) (S := Set.Disjoint)
        (Set.inter target)
    · intro first second disjoint point firstMember secondMember
      exact disjoint firstMember.2 secondMember.2
    · exact pairwise
  · intro point
    rw [listUnion_map_inter, complementCover]
    rfl

/-- Subtract a boxed set from every piece of an existing finite analytic
partition, preserving disjointness across its original pieces. -/
public noncomputable def FiniteAnalyticPartition.subtractBox
    {dimension : Nat} {target removed : Set (carrier dimension)}
    (partition : FiniteAnalyticPartition target)
    (boxed : BoxedAnalytic removed) :
    FiniteAnalyticPartition (Set.difference target removed) := by
  classical
  let piecesOf (piece : Set (carrier dimension)) :
      List (Set (carrier dimension)) :=
    if member : piece ∈ partition.pieces then
      (partitionDifference (partition.analytic piece member) boxed).pieces
    else []
  have piecesOfAnalytic (piece : Set (carrier dimension))
      (member : piece ∈ partition.pieces) :
      ∀ smaller, smaller ∈ piecesOf piece → AnalyticSet smaller := by
    intro smaller inSmaller
    have inPartitionPieces : smaller ∈
        (partitionDifference (partition.analytic piece member) boxed).pieces := by
      simpa only [piecesOf, dif_pos member] using inSmaller
    exact (partitionDifference (partition.analytic piece member) boxed).analytic
      smaller inPartitionPieces
  have piecesOfPairwise (piece : Set (carrier dimension))
      (member : piece ∈ partition.pieces) :
      List.Pairwise Set.Disjoint (piecesOf piece) := by
    simpa only [piecesOf, dif_pos member] using
      (partitionDifference (partition.analytic piece member) boxed).pairwise
  have piecesOfCover (piece : Set (carrier dimension))
      (member : piece ∈ partition.pieces) (point : carrier dimension) :
      listUnion (piecesOf piece) point ↔
        Set.difference piece removed point := by
    simpa only [piecesOf, dif_pos member] using
      (partitionDifference (partition.analytic piece member) boxed).cover point
  have piecesOfSubset (piece smaller : Set (carrier dimension))
      (member : smaller ∈ piecesOf piece) : Set.Subset smaller piece := by
    by_cases inPartition : piece ∈ partition.pieces
    · have covered := (piecesOfCover piece inPartition)
      intro point inside
      exact ((covered point).mp ⟨smaller, member, inside⟩).1
    · have impossible : False := by
        simp only [piecesOf, dif_neg inPartition] at member
        exact List.not_mem_nil member
      exact False.elim impossible
  refine {
    pieces := partition.pieces.flatMap piecesOf
    analytic := ?_
    pairwise := ?_
    cover := ?_
  }
  · intro smaller member
    rcases List.mem_flatMap.mp member with ⟨piece, inPartition, inSmaller⟩
    exact piecesOfAnalytic piece inPartition smaller inSmaller
  · apply List.pairwise_flatMap.mpr
    constructor
    · intro piece member
      exact piecesOfPairwise piece member
    · apply partition.pairwise.imp
      intro first second disjoint smaller inFirst other inSecond point
        inSmaller inOther
      exact disjoint (piecesOfSubset first smaller inFirst inSmaller)
        (piecesOfSubset second other inSecond inOther)
  · intro point
    constructor
    · rintro ⟨smaller, inFlat, inside⟩
      rcases List.mem_flatMap.mp inFlat with
        ⟨piece, inPartition, inSmaller⟩
      have within := (piecesOfCover piece inPartition point).mp
        ⟨smaller, inSmaller, inside⟩
      exact ⟨(partition.cover point).mp
        ⟨piece, inPartition, within.1⟩, within.2⟩
    · rintro ⟨inTarget, outside⟩
      rcases (partition.cover point).mpr inTarget with
        ⟨piece, inPartition, inside⟩
      rcases (piecesOfCover piece inPartition point).mpr
          ⟨inside, outside⟩ with ⟨smaller, inSmaller, within⟩
      exact ⟨smaller, List.mem_flatMap.mpr
        ⟨piece, inPartition, inSmaller⟩, within⟩

public def FiniteAnalyticPartition.cast {dimension : Nat}
    {first second : Set (carrier dimension)}
    (partition : FiniteAnalyticPartition first) (equal : first = second) :
    FiniteAnalyticPartition second where
  pieces := partition.pieces
  analytic := partition.analytic
  pairwise := partition.pairwise
  cover := by
    intro point
    exact (partition.cover point).trans
      (congrFun equal point |> Iff.of_eq)

/-- Starting from one analytic set, subtract each earlier boxed set while
retaining a finite disjoint analytic partition at every prefix. -/
public noncomputable def boxedPrefixPartition {dimension : Nat}
    (family : Nat → Set (carrier dimension))
    (boxed : ∀ index, BoxedAnalytic (family index))
    (index : Nat) : (bound : Nat) →
      FiniteAnalyticPartition
        (Set.difference (family index) (Set.prefixUnion family bound))
  | 0 => by
      have equal : family index =
          Set.difference (family index) (Set.prefixUnion family 0) := by
        apply Set.ext
        intro point
        change family index point ↔ (family index point ∧ ¬False)
        exact ⟨fun member => ⟨member, False.elim⟩,
          fun member => member.1⟩
      exact (partitionSingle (boxed index).analytic).cast equal
  | bound + 1 => by
      let previous := boxedPrefixPartition family boxed index bound
      let subtracted := previous.subtractBox (boxed bound)
      have equal :
          Set.difference
            (Set.difference (family index) (Set.prefixUnion family bound))
            (family bound) =
          Set.difference (family index)
            (Set.prefixUnion family (bound + 1)) := by
        apply Set.ext
        intro point
        change
          ((family index point ∧ ¬Set.prefixUnion family bound point) ∧
            ¬family bound point) ↔
          (family index point ∧
            ¬(Set.prefixUnion family bound point ∨ family bound point))
        constructor
        · rintro ⟨⟨inFamily, noEarlier⟩, noLast⟩
          exact ⟨inFamily, fun member => member.elim noEarlier noLast⟩
        · rintro ⟨inFamily, noEarlierOrLast⟩
          exact ⟨⟨inFamily, fun earlier =>
            noEarlierOrLast (Or.inl earlier)⟩,
            fun last => noEarlierOrLast (Or.inr last)⟩
      exact subtracted.cast equal

/-- A c-analytic set admits a countable, pairwise-disjoint analytic
partition. The construction first uses rational boxes to localize every
analytic constraint, then removes preceding boxed pieces by finite
first-failure partitions. -/
public theorem c_analytic_disjoint_refinement {dimension : Nat}
    {points : Set (carrier dimension)} (analytic : CAnalytic points) :
    ∃ pieces : Nat → Set (carrier dimension),
      (∀ index, AnalyticSet (pieces index)) ∧
        Set.PairwiseDisjoint pieces ∧ points = Set.iUnion pieces := by
  classical
  rcases analytic with ⟨analyticPieces, eachAnalytic, analyticCover⟩
  let boxCover (index : Nat) :=
    analytic_set_box_cover (eachAnalytic index)
  let boxedPieces (index : Nat) : Nat → Set (carrier dimension) :=
    Classical.choose (boxCover index)
  have eachBoxed (index piece : Nat) :
      Nonempty (BoxedAnalytic (boxedPieces index piece)) :=
    (Classical.choose_spec (boxCover index)).1 piece
  have boxedCover (index : Nat) :
      analyticPieces index = Set.iUnion (boxedPieces index) :=
    (Classical.choose_spec (boxCover index)).2
  let packed (code : Nat) : Set (carrier dimension) :=
    boxedPieces (Problib.Countable.Pair.decode code).1
      (Problib.Countable.Pair.decode code).2
  let boxed (code : Nat) : BoxedAnalytic (packed code) :=
    Classical.choice (eachBoxed _ _)
  have packedCover : points = Set.iUnion packed := by
    apply Set.ext
    intro point
    rw [analyticCover]
    constructor
    · rintro ⟨index, inAnalytic⟩
      rw [boxedCover index] at inAnalytic
      rcases inAnalytic with ⟨piece, inBoxed⟩
      exact ⟨Problib.Countable.Pair.encode (index, piece), by
        simpa only [packed, Problib.Countable.Pair.decode_encode] using inBoxed⟩
    · rintro ⟨code, inPacked⟩
      let pair := Problib.Countable.Pair.decode code
      exact ⟨pair.1, by
        rw [boxedCover pair.1]
        exact ⟨pair.2, inPacked⟩⟩
  let partition (index : Nat) := boxedPrefixPartition packed boxed index index
  let refined (code : Nat) : Set (carrier dimension) :=
    ((partition (Problib.Countable.Pair.decode code).1).pieces).getD
      (Problib.Countable.Pair.decode code).2 Set.empty
  have refinedAnalytic (code : Nat) : AnalyticSet (refined code) := by
    let pair := Problib.Countable.Pair.decode code
    by_cases inRange : pair.2 < (partition pair.1).pieces.length
    · have inPartition : (partition pair.1).pieces[pair.2]'inRange ∈
          (partition pair.1).pieces := List.getElem_mem inRange
      have equal : refined code =
          (partition pair.1).pieces[pair.2]'inRange := by
        exact (List.getElem_eq_getD Set.empty).symm
      rw [equal]
      exact (partition pair.1).analytic _ inPartition
    · have equal : refined code = Set.empty := by
        simp only [refined, pair, List.getD_eq_getElem?_getD,
          List.getD_getElem?, dif_neg inRange]
      rw [equal]
      exact analytic_set_empty dimension
  have refinedSubset (code : Nat) :
      Set.Subset (refined code)
        (Set.disjointed packed (Problib.Countable.Pair.decode code).1) := by
    let pair := Problib.Countable.Pair.decode code
    by_cases inRange : pair.2 < (partition pair.1).pieces.length
    · intro point member
      have inPartition : (partition pair.1).pieces[pair.2]'inRange ∈
          (partition pair.1).pieces := List.getElem_mem inRange
      have inPiece :
          ((partition pair.1).pieces[pair.2]'inRange) point := by
        have equal : refined code =
            (partition pair.1).pieces[pair.2]'inRange :=
          (List.getElem_eq_getD Set.empty).symm
        exact equal ▸ member
      exact ((partition pair.1).cover point).mp
        ⟨_, inPartition, inPiece⟩
    · intro point member
      have impossible : False := by
        have equal : refined code = Set.empty := by
          simp only [refined, pair, List.getD_eq_getElem?_getD,
            List.getD_getElem?, dif_neg inRange]
        rw [equal] at member
        exact member
      exact False.elim impossible
  refine ⟨refined, refinedAnalytic, ?_, ?_⟩
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
        fun equal => pairsDifferent (Prod.ext firstIndexEqual equal)
      have firstBound : firstPair.2 <
          (partition firstPair.1).pieces.length := by
        by_cases bound : firstPair.2 < (partition firstPair.1).pieces.length
        · exact bound
        · have impossible : False := by
            change ((partition firstPair.1).pieces.getD
              firstPair.2 Set.empty) point at inFirst
            simp only [List.getD_eq_getElem?_getD,
              List.getD_getElem?, dif_neg bound, Set.empty] at inFirst
          exact False.elim impossible
      have secondBound : secondPair.2 <
          (partition secondPair.1).pieces.length := by
        by_cases bound : secondPair.2 < (partition secondPair.1).pieces.length
        · exact bound
        · have impossible : False := by
            change ((partition secondPair.1).pieces.getD
              secondPair.2 Set.empty) point at inSecond
            simp only [List.getD_eq_getElem?_getD,
              List.getD_getElem?, dif_neg bound, Set.empty] at inSecond
          exact False.elim impossible
      have secondBound' : secondPair.2 <
          (partition firstPair.1).pieces.length :=
        firstIndexEqual ▸ secondBound
      have secondRaw :
          ((partition secondPair.1).pieces.getD
            secondPair.2 Set.empty) point := by
        exact inSecond
      have secondMember :
          ((partition firstPair.1).pieces[secondPair.2]'secondBound') point := by
        have transported : ((partition firstPair.1).pieces.getD
            secondPair.2 Set.empty) point := by
          have sameList : (partition firstPair.1).pieces =
              (partition secondPair.1).pieces :=
            congrArg (fun index => (partition index).pieces) firstIndexEqual
          rw [sameList]
          exact secondRaw
        rw [List.getElem_eq_getD]
        exact transported
      have firstMember :
          ((partition firstPair.1).pieces[firstPair.2]'firstBound) point := by
        rw [List.getElem_eq_getD]
        exact inFirst
      rcases Nat.lt_or_gt_of_ne secondIndexDifferent with before | after
      · exact (List.pairwise_iff_getElem.mp
          (partition firstPair.1).pairwise)
          firstPair.2 secondPair.2 firstBound secondBound' before
          firstMember secondMember
      · have reverse := (List.pairwise_iff_getElem.mp
          (partition firstPair.1).pairwise)
          secondPair.2 firstPair.2 secondBound' firstBound after
        exact (Set.disjoint_symm reverse) firstMember secondMember
    · exact Set.disjointed_pairwise packed firstPair.1 secondPair.1
        firstIndexEqual
        (refinedSubset first inFirst) (refinedSubset second inSecond)
  · apply Set.ext
    intro point
    rw [packedCover]
    constructor
    · intro inPacked
      have inDisjointUnion : Set.iUnion (Set.disjointed packed) point := by
        rw [Set.iUnion_disjointed]
        exact inPacked
      rcases inDisjointUnion with ⟨index, inDisjoint⟩
      rcases ((partition index).cover point).mpr inDisjoint with
        ⟨piece, inPartition, inside⟩
      rcases List.getElem_of_mem inPartition with
        ⟨pieceIndex, inRange, equal⟩
      refine ⟨Problib.Countable.Pair.encode (index, pieceIndex), ?_⟩
      have inSelected : ((partition index).pieces.getD
          pieceIndex Set.empty) point := by
        rw [← List.getElem_eq_getD (h := inRange)]
        exact equal ▸ inside
      change ((partition (Problib.Countable.Pair.decode
        (Problib.Countable.Pair.encode (index, pieceIndex))).1).pieces.getD
          (Problib.Countable.Pair.decode
            (Problib.Countable.Pair.encode (index, pieceIndex))).2
          Set.empty) point
      rw [Problib.Countable.Pair.decode_encode]
      exact inSelected
    · rintro ⟨code, inRefined⟩
      have inDisjoint := refinedSubset code inRefined
      exact ⟨(Problib.Countable.Pair.decode code).1, inDisjoint.1⟩

end Problib.Analysis.PAP
