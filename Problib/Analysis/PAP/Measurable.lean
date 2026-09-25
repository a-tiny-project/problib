module

public import Problib.Analysis.PAP.Operations
public import Problib.Analysis.Real.FiniteVector.Borel

set_option autoImplicit false

namespace Problib.Analysis.PAP

open Problib.Measure
open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real
open Problib.Analysis.Real.FiniteVector
open Problib.Analysis.Real.PowerSeries

private theorem less_of_abs_sub_less {first second tolerance : selection.Carrier}
    (near : lt (abs (sub second first)) tolerance) :
    lt second (add first tolerance) := by
  have upper := (abs_lt.mp near).2
  have shifted := add_lt_add_left first upper
  rwa [add_sub_cancel] at shifted

private theorem greater_of_abs_sub_less {first second tolerance : selection.Carrier}
    (near : lt (abs (sub second first)) tolerance) :
    lt (sub first tolerance) second := by
  have lower := (abs_lt.mp near).1
  have shifted := add_lt_add_left first lower
  rw [← sub_eq_add_neg, add_sub_cancel] at shifted
  exact shifted

/-- A strict analytic superlevel is open inside the analytic function's
domain. -/
public theorem analytic_superlevel_open {dimension : Nat}
    {region : Set (carrier dimension)}
    {function : carrier dimension → selection.Carrier}
    (analytic : AnalyticOn region function)
    (bound : selection.Carrier) :
    IsOpen (fun point => region point ∧ lt bound (function point)) := by
  intro point member
  rcases analytic.left point member.1 with
    ⟨regionRadius, regionPositive, staysInRegion⟩
  let tolerance := sub (function point) bound
  have tolerancePositive : lt zero tolerance :=
    sub_positive_iff.mpr member.2
  rcases analytic_on_continuous_at analytic point member.1
    tolerance tolerancePositive with
      ⟨functionRadius, functionPositive, staysAbove⟩
  rcases small_positive regionPositive functionPositive with
    ⟨radius, positive, belowRegion, belowFunction⟩
  refine ⟨radius, positive, fun neighbor near => ?_⟩
  have insideRegion := staysInRegion neighbor (ball_mono belowRegion near)
  have close := staysAbove neighbor (ball_mono belowFunction near)
  have above := greater_of_abs_sub_less close
  rw [sub_sub_cancel] at above
  exact ⟨insideRegion, above⟩

/-- A nonpositive analytic inequality is Borel measurable on its open
domain. -/
public theorem analytic_sublevel_measurable {dimension : Nat}
    {region : Set (carrier dimension)}
    {function : carrier dimension → selection.Carrier}
    (analytic : AnalyticOn region function) :
    (vectorBorel dimension).Measurable
      (fun point => region point ∧ le (function point) zero) := by
  let superlevel : Set (carrier dimension) :=
    fun point => region point ∧ lt zero (function point)
  have openSuperlevel : IsOpen superlevel :=
    analytic_superlevel_open analytic zero
  have differenceMeasurable := (vectorBorel dimension).difference
    (open_measurable analytic.left) (open_measurable openSuperlevel)
  have equal : Set.difference region superlevel =
      (fun point => region point ∧ le (function point) zero) := by
    apply Set.ext
    intro point
    change (region point ∧ ¬(region point ∧ lt zero (function point))) ↔
      (region point ∧ le (function point) zero)
    constructor
    · rintro ⟨inRegion, notPositive⟩
      by_cases nonpositive : le (function point) zero
      · exact ⟨inRegion, nonpositive⟩
      · exact False.elim
          (notPositive ⟨inRegion, lt_of_not_le nonpositive⟩)
    · rintro ⟨inRegion, nonpositive⟩
      exact ⟨inRegion, fun positive => positive.2.2 nonpositive⟩
  rw [← equal]
  exact differenceMeasurable

public theorem analytic_set_measurable {dimension : Nat}
    {points : Set (carrier dimension)} (analytic : AnalyticSet points) :
    (vectorBorel dimension).Measurable points := by
  rcases analytic with ⟨region, constraints, openRegion, eachAnalytic, character⟩
  let constrained : List (carrier dimension → selection.Carrier) →
      Set (carrier dimension) := fun list point =>
    region point ∧ ∀ constraint, constraint ∈ list → le (constraint point) zero
  have measurableList (list : List (carrier dimension → selection.Carrier))
      (included : ∀ constraint, constraint ∈ list → AnalyticOn region constraint) :
      (vectorBorel dimension).Measurable (constrained list) := by
    induction list with
    | nil =>
        have equal : constrained [] = region := by
          apply Set.ext
          intro point
          simp [constrained]
        rw [equal]
        exact open_measurable openRegion
    | cons head tail induction =>
        have headAnalytic : AnalyticOn region head :=
          included head (List.mem_cons_self)
        have tailMeasurable := induction (fun constraint member =>
          included constraint (List.mem_cons_of_mem head member))
        have intersectMeasurable := (vectorBorel dimension).inter
          (analytic_sublevel_measurable headAnalytic) tailMeasurable
        have equal : constrained (head :: tail) =
            Set.inter (fun point => region point ∧ le (head point) zero)
              (constrained tail) := by
          apply Set.ext
          intro point
          change (region point ∧ ∀ constraint,
            constraint ∈ head :: tail → le (constraint point) zero) ↔
            ((region point ∧ le (head point) zero) ∧
              (region point ∧ ∀ constraint,
                constraint ∈ tail → le (constraint point) zero))
          constructor
          · rintro ⟨inRegion, bounded⟩
            exact ⟨⟨inRegion, bounded head (List.mem_cons_self)⟩,
              inRegion, fun constraint member =>
                bounded constraint (List.mem_cons_of_mem head member)⟩
          · rintro ⟨⟨inRegion, headBound⟩, _, tailBound⟩
            refine ⟨inRegion, fun constraint member => ?_⟩
            rcases List.mem_cons.mp member with equal | inTail
            · subst constraint
              exact headBound
            · exact tailBound constraint inTail
        rw [equal]
        exact intersectMeasurable
  have measured := measurableList constraints eachAnalytic
  have equal : points = constrained constraints := by
    apply Set.ext
    intro point
    exact character point
  rw [equal]
  exact measured

public theorem c_analytic_measurable {dimension : Nat}
    {points : Set (carrier dimension)} (analytic : CAnalytic points) :
    (vectorBorel dimension).Measurable points := by
  rcases analytic with ⟨pieces, eachAnalytic, cover⟩
  rw [cover]
  exact (vectorBorel dimension).iUnion
    (fun index => analytic_set_measurable (eachAnalytic index))

private theorem analytic_scalar_piece_preimage_measurable {dimension : Nat}
    {piece region : Set (carrier dimension)}
    {function : carrier dimension → selection.Carrier}
    (pieceMeasurable : (vectorBorel dimension).Measurable piece)
    (inside : Set.Subset piece region)
    (analytic : AnalyticOn region function)
    {targetSet : Set selection.Carrier}
    (targetMeasurable : Problib.Measure.Real.borel.Measurable targetSet) :
    (vectorBorel dimension).Measurable
      (fun point => piece point ∧ targetSet (function point)) := by
  induction targetMeasurable with
  | @basic interval generator =>
      rcases generator with ⟨lower, upper, rfl⟩
      have lowerOpen := open_measurable
        (analytic_superlevel_open analytic lower)
      have upperOpen := open_measurable
        (analytic_superlevel_open analytic upper)
      have upperMeasured := (vectorBorel dimension).difference
        (open_measurable analytic.left) upperOpen
      have both := (vectorBorel dimension).inter pieceMeasurable
        ((vectorBorel dimension).inter lowerOpen upperMeasured)
      have equal : (fun point => piece point ∧
          Problib.Measure.Real.Ioc lower upper (function point)) =
          Set.inter piece (Set.inter
            (fun point => region point ∧ lt lower (function point))
            (Set.difference region
              (fun point => region point ∧ lt upper (function point)))) := by
        apply Set.ext
        intro point
        change (piece point ∧
          (lt lower (function point) ∧ le (function point) upper)) ↔
          (piece point ∧ (region point ∧ lt lower (function point)) ∧
            (region point ∧ ¬(region point ∧ lt upper (function point))))
        constructor
        · rintro ⟨inPiece, lowerBound, upperBound⟩
          have inRegion := inside inPiece
          exact ⟨inPiece, ⟨inRegion, lowerBound⟩,
            ⟨inRegion, fun above => above.2.2 upperBound⟩⟩
        · rintro ⟨inPiece, ⟨_, lowerBound⟩, ⟨inRegion, notAbove⟩⟩
          refine ⟨inPiece, lowerBound, ?_⟩
          by_cases bound : le (function point) upper
          · exact bound
          · exact False.elim
              (notAbove ⟨inRegion, lt_of_not_le bound⟩)
      rw [equal]
      exact both
  | empty =>
      have equal : (fun point => piece point ∧
          (Set.empty : Set selection.Carrier) (function point)) = Set.empty := by
        apply Set.ext
        intro point
        exact ⟨fun member => member.2, fun impossible => False.elim impossible⟩
      rw [equal]
      exact (vectorBorel dimension).empty
  | @complement targetSet measured induction =>
      have differenceMeasurable := (vectorBorel dimension).difference
        pieceMeasurable induction
      have equal : (fun point => piece point ∧
          (Set.complement targetSet) (function point)) =
          Set.difference piece
            (fun point => piece point ∧ targetSet (function point)) := by
        apply Set.ext
        intro point
        exact ⟨fun member => ⟨member.1, fun other => member.2 other.2⟩,
          fun member => ⟨member.1, fun other => member.2 ⟨member.1, other⟩⟩⟩
      rw [equal]
      exact differenceMeasurable
  | @iUnion sets measured induction =>
      have unionMeasurable := (vectorBorel dimension).iUnion induction
      have equal : (fun point => piece point ∧
          (Set.iUnion sets) (function point)) =
          Set.iUnion (fun index point => piece point ∧ sets index (function point)) := by
        apply Set.ext
        intro point
        exact ⟨fun member => by
            rcases member with ⟨inPiece, index, inTarget⟩
            exact ⟨index, inPiece, inTarget⟩,
          fun member => by
            rcases member with ⟨index, inPiece, inTarget⟩
            exact ⟨inPiece, index, inTarget⟩⟩
      rw [equal]
      exact unionMeasurable

/-- A measurable piece can be tested against any target Borel set through
an analytic witness defined on an open neighborhood of the piece. -/
public theorem analytic_piece_preimage_measurable {source target : Nat}
    {piece region : Set (carrier source)}
    {function : carrier source → carrier target}
    (pieceMeasurable : (vectorBorel source).Measurable piece)
    (_openRegion : IsOpen region)
    (inside : Set.Subset piece region)
    (analytic : AnalyticVectorOn region function)
    {targetSet : Set (carrier target)}
    (targetMeasurable : (vectorBorel target).Measurable targetSet) :
    (vectorBorel source).Measurable
      (fun point => piece point ∧ targetSet (function point)) := by
  induction targetMeasurable with
  | @basic openSet targetOpen =>
      rcases targetOpen with ⟨coordinate, coordinateSet,
        coordinateMeasurable, rfl⟩
      exact analytic_scalar_piece_preimage_measurable
        pieceMeasurable inside (analytic coordinate) coordinateMeasurable
  | empty =>
      have equal : (fun point => piece point ∧
          (Set.empty : Set (carrier target)) (function point)) = Set.empty := by
        apply Set.ext
        intro point
        exact ⟨fun member => member.2, fun impossible => False.elim impossible⟩
      rw [equal]
      exact (vectorBorel source).empty
  | @complement targetSet targetMeasurable induction =>
      have differenceMeasurable := (vectorBorel source).difference
        pieceMeasurable induction
      have equal : (fun point => piece point ∧
          (Set.complement targetSet) (function point)) =
          Set.difference piece
            (fun point => piece point ∧ targetSet (function point)) := by
        apply Set.ext
        intro point
        change (piece point ∧ ¬targetSet (function point)) ↔
          (piece point ∧ ¬(piece point ∧ targetSet (function point)))
        constructor
        · rintro ⟨inPiece, outside⟩
          exact ⟨inPiece, fun member => outside member.2⟩
        · rintro ⟨inPiece, outside⟩
          exact ⟨inPiece, fun inTarget => outside ⟨inPiece, inTarget⟩⟩
      rw [equal]
      exact differenceMeasurable
  | @iUnion sets each induction =>
      have unionMeasurable := (vectorBorel source).iUnion induction
      have equal : (fun point => piece point ∧
          (Set.iUnion sets) (function point)) =
          Set.iUnion (fun index point =>
            piece point ∧ sets index (function point)) := by
        apply Set.ext
        intro point
        change (piece point ∧ (∃ index, sets index (function point))) ↔
          (∃ index, piece point ∧ sets index (function point))
        constructor
        · rintro ⟨inPiece, index, inTarget⟩
          exact ⟨index, inPiece, inTarget⟩
        · rintro ⟨index, inPiece, inTarget⟩
          exact ⟨inPiece, index, inTarget⟩
      rw [equal]
      exact unionMeasurable

/-- PAP maps are measurable on their domain: each target preimage is a
countable union of measurable analytic-piece preimages. -/
public theorem pap_preimage_measurable {source target : Nat}
    {domain : Set (carrier source)}
    {function : carrier source → carrier target}
    (representation : PAPRepresentation domain function)
    {targetSet : Set (carrier target)}
    (targetMeasurable : (vectorBorel target).Measurable targetSet) :
    (vectorBorel source).Measurable
      (fun point => domain point ∧ targetSet (function point)) := by
  let pieces (index : Nat) : Set (carrier source) :=
    fun point => representation.pieces index point ∧ targetSet (function point)
  have each (index : Nat) : (vectorBorel source).Measurable (pieces index) := by
    have localMeasurable := analytic_piece_preimage_measurable
      (analytic_set_measurable (representation.analytic index))
      (representation.open_regions index)
      (representation.pieces_in_regions index)
      (representation.analytic_witnesses index) targetMeasurable
    have equal : pieces index =
        (fun point => representation.pieces index point ∧
          targetSet (representation.witnesses index point)) := by
      apply Set.ext
      intro point
      change (representation.pieces index point ∧ targetSet (function point)) ↔
        (representation.pieces index point ∧
          targetSet (representation.witnesses index point))
      constructor
      · rintro ⟨inPiece, inTarget⟩
        exact ⟨inPiece, (representation.agrees index point inPiece) ▸ inTarget⟩
      · rintro ⟨inPiece, inTarget⟩
        exact ⟨inPiece, (representation.agrees index point inPiece).symm ▸ inTarget⟩
    rw [equal]
    exact localMeasurable
  have unionMeasurable := (vectorBorel source).iUnion each
  have equal : (fun point => domain point ∧ targetSet (function point)) =
      Set.iUnion pieces := by
    apply Set.ext
    intro point
    constructor
    · rintro ⟨inDomain, inTarget⟩
      rw [representation.cover] at inDomain
      rcases inDomain with ⟨index, inPiece⟩
      exact ⟨index, inPiece, inTarget⟩
    · rintro ⟨index, inPiece, inTarget⟩
      exact ⟨by rw [representation.cover]; exact ⟨index, inPiece⟩,
        inTarget⟩
  rw [equal]
  exact unionMeasurable

public theorem PartialPAP.measurable {source target : Nat}
    (map : PartialPAP source target) :
    MeasurableMap
      (Space.comap (fun point : {point : carrier source // map.domain point} =>
        point.val) (vectorBorel source))
      (vectorBorel target) map.values := by
  intro targetSet targetMeasurable
  have ambient := pap_preimage_measurable map.representation targetMeasurable
  let sourceSet : Set (carrier source) := fun point =>
    map.domain point ∧ targetSet (map.totalize point)
  have sourceMeasurable : (vectorBorel source).Measurable sourceSet := ambient
  have equal : Set.preimage map.values targetSet =
      Set.preimage (fun point : {point : carrier source // map.domain point} =>
        point.val) sourceSet := by
    apply Set.ext
    intro point
    change targetSet (map.values point) ↔
      (map.domain point.val ∧ targetSet (map.totalize point.val))
    rw [map.totalize_on_domain point.property]
    exact ⟨fun member => ⟨point.property, member⟩,
      fun member => member.2⟩
  rw [equal]
  exact Space.comap_map _ _ sourceMeasurable

end Problib.Analysis.PAP
