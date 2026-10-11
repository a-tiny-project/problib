module

public import Problib.Analysis.Real.PowerSeries.Identity
public import Problib.Measure.Real.Lebesgue
public import Problib.Measure.Null.Basic
public import Problib.Real.Basis
public import Problib.Countable.Bijection

/-! Zero sets of analytic functions on an interval have zero volume.

A set whose points are each isolated from the rest is covered by countably
many rational windows, each holding at most one of its points, so it is null.
The zeros of an analytic function that does not vanish on the whole interval
are never flat, by the identity theorem. Each zero therefore has a least order
at which the next derivative is nonzero, and it is isolated among the zeros of
the derivative of that order.
-/

set_option autoImplicit false

namespace Problib.Analysis.PAP

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real
open Problib.Analysis.Real.PowerSeries
open Problib.Measure

noncomputable section

private def window (code : Nat) : Set selection.Carrier :=
  fun value =>
    lt (rationalBasis (Problib.Countable.Pair.decode code).1) value ∧
      lt value (rationalBasis (Problib.Countable.Pair.decode code).2)

/-- A set whose every point has a neighborhood free of its other points has
zero volume. -/
public theorem isolated_null {points : Set selection.Carrier}
    (isolated : ∀ point, points point →
      ∃ radius, lt zero radius ∧
        ∀ other, points other → lt (abs (sub other point)) radius →
          other = point) :
    Problib.Measure.Real.volume.NullSet points := by
  classical
  let piece (code : Nat) : Set selection.Carrier := fun value =>
    points value ∧ window code value ∧
      ∀ other, points other → window code other → other = value
  have pieceNull : ∀ code, Problib.Measure.Real.volume.NullSet (piece code) := by
    intro code
    by_cases occupied : ∃ value, piece code value
    · rcases occupied with ⟨value, member⟩
      apply Measure.NullSet.mono
        (show Problib.Measure.Real.volume.NullSet (Set.singleton value) from
          Problib.Measure.Real.volume_singleton value)
      intro other otherMember
      exact member.2.2 other otherMember.1 otherMember.2.1
    · apply Measure.NullSet.mono (Measure.null_empty _)
      intro value member
      exact occupied ⟨value, member⟩
  apply Measure.NullSet.mono (Measure.NullSet.iUnion pieceNull)
  intro point member
  rcases isolated point member with ⟨radius, positive, apart⟩
  have lowerGap : lt (sub point radius) point := by
    apply sub_positive_iff.mp
    rw [sub_sub_cancel]
    exact positive
  have upperGap : lt point (add point radius) := by
    simpa only [add_zero] using add_lt_add_left point positive
  rcases exists_rationalBasis_between lowerGap with
    ⟨lowerCode, lowerAbove, lowerBelow⟩
  rcases exists_rationalBasis_between upperGap with
    ⟨upperCode, upperAbove, upperBelow⟩
  refine ⟨Problib.Countable.Pair.encode (lowerCode, upperCode), ?_⟩
  have decoded := Problib.Countable.Pair.decode_encode (lowerCode, upperCode)
  have inWindow : ∀ value, window (Problib.Countable.Pair.encode
      (lowerCode, upperCode)) value ↔
      lt (rationalBasis lowerCode) value ∧
        lt value (rationalBasis upperCode) := by
    intro value
    unfold window
    rw [decoded]
  refine ⟨member, (inWindow point).mpr ⟨lowerBelow, upperAbove⟩, ?_⟩
  intro other otherMember otherWindow
  rcases (inWindow other).mp otherWindow with ⟨otherLower, otherUpper⟩
  apply apart other otherMember
  apply abs_lt.mpr
  constructor
  · have shifted := add_lt_add_right (neg point)
      (lt_trans lowerAbove otherLower)
    have shift : add (sub point radius) (neg point) = neg radius := by
      rw [← sub_eq_add_neg, sub_eq_add_neg point radius, add_sub_self]
    rwa [shift, ← sub_eq_add_neg] at shifted
  · have shifted := add_lt_add_right (neg point)
      (lt_trans otherUpper upperBelow)
    rwa [← sub_eq_add_neg, ← sub_eq_add_neg, add_sub_self] at shifted

/-- The zeros of an analytic function on an open interval have zero volume,
unless the function vanishes on the whole interval. -/
public theorem line_zero_null {center radius : selection.Carrier}
    {function : FiniteVector.carrier 1 → selection.Carrier}
    (analytic : AnalyticOn (FiniteVector.ball (linePoint center) radius)
      function)
    (somewhereNonzero : ¬∀ value, lt (abs (sub value center)) radius →
      function (linePoint value) = zero) :
    Problib.Measure.Real.volume.NullSet (fun value =>
      lt (abs (sub value center)) radius ∧
        function (linePoint value) = zero) := by
  classical
  have neverFlat : ∀ value, lt (abs (sub value center)) radius →
      ¬FlatAt function (linePoint value) := by
    intro value inside flat
    apply somewhereNonzero
    intro target targetInside
    exact line_identity analytic inside flat targetInside 0
  let layer (count : Nat) : Set selection.Carrier := fun value =>
    lt (abs (sub value center)) radius ∧
      lineDerivative function count (linePoint value) = zero ∧
      lineDerivative function (count + 1) (linePoint value) ≠ zero
  have layerNull : ∀ count, Problib.Measure.Real.volume.NullSet (layer count) := by
    intro count
    apply isolated_null
    intro value member
    rcases lineDerivative_isolated analytic count member.1 member.2.1 member.2.2
      with ⟨isolation, positive, apart⟩
    exact ⟨isolation, positive, fun other otherMember close =>
      apart other close otherMember.2.1⟩
  apply Measure.NullSet.mono (Measure.NullSet.iUnion layerNull)
  intro value member
  have notFlat := neverFlat value member.1
  unfold FlatAt at notFlat
  rcases Classical.not_forall.mp notFlat with ⟨order, nonzero⟩
  have exists_next : ∃ count, lineDerivative function (count + 1)
      (linePoint value) ≠ zero := by
    cases order with
    | zero => exact False.elim (nonzero member.2)
    | succ order => exact ⟨order, nonzero⟩
  have descend : ∀ count, lineDerivative function (count + 1)
      (linePoint value) ≠ zero →
      ∃ order, lineDerivative function order (linePoint value) = zero ∧
        lineDerivative function (order + 1) (linePoint value) ≠ zero := by
    intro count
    induction count with
    | zero => exact fun nonzero => ⟨0, member.2, nonzero⟩
    | succ count induction =>
        intro nonzero
        by_cases vanished : lineDerivative function (count + 1)
            (linePoint value) = zero
        · exact ⟨count + 1, vanished, nonzero⟩
        · exact induction vanished
  rcases exists_next with ⟨count, nonzero⟩
  rcases descend count nonzero with ⟨order, vanished, next⟩
  exact ⟨order, member.1, vanished, next⟩

end

end Problib.Analysis.PAP
