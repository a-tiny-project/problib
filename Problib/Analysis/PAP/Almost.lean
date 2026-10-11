module

public import Problib.Analysis.PAP.ZeroSet
public import Problib.Analysis.PAP.Derivative
public import Problib.Analysis.Real.FiniteVector.Basis
public import Problib.Measure.AlmostEverywhere.Basic

/-! The intensional derivative is the ordinary derivative almost everywhere.

Fix a chosen PAP representation. Its bad set collects, for every piece, every
constraint of that piece and every rational coordinate ball inside the
constraint's domain on which the constraint does not vanish identically, the
zeros of the constraint in that ball. Each of these countably many sets is
null when the measure makes nonvanishing analytic zero sets null. Off the
bad set, a point of the domain meets each constraint of its piece either
strictly, so the constraint stays negative nearby, or at a zero on a ball
where the constraint vanishes identically. Either way the piece contains a
neighborhood of the point. There the map equals the piece's analytic
witness, so it has the witness's coordinate derivatives, which are the
intensional derivative. An identically zero constraint is the case Lee et al.
single out: its boundary is not null, and it is harmless because it cuts
nothing away.
-/

set_option autoImplicit false

namespace Problib.Analysis.PAP

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real
open Problib.Analysis.Real.FiniteVector
open Problib.Analysis.Real.PowerSeries
open Problib.Measure

noncomputable section

/-- A measure for which the zeros of an analytic function on a coordinate
ball are null unless the function vanishes on the whole ball. -/
@[expose] public def NullAnalyticZeros {dimension : Nat}
    (measure : Measure (vectorBorel dimension)) : Prop :=
  ∀ (center : carrier dimension) (radius : selection.Carrier)
    (function : carrier dimension → selection.Carrier),
    AnalyticOn (ball center radius) function →
    (∀ point, ball center radius point → function point = zero) ∨
      measure.NullSet
        (fun point => ball center radius point ∧ function point = zero)

/-- Every measure of a first-coordinate Tonelli family makes nonvanishing
analytic zero sets null. -/
public theorem null_analytic_zeros_of_tonelli
    {law : (dimension : Nat) → Measure (vectorBorel dimension)}
    (tonelli : FirstCoordinateTonelli law) (dimension : Nat) :
    NullAnalyticZeros (law dimension) :=
  analytic_zero_null tonelli dimension

private theorem null_of_list {dimension : Nat}
    {measure : Measure (vectorBorel dimension)}
    {α : Type} (items : List α) (sets : α → Set (carrier dimension))
    (each : ∀ item, item ∈ items → measure.NullSet (sets item)) :
    measure.NullSet (fun point => ∃ item, item ∈ items ∧ sets item point) := by
  induction items with
  | nil =>
      apply Measure.NullSet.mono (Measure.null_empty _)
      rintro point ⟨item, member, _⟩
      exact False.elim (List.not_mem_nil member)
  | cons first rest induction =>
      apply Measure.NullSet.mono
        (Measure.NullSet.union (each first List.mem_cons_self)
          (induction fun item member =>
            each item (List.mem_cons_of_mem _ member)))
      rintro point ⟨item, member, inside⟩
      rcases List.mem_cons.mp member with equal | later
      · left
        rw [← equal]
        exact inside
      · right
        exact ⟨item, later, inside⟩

private theorem exists_rational_ball_inside {dimension : Nat}
    {region : Set (carrier dimension)} (openRegion : IsOpen region)
    {point : carrier dimension} (member : region point) :
    ∃ centerCode radiusCode,
      ball (rationalCenter dimension centerCode)
        (rationalBasis radiusCode) point ∧
      ∀ other, ball (rationalCenter dimension centerCode)
        (rationalBasis radiusCode) other → region other := by
  rcases openRegion point member with ⟨radius, positive, inside⟩
  rcases exists_rationalBasis_between (half_positive positive) with
    ⟨radiusCode, radiusPositive, radiusSmall⟩
  let step := rationalBasis radiusCode
  rcases exists_rationalCenter_between
    (lower := fun coordinate => sub (point coordinate) step)
    (upper := fun coordinate => add (point coordinate) step)
    (fun coordinate => by
      apply lt_trans (middle := point coordinate)
      · apply sub_positive_iff.mp
        rw [sub_sub_cancel]
        exact radiusPositive
      · simpa only [add_zero] using
          add_lt_add_left (point coordinate) radiusPositive) with
    ⟨centerCode, between⟩
  have near : ∀ coordinate, lt (abs (sub (point coordinate)
      (rationalCenter dimension centerCode coordinate))) step := by
    intro coordinate
    rcases between coordinate with ⟨lower, upper⟩
    rw [abs_sub_comm]
    apply abs_lt.mpr
    constructor
    · have shifted := add_lt_add_right (neg (point coordinate)) lower
      have shift : add (sub (point coordinate) step) (neg (point coordinate)) =
          neg step := by
        rw [← sub_eq_add_neg, sub_eq_add_neg (point coordinate) step,
          add_sub_self]
      rwa [shift, ← sub_eq_add_neg] at shifted
    · have shifted := add_lt_add_right (neg (point coordinate)) upper
      rwa [← sub_eq_add_neg, ← sub_eq_add_neg, add_sub_self] at shifted
  refine ⟨centerCode, radiusCode, near, fun other otherInside => ?_⟩
  apply inside
  intro coordinate
  have split : sub (other coordinate) (point coordinate) =
      add (sub (other coordinate) (rationalCenter dimension centerCode coordinate))
        (sub (rationalCenter dimension centerCode coordinate) (point coordinate)) :=
    (sub_add_sub _ _ _).symm
  rw [split]
  apply lt_of_le_of_lt (abs_add_le _ _)
  have doubled : lt (add step step) radius := by
    have both := add_lt_add radiusSmall radiusSmall
    rwa [add_half] at both
  apply lt_trans (add_lt_add (otherInside coordinate) ?_) doubled
  rw [abs_sub_comm]
  exact near coordinate

private theorem ball_coordinate_step {dimension : Nat}
    {point : carrier dimension} {radius step : selection.Carrier}
    (positive : lt zero radius) (small : lt (abs step) radius)
    (selected : Fin dimension) :
    ball point radius (addVector point
      (replaceCoordinate (zeroVector dimension) selected step)) := by
  classical
  intro coordinate
  change lt (abs (sub (add (point coordinate)
    (replaceCoordinate (zeroVector dimension) selected step coordinate))
    (point coordinate))) radius
  rw [add_sub_self]
  by_cases equal : coordinate = selected
  · rw [show replaceCoordinate (zeroVector dimension) selected step coordinate =
      step from ite_eq_left equal]
    exact small
  · rw [show replaceCoordinate (zeroVector dimension) selected step coordinate =
      zero from ite_eq_right equal, abs_zero]
    exact positive

/-- A coordinate ball is open for every radius. A nonpositive radius leaves it
empty in positive dimension and the whole one-point carrier in dimension
zero. -/
public theorem ball_open {dimension : Nat} (center : carrier dimension)
    (radius : selection.Carrier) : IsOpen (ball center radius) := by
  intro point inside
  by_cases positive : lt zero radius
  · exact ball_is_open center positive point inside
  · refine ⟨one, one_positive, fun other _ coordinate => ?_⟩
    exact False.elim
      (positive (lt_of_le_of_lt (abs_nonnegative _) (inside coordinate)))

/-- The zeros of one constraint inside a rational coordinate ball of its
domain, kept only when the constraint does not vanish on the whole ball. -/
private def constraintExceptions {dimension : Nat}
    (region : Set (carrier dimension))
    (constraint : carrier dimension → selection.Carrier)
    (centerCode radiusCode : Nat) : Set (carrier dimension) :=
  fun point =>
    let center := rationalCenter dimension centerCode
    let radius := rationalBasis radiusCode
    (∀ other, ball center radius other → region other) ∧
      ¬(∀ other, ball center radius other → constraint other = zero) ∧
      ball center radius point ∧ constraint point = zero

private theorem constraintExceptions_null {dimension : Nat}
    {measure : Measure (vectorBorel dimension)}
    (nullZeros : NullAnalyticZeros measure)
    {region : Set (carrier dimension)}
    {constraint : carrier dimension → selection.Carrier}
    (analytic : AnalyticOn region constraint)
    (centerCode radiusCode : Nat) :
    measure.NullSet
      (constraintExceptions region constraint centerCode radiusCode) := by
  classical
  let center := rationalCenter dimension centerCode
  let radius := rationalBasis radiusCode
  by_cases within : ∀ other, ball center radius other → region other
  · by_cases vanish : ∀ other, ball center radius other → constraint other = zero
    · apply Measure.NullSet.mono (Measure.null_empty _)
      intro point member
      exact member.2.1 vanish
    · have analyticBall : AnalyticOn (ball center radius) constraint :=
        analytic_on_open_subset analytic (ball_open center radius) within
      rcases nullZeros center radius constraint analyticBall with allZero | null
      · exact False.elim (vanish allZero)
      · apply null.mono
        intro point member
        exact ⟨member.2.2.1, member.2.2.2⟩
  · apply Measure.NullSet.mono (Measure.null_empty _)
    intro point member
    exact within member.1

private theorem common_radius {dimension : Nat} {point : carrier dimension}
    {α : Type} (items : List α) (property : α → carrier dimension → Prop)
    (each : ∀ item, item ∈ items → ∃ radius, lt zero radius ∧
      ∀ other, ball point radius other → property item other) :
    ∃ radius, lt zero radius ∧
      ∀ other, ball point radius other →
        ∀ item, item ∈ items → property item other := by
  induction items with
  | nil =>
      exact ⟨one, one_positive, fun _ _ item member =>
        False.elim (List.not_mem_nil member)⟩
  | cons first rest induction =>
      rcases each first List.mem_cons_self with ⟨firstRadius, firstPositive, firstNear⟩
      rcases induction (fun item member => each item (List.mem_cons_of_mem _ member))
        with ⟨restRadius, restPositive, restNear⟩
      rcases small_positive firstPositive restPositive with
        ⟨radius, positive, belowFirst, belowRest⟩
      refine ⟨radius, positive, fun other inside item member => ?_⟩
      rcases List.mem_cons.mp member with equal | later
      · rw [equal]
        exact firstNear other (ball_mono belowFirst inside)
      · exact restNear other (ball_mono belowRest inside) item later

private theorem negative_near {dimension : Nat}
    {region : Set (carrier dimension)}
    {constraint : carrier dimension → selection.Carrier}
    (analytic : AnalyticOn region constraint)
    {point : carrier dimension} (member : region point)
    (negative : lt (constraint point) zero) :
    ∃ radius, lt zero radius ∧
      ∀ other, ball point radius other → le (constraint other) zero := by
  have size : lt zero (abs (constraint point)) :=
    abs_positive_of_nonzero (fun equal => negative.2 (by rw [equal]; exact le_refl zero))
  rcases analytic_on_continuous_at analytic point member _ size with
    ⟨radius, positive, close⟩
  refine ⟨radius, positive, fun other inside => ?_⟩
  have upper := (abs_lt.mp (close other inside)).2
  rw [abs_of_nonpositive (le_of_lt negative)] at upper
  have shifted := add_lt_add_right (constraint point) upper
  rw [sub_add_cancel, add_comm (neg (constraint point)), add_neg] at shifted
  exact le_of_lt shifted

/-- The analytic system chosen for one piece: its open domain and
constraints. -/
private def pieceRegion {source target : Nat} {domain : Set (carrier source)}
    {function : carrier source → carrier target}
    (representation : PAPRepresentation domain function) (index : Nat) :
    Set (carrier source) :=
  Classical.choose (representation.analytic index)

private def pieceConstraints {source target : Nat}
    {domain : Set (carrier source)}
    {function : carrier source → carrier target}
    (representation : PAPRepresentation domain function) (index : Nat) :
    List (carrier source → selection.Carrier) :=
  Classical.choose (Classical.choose_spec (representation.analytic index))

private theorem piece_system {source target : Nat}
    {domain : Set (carrier source)}
    {function : carrier source → carrier target}
    (representation : PAPRepresentation domain function) (index : Nat) :
    IsOpen (pieceRegion representation index) ∧
      (∀ constraint, constraint ∈ pieceConstraints representation index →
        AnalyticOn (pieceRegion representation index) constraint) ∧
      ∀ point, representation.pieces index point ↔
        pieceRegion representation index point ∧
          ∀ constraint, constraint ∈ pieceConstraints representation index →
            le (constraint point) zero :=
  Classical.choose_spec (Classical.choose_spec (representation.analytic index))

/-- The countable union of constraint exceptions of a representation. -/
private def exceptions {source target : Nat} {domain : Set (carrier source)}
    {function : carrier source → carrier target}
    (representation : PAPRepresentation domain function) :
    Set (carrier source) :=
  Set.iUnion fun index => Set.iUnion fun centerCode =>
    Set.iUnion fun radiusCode => fun point =>
      ∃ constraint, constraint ∈ pieceConstraints representation index ∧
        constraintExceptions (pieceRegion representation index) constraint
          centerCode radiusCode point

private theorem exceptions_null {source target : Nat}
    {domain : Set (carrier source)}
    {function : carrier source → carrier target}
    (representation : PAPRepresentation domain function)
    {measure : Measure (vectorBorel source)}
    (nullZeros : NullAnalyticZeros measure) :
    measure.NullSet (exceptions representation) := by
  apply Measure.NullSet.iUnion
  intro index
  apply Measure.NullSet.iUnion
  intro centerCode
  apply Measure.NullSet.iUnion
  intro radiusCode
  apply null_of_list
  intro constraint member
  exact constraintExceptions_null nullZeros
    ((piece_system representation index).2.1 constraint member)
    centerCode radiusCode

/-- Off the exceptions, a point of a piece has a neighborhood inside the
piece. -/
private theorem piece_neighborhood {source target : Nat}
    {domain : Set (carrier source)}
    {function : carrier source → carrier target}
    (representation : PAPRepresentation domain function)
    {index : Nat} {point : carrier source}
    (member : representation.pieces index point)
    (regular : ¬exceptions representation point) :
    ∃ radius, lt zero radius ∧
      ∀ other, ball point radius other → representation.pieces index other := by
  classical
  rcases piece_system representation index with ⟨openRegion, analytic, character⟩
  rcases (character point).mp member with ⟨inRegion, bounded⟩
  have each : ∀ constraint, constraint ∈ pieceConstraints representation index →
      ∃ radius, lt zero radius ∧
        ∀ other, ball point radius other → le (constraint other) zero := by
    intro constraint constraintMember
    by_cases negative : lt (constraint point) zero
    · exact negative_near (analytic constraint constraintMember) inRegion negative
    · have vanished : constraint point = zero :=
        le_antisymm (bounded constraint constraintMember)
          (Classical.byContradiction fun failure =>
            negative ⟨bounded constraint constraintMember, failure⟩)
      rcases exists_rational_ball_inside openRegion inRegion with
        ⟨centerCode, radiusCode, pointInside, within⟩
      have vanish : ∀ other, ball (rationalCenter source centerCode)
          (rationalBasis radiusCode) other → constraint other = zero := by
        apply Classical.byContradiction
        intro failure
        exact regular ⟨index, centerCode, radiusCode, constraint,
          constraintMember, within, failure, pointInside, vanished⟩
      rcases ball_open _ _ point pointInside with ⟨radius, positive, near⟩
      exact ⟨radius, positive, fun other inside =>
        le_of_equal (vanish other (near other inside))⟩
  rcases common_radius _
    (fun (constraint : carrier source → selection.Carrier) other =>
      le (constraint other) zero)
    each with ⟨constraintRadius, constraintPositive, constraintNear⟩
  rcases openRegion point inRegion with ⟨regionRadius, regionPositive, regionNear⟩
  rcases small_positive constraintPositive regionPositive with
    ⟨radius, positive, belowConstraint, belowRegion⟩
  refine ⟨radius, positive, fun other inside => ?_⟩
  exact (character other).mpr ⟨regionNear other (ball_mono belowRegion inside),
    constraintNear other (ball_mono belowConstraint inside)⟩

/-- Almost everywhere on its domain, a map with a chosen PAP representation
is defined on a neighborhood and has every coordinate derivative, and each
equals the representation's intensional derivative. The measure is any one
that makes nonvanishing analytic zero sets null. -/
public theorem PAPRepresentation.intensionalDerivative_ae
    {source target : Nat} {domain : Set (carrier source)}
    {function : carrier source → carrier target}
    (representation : PAPRepresentation domain function)
    {measure : Measure (vectorBorel source)}
    (nullZeros : NullAnalyticZeros measure) :
    measure.AE (fun point => domain point →
      (∃ radius, lt zero radius ∧
        ∀ other, ball point radius other → domain other) ∧
      ∀ input output, HasDerivative
        (coordinateSliceAt (fun other => function other output) point input)
        zero (representation.intensionalDerivative point input output)) := by
  apply (exceptions_null representation nullZeros).mono
  intro point failure
  apply Classical.byContradiction
  intro regular
  apply failure
  intro member
  rw [representation.cover] at member
  rcases member with ⟨index, inPiece⟩
  rcases piece_neighborhood representation inPiece regular with
    ⟨pieceRadius, piecePositive, pieceNear⟩
  rcases representation.open_regions index point
    (representation.pieces_in_regions index inPiece) with
    ⟨witnessRadius, witnessPositive, _⟩
  refine ⟨⟨pieceRadius, piecePositive, fun other inside => ?_⟩, ?_⟩
  · rw [representation.cover]
    exact ⟨index, pieceNear other inside⟩
  · intro input output
    rw [representation.intensionalDerivative_on_piece index point inPiece
      input output]
    have differentiable := analytic_has_partialDerivativeAt
      (representation.analytic_witnesses index output)
      (representation.pieces_in_regions index inPiece) input
    refine HasDerivative.congr_near ?_ differentiable
    refine ⟨pieceRadius, piecePositive, fun step small => ?_⟩
    show coordinateSliceAt (fun nearby => representation.witnesses index nearby output)
        point input (add zero step) =
      coordinateSliceAt (fun other => function other output) point input
        (add zero step)
    rw [zero_add]
    unfold coordinateSliceAt
    exact (congrFun (representation.agrees index _
      (pieceNear _ (ball_coordinate_step piecePositive small input))) output).symm

/-- The partial-map form: almost everywhere on the domain, the map's total
extension has the intensional derivative as its coordinate derivatives, and
the domain contains a neighborhood of the point. -/
public theorem PartialPAP.intensionalDerivative_ae {source target : Nat}
    (map : PartialPAP source target)
    {measure : Measure (vectorBorel source)}
    (nullZeros : NullAnalyticZeros measure) :
    measure.AE (fun point => map.domain point →
      (∃ radius, lt zero radius ∧
        ∀ other, ball point radius other → map.domain other) ∧
      ∀ input output, HasDerivative
        (coordinateSliceAt (fun other => map.totalize other output) point input)
        zero (map.intensionalDerivative point input output)) :=
  map.representation.intensionalDerivative_ae nullZeros

end

end Problib.Analysis.PAP
