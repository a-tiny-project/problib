module

public import Problib.Analysis.Real.Sequence
public import Problib.FiniteEnumeration

/-! Finite-dimensional real vectors and their common-radius neighborhoods.

The radius is shared by every coordinate. For a finite carrier this is the
usual sup-norm neighborhood, without selecting a maximum before it is needed.
The carrier is problib's sealed real, not Lean's built-in `Real`.
-/

set_option autoImplicit false

namespace Problib.Analysis.Real.FiniteVector

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real

noncomputable section

@[expose] public def carrier (dimension : Nat) : Type :=
  Fin dimension → selection.Carrier

@[expose] public def zeroVector (dimension : Nat) : carrier dimension :=
  fun _ => zero

@[expose] public def addVector {dimension : Nat}
    (left right : carrier dimension) : carrier dimension :=
  fun coordinate => add (left coordinate) (right coordinate)

@[expose] public def subVector {dimension : Nat}
    (left right : carrier dimension) : carrier dimension :=
  fun coordinate => sub (left coordinate) (right coordinate)

@[expose] public def negVector {dimension : Nat}
    (value : carrier dimension) : carrier dimension :=
  fun coordinate => neg (value coordinate)

@[expose] public def scaleVector {dimension : Nat} (factor : selection.Carrier)
    (value : carrier dimension) : carrier dimension :=
  fun coordinate => mul factor (value coordinate)

/-- The larger of two sealed reals, used only to construct a finite maximum. -/
@[expose] public noncomputable def maxReal (left right : selection.Carrier) :
    selection.Carrier := by
  classical
  exact if le left right then right else left

public theorem le_max_left (left right : selection.Carrier) :
    le left (maxReal left right) := by
  classical
  by_cases ordered : le left right
  · rw [maxReal, if_pos ordered]
    exact ordered
  · rw [maxReal, if_neg ordered]
    exact le_refl _

public theorem le_max_right (left right : selection.Carrier) :
    le right (maxReal left right) := by
  classical
  by_cases ordered : le left right
  · rw [maxReal, if_pos ordered]
    exact le_refl _
  · rw [maxReal, if_neg ordered]
    exact le_of_lt (lt_of_not_le ordered)

public theorem max_le {left right upper : selection.Carrier}
    (leftBound : le left upper) (rightBound : le right upper) :
    le (maxReal left right) upper := by
  classical
  by_cases ordered : le left right
  · rwa [maxReal, if_pos ordered]
  · rwa [maxReal, if_neg ordered]

public theorem max_lt {left right upper : selection.Carrier}
    (leftBound : lt left upper) (rightBound : lt right upper) :
    lt (maxReal left right) upper := by
  classical
  by_cases ordered : le left right
  · rwa [maxReal, if_pos ordered]
  · rwa [maxReal, if_neg ordered]

/-- Fold the magnitudes of a finite list of coordinates into a running bound. -/
@[expose] public def foldMax {dimension : Nat} (value : carrier dimension) :
    List (Fin dimension) → selection.Carrier → selection.Carrier
  | [], base => base
  | coordinate :: rest, base =>
      foldMax value rest (maxReal base (abs (value coordinate)))

public theorem le_fold_max {dimension : Nat} (value : carrier dimension)
    (indices : List (Fin dimension)) (base : selection.Carrier) :
    le base (foldMax value indices base) := by
  induction indices generalizing base with
  | nil => exact le_refl _
  | cons coordinate rest induction =>
      exact le_trans (le_max_left base (abs (value coordinate)))
        (induction (maxReal base (abs (value coordinate))))

public theorem member_le_fold_max {dimension : Nat} (value : carrier dimension)
    (indices : List (Fin dimension)) (base : selection.Carrier)
    {coordinate : Fin dimension} (member : coordinate ∈ indices) :
    le (abs (value coordinate)) (foldMax value indices base) := by
  induction indices generalizing base with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons head rest induction =>
      rcases List.mem_cons.mp member with equal | inRest
      · subst coordinate
        exact le_trans (le_max_right base (abs (value head)))
          (le_fold_max value rest (maxReal base (abs (value head))))
      · exact induction (maxReal base (abs (value head))) inRest

public theorem fold_max_le {dimension : Nat} (value : carrier dimension)
    (indices : List (Fin dimension)) {base upper : selection.Carrier}
    (baseBound : le base upper)
    (coordinateBound : ∀ coordinate, coordinate ∈ indices →
      le (abs (value coordinate)) upper) :
    le (foldMax value indices base) upper := by
  induction indices generalizing base with
  | nil => exact baseBound
  | cons head rest induction =>
      apply induction
      · exact max_le baseBound (coordinateBound head (List.mem_cons_self))
      · intro coordinate member
        exact coordinateBound coordinate (List.mem_cons_of_mem head member)

@[expose] public def supNorm {dimension : Nat} (value : carrier dimension) :
    selection.Carrier :=
  foldMax value (List.finRange dimension) zero

public theorem sup_norm_nonnegative {dimension : Nat} (value : carrier dimension) :
    le zero (supNorm value) :=
  le_fold_max value (List.finRange dimension) zero

public theorem coordinate_le_sup_norm {dimension : Nat} (value : carrier dimension)
    (coordinate : Fin dimension) :
    le (abs (value coordinate)) (supNorm value) :=
  member_le_fold_max value (List.finRange dimension) zero
    (List.mem_finRange coordinate)

public theorem sup_norm_le {dimension : Nat} {value : carrier dimension}
    {upper : selection.Carrier} (nonnegative : le zero upper)
    (coordinates : ∀ coordinate, le (abs (value coordinate)) upper) :
    le (supNorm value) upper := by
  apply fold_max_le value (List.finRange dimension) nonnegative
  intro coordinate _
  exact coordinates coordinate

public theorem sup_norm_lt {dimension : Nat} {value : carrier dimension}
    {upper : selection.Carrier} (positive : lt zero upper)
    (coordinates : ∀ coordinate, lt (abs (value coordinate)) upper) :
    lt (supNorm value) upper := by
  have go (indices : List (Fin dimension)) (base : selection.Carrier)
      (baseBelow : lt base upper) : lt (foldMax value indices base) upper := by
    induction indices generalizing base with
    | nil => exact baseBelow
    | cons coordinate rest induction =>
        exact induction (maxReal base (abs (value coordinate)))
          (max_lt baseBelow (coordinates coordinate))
  exact go (List.finRange dimension) zero positive

public theorem sup_norm_triangle {dimension : Nat}
    (left right : carrier dimension) :
    le (supNorm (addVector left right))
      (add (supNorm left) (supNorm right)) := by
  apply sup_norm_le
    (add_nonnegative (sup_norm_nonnegative left) (sup_norm_nonnegative right))
  intro coordinate
  exact le_trans (abs_add_le (left coordinate) (right coordinate))
    (add_le_add (coordinate_le_sup_norm left coordinate)
      (coordinate_le_sup_norm right coordinate))

@[expose] public def ball {dimension : Nat} (center : carrier dimension)
    (radius : selection.Carrier) : carrier dimension → Prop :=
  fun value => ∀ coordinate,
    lt (abs (sub (value coordinate) (center coordinate))) radius

public theorem ball_iff_sup_norm {dimension : Nat} {center value : carrier dimension}
    {radius : selection.Carrier} (positive : lt zero radius) :
    ball center radius value ↔ lt (supNorm (subVector value center)) radius := by
  constructor
  · intro inside
    apply sup_norm_lt positive
    exact inside
  · intro bounded coordinate
    exact lt_of_le_of_lt
      (coordinate_le_sup_norm (subVector value center) coordinate) bounded

@[expose] public def IsOpen {dimension : Nat}
    (region : carrier dimension → Prop) : Prop :=
  ∀ point, region point →
    ∃ radius : selection.Carrier,
      lt zero radius ∧
        ∀ neighbor, ball point radius neighbor → region neighbor

/-- Every positive-radius ball is open in the common-radius topology. -/
public theorem ball_is_open {dimension : Nat} (center : carrier dimension)
    {radius : selection.Carrier} (positive : lt zero radius) :
    IsOpen (ball center radius) := by
  intro point inside
  have normInside := (ball_iff_sup_norm positive).mp inside
  let gap := sub radius (supNorm (subVector point center))
  have gapPositive : lt zero gap := sub_positive_iff.mpr normInside
  refine ⟨gap, gapPositive, fun neighbor near => ?_⟩
  apply (ball_iff_sup_norm positive).mpr
  have nearNorm := (ball_iff_sup_norm gapPositive).mp near
  have split : subVector neighbor center =
      addVector (subVector neighbor point) (subVector point center) := by
    funext coordinate
    exact (sub_add_sub (neighbor coordinate) (point coordinate) (center coordinate)).symm
  rw [split]
  have triangle := sup_norm_triangle (subVector neighbor point) (subVector point center)
  have shifted := add_lt_add_right (supNorm (subVector point center)) nearNorm
  have rightEqual : add gap (supNorm (subVector point center)) = radius := by
    exact sub_add_cancel _ _
  rw [rightEqual] at shifted
  exact lt_of_le_of_lt triangle shifted

public theorem ball_center {dimension : Nat} (center : carrier dimension)
    {radius : selection.Carrier} (positive : lt zero radius) :
    ball center radius center := by
  intro coordinate
  rw [sub_self, abs_zero]
  exact positive

public theorem ball_symm {dimension : Nat} {left right : carrier dimension}
    {radius : selection.Carrier} (inside : ball left radius right) :
    ball right radius left := by
  intro coordinate
  rw [abs_sub_comm]
  exact inside coordinate

public theorem ball_mono {dimension : Nat} {center value : carrier dimension}
    {small large : selection.Carrier} (bounded : le small large)
    (inside : ball center small value) : ball center large value := by
  intro coordinate
  exact lt_of_lt_of_le (inside coordinate) bounded

public theorem is_open_univ (dimension : Nat) :
    IsOpen (fun _ : carrier dimension => True) := by
  intro point _
  exact ⟨one, one_positive, fun _ _ => True.intro⟩

public theorem is_open_empty (dimension : Nat) :
    IsOpen (fun _ : carrier dimension => False) := by
  intro _ impossible
  exact False.elim impossible

public theorem is_open_inter {dimension : Nat}
    {left right : carrier dimension → Prop}
    (leftOpen : IsOpen left) (rightOpen : IsOpen right) :
    IsOpen (fun point => left point ∧ right point) := by
  intro point member
  rcases leftOpen point member.left with ⟨leftRadius, leftPositive, leftBall⟩
  rcases rightOpen point member.right with ⟨rightRadius, rightPositive, rightBall⟩
  rcases small_positive leftPositive rightPositive with
    ⟨radius, positive, leLeft, leRight⟩
  refine ⟨radius, positive, fun neighbor inside => ?_⟩
  exact ⟨leftBall neighbor (ball_mono leLeft inside),
    rightBall neighbor (ball_mono leRight inside)⟩

public theorem is_open_iunion {dimension : Nat}
    {regions : Nat → carrier dimension → Prop}
    (eachOpen : ∀ index, IsOpen (regions index)) :
    IsOpen (fun point => ∃ index, regions index point) := by
  intro point member
  rcases member with ⟨index, indexMember⟩
  rcases eachOpen index point indexMember with ⟨radius, positive, around⟩
  exact ⟨radius, positive, fun neighbor inside => ⟨index, around neighbor inside⟩⟩

@[expose] public def ConvergesTo {dimension : Nat}
    (values : Nat → carrier dimension) (limit : carrier dimension) : Prop :=
  ∀ radius : selection.Carrier, lt zero radius →
    ∃ stage : Nat, ∀ index : Nat, stage ≤ index → ball limit radius (values index)

public theorem converges_to_coordinate {dimension : Nat}
    {values : Nat → carrier dimension} {limit : carrier dimension}
    (converges : ConvergesTo values limit) (coordinate : Fin dimension) :
    Problib.Analysis.Real.ConvergesTo
      (fun index => values index coordinate) (limit coordinate) := by
  intro radius positive
  rcases converges radius positive with ⟨stage, near⟩
  exact ⟨stage, fun index later => near index later coordinate⟩

private def indexMax {dimension : Nat} (stages : Fin dimension → Nat) :
    List (Fin dimension) → Nat → Nat
  | [], base => base
  | coordinate :: rest, base => indexMax stages rest (max base (stages coordinate))

private theorem base_le_index_max {dimension : Nat} (stages : Fin dimension → Nat)
    (indices : List (Fin dimension)) (base : Nat) :
    base ≤ indexMax stages indices base := by
  induction indices generalizing base with
  | nil => exact Nat.le_refl _
  | cons head rest induction =>
      exact Nat.le_trans (Nat.le_max_left _ _)
        (induction (max base (stages head)))

private theorem index_le_max {dimension : Nat} (stages : Fin dimension → Nat)
    (indices : List (Fin dimension)) (base : Nat)
    {coordinate : Fin dimension} (member : coordinate ∈ indices) :
    stages coordinate ≤ indexMax stages indices base := by
  induction indices generalizing base with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons head rest induction =>
      rcases List.mem_cons.mp member with equal | inRest
      · subst coordinate
        exact Nat.le_trans (Nat.le_max_right _ _)
          (base_le_index_max stages rest (max base (stages head)))
      · exact induction (max base (stages head)) inRest

public theorem converges_to_of_coordinates {dimension : Nat}
    {values : Nat → carrier dimension} {limit : carrier dimension}
    (coordinates : ∀ coordinate : Fin dimension,
      Problib.Analysis.Real.ConvergesTo
        (fun index => values index coordinate) (limit coordinate)) :
    ConvergesTo values limit := by
  classical
  intro radius positive
  let stages : Fin dimension → Nat := fun coordinate =>
    Classical.choose (coordinates coordinate radius positive)
  let stage := indexMax stages (List.finRange dimension) 0
  refine ⟨stage, fun index later coordinate => ?_⟩
  have coordinateStage : stages coordinate ≤ stage :=
    index_le_max stages (List.finRange dimension) 0
      (List.mem_finRange coordinate)
  exact (Classical.choose_spec (coordinates coordinate radius positive))
    index (Nat.le_trans coordinateStage later)

@[expose] public def ContinuousAt {source target : Nat}
    (function : carrier source → carrier target)
    (point : carrier source) : Prop :=
  ∀ radius : selection.Carrier, lt zero radius →
    ∃ delta : selection.Carrier,
      lt zero delta ∧
        ∀ neighbor, ball point delta neighbor →
          ball (function point) radius (function neighbor)

public theorem continuous_at_id {dimension : Nat} (point : carrier dimension) :
    ContinuousAt (fun value => value) point := by
  intro radius positive
  exact ⟨radius, positive, fun _ inside => inside⟩

public theorem continuous_at_const {source target : Nat}
    (value : carrier target) (point : carrier source) :
    ContinuousAt (fun _ => value) point := by
  intro radius positive
  exact ⟨one, one_positive,
    fun _ _ => ball_center value positive⟩

public theorem continuous_at_comp {source middle target : Nat}
    {first : carrier source → carrier middle}
    {second : carrier middle → carrier target} {point : carrier source}
    (firstContinuous : ContinuousAt first point)
    (secondContinuous : ContinuousAt second (first point)) :
    ContinuousAt (fun value => second (first value)) point := by
  intro radius positive
  rcases secondContinuous radius positive with ⟨middleRadius, middlePositive, secondNear⟩
  rcases firstContinuous middleRadius middlePositive with
    ⟨sourceRadius, sourcePositive, firstNear⟩
  exact ⟨sourceRadius, sourcePositive,
    fun neighbor inside => secondNear (first neighbor) (firstNear neighbor inside)⟩

public theorem continuous_at_add {source target : Nat}
    {first second : carrier source → carrier target} {point : carrier source}
    (firstContinuous : ContinuousAt first point)
    (secondContinuous : ContinuousAt second point) :
    ContinuousAt (fun value => addVector (first value) (second value)) point := by
  intro radius positive
  have halfPositive := half_positive positive
  rcases firstContinuous _ halfPositive with ⟨firstDelta, firstPositive, firstNear⟩
  rcases secondContinuous _ halfPositive with ⟨secondDelta, secondPositive, secondNear⟩
  rcases small_positive firstPositive secondPositive with
    ⟨delta, deltaPositive, deltaFirst, deltaSecond⟩
  refine ⟨delta, deltaPositive, fun neighbor inside coordinate => ?_⟩
  have firstClose := firstNear neighbor (ball_mono deltaFirst inside) coordinate
  have secondClose := secondNear neighbor (ball_mono deltaSecond inside) coordinate
  have split : sub (add (first neighbor coordinate) (second neighbor coordinate))
      (add (first point coordinate) (second point coordinate)) =
      add (sub (first neighbor coordinate) (first point coordinate))
        (sub (second neighbor coordinate) (second point coordinate)) :=
    add_sub_add_comm _ _ _ _
  change lt (abs (sub
    (add (first neighbor coordinate) (second neighbor coordinate))
    (add (first point coordinate) (second point coordinate)))) radius
  rw [split]
  have triangle := abs_add_le
    (sub (first neighbor coordinate) (first point coordinate))
    (sub (second neighbor coordinate) (second point coordinate))
  have strict := add_lt_add firstClose secondClose
  rw [add_half] at strict
  exact lt_of_le_of_lt triangle strict

public theorem continuous_at_neg {source target : Nat}
    {function : carrier source → carrier target} {point : carrier source}
    (continuous : ContinuousAt function point) :
    ContinuousAt (fun value => negVector (function value)) point := by
  intro radius positive
  rcases continuous radius positive with ⟨delta, deltaPositive, near⟩
  refine ⟨delta, deltaPositive, fun neighbor inside coordinate => ?_⟩
  have split : sub (neg (function neighbor coordinate))
      (neg (function point coordinate)) =
      neg (sub (function neighbor coordinate) (function point coordinate)) := by
    rw [sub_eq_add_neg, sub_eq_add_neg, neg_add, neg_neg]
  change lt (abs (sub (neg (function neighbor coordinate))
    (neg (function point coordinate)))) radius
  rw [split, abs_neg]
  exact near neighbor inside coordinate

end

end Problib.Analysis.Real.FiniteVector
