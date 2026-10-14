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

@[expose, implicit_reducible] public def carrier (dimension : Nat) : Type :=
  Fin dimension → selection.Carrier

@[expose] public def zeroVector (dimension : Nat) : carrier dimension :=
  fun _ => zero

@[expose] public def addVector {dimension : Nat}
    (left right : carrier dimension) : carrier dimension :=
  fun coordinate => add (left coordinate) (right coordinate)

@[expose] public def subVector {dimension : Nat}
    (left right : carrier dimension) : carrier dimension :=
  fun coordinate => sub (left coordinate) (right coordinate)

/-- Every coordinate multiplied by one scalar. -/
@[expose] public def scaleVector {dimension : Nat}
    (scalar : selection.Carrier) (value : carrier dimension) : carrier dimension :=
  fun coordinate => mul scalar (value coordinate)

/-- The larger of two sealed reals, used only to construct a finite maximum. -/
@[expose] public noncomputable def maxReal (left right : selection.Carrier) :
    selection.Carrier := by
  classical
  exact if le left right then right else left

public theorem le_max_left (left right : selection.Carrier) :
    le left (maxReal left right) := by
  classical
  by_cases ordered : le left right
  · rw [maxReal, ite_eq_left ordered]
    exact ordered
  · rw [maxReal, ite_eq_right ordered]
    exact le_refl _

public theorem le_max_right (left right : selection.Carrier) :
    le right (maxReal left right) := by
  classical
  by_cases ordered : le left right
  · rw [maxReal, ite_eq_left ordered]
    exact le_refl _
  · rw [maxReal, ite_eq_right ordered]
    exact le_of_lt (lt_of_not_le ordered)

public theorem max_le {left right upper : selection.Carrier}
    (leftBound : le left upper) (rightBound : le right upper) :
    le (maxReal left right) upper := by
  classical
  by_cases ordered : le left right
  · rwa [maxReal, ite_eq_left ordered]
  · rwa [maxReal, ite_eq_right ordered]

public theorem max_lt {left right upper : selection.Carrier}
    (leftBound : lt left upper) (rightBound : lt right upper) :
    lt (maxReal left right) upper := by
  classical
  by_cases ordered : le left right
  · rwa [maxReal, ite_eq_left ordered]
  · rwa [maxReal, ite_eq_right ordered]

/-- Fold the magnitudes of a finite list of coordinates into a running bound. -/
@[expose] public def foldMax {dimension : Nat} (value : carrier dimension) :
    List (Fin dimension) → selection.Carrier → selection.Carrier
  | [], base => base
  | coordinate :: rest, base =>
      foldMax value rest (maxReal base (abs (value coordinate)))

public theorem le_foldMax {dimension : Nat} (value : carrier dimension)
    (indices : List (Fin dimension)) (base : selection.Carrier) :
    le base (foldMax value indices base) := by
  induction indices generalizing base with
  | nil => exact le_refl _
  | cons coordinate rest induction =>
      exact le_trans (le_max_left base (abs (value coordinate)))
        (induction (maxReal base (abs (value coordinate))))

public theorem member_le_foldMax {dimension : Nat} (value : carrier dimension)
    (indices : List (Fin dimension)) (base : selection.Carrier)
    {coordinate : Fin dimension} (member : coordinate ∈ indices) :
    le (abs (value coordinate)) (foldMax value indices base) := by
  induction indices generalizing base with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons head rest induction =>
      rcases List.mem_cons.mp member with equal | inRest
      · subst coordinate
        exact le_trans (le_max_right base (abs (value head)))
          (le_foldMax value rest (maxReal base (abs (value head))))
      · exact induction (maxReal base (abs (value head))) inRest

public theorem foldMax_le {dimension : Nat} (value : carrier dimension)
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

public theorem supNorm_nonnegative {dimension : Nat} (value : carrier dimension) :
    le zero (supNorm value) :=
  le_foldMax value (List.finRange dimension) zero

public theorem coordinate_le_supNorm {dimension : Nat} (value : carrier dimension)
    (coordinate : Fin dimension) :
    le (abs (value coordinate)) (supNorm value) :=
  member_le_foldMax value (List.finRange dimension) zero
    (List.mem_finRange coordinate)

public theorem supNorm_le {dimension : Nat} {value : carrier dimension}
    {upper : selection.Carrier} (nonnegative : le zero upper)
    (coordinates : ∀ coordinate, le (abs (value coordinate)) upper) :
    le (supNorm value) upper := by
  apply foldMax_le value (List.finRange dimension) nonnegative
  intro coordinate _
  exact coordinates coordinate

public theorem supNorm_lt {dimension : Nat} {value : carrier dimension}
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

public theorem supNorm_triangle {dimension : Nat}
    (left right : carrier dimension) :
    le (supNorm (addVector left right))
      (add (supNorm left) (supNorm right)) := by
  apply supNorm_le
    (add_nonnegative (supNorm_nonnegative left) (supNorm_nonnegative right))
  intro coordinate
  exact le_trans (abs_add_le (left coordinate) (right coordinate))
    (add_le_add (coordinate_le_supNorm left coordinate)
      (coordinate_le_supNorm right coordinate))

/-- Scaling a vector scales its norm by the scalar's magnitude. -/
public theorem supNorm_scaleVector {dimension : Nat} (scalar : selection.Carrier)
    (value : carrier dimension) :
    supNorm (scaleVector scalar value) = mul (abs scalar) (supNorm value) := by
  classical
  have upper : le (supNorm (scaleVector scalar value))
      (mul (abs scalar) (supNorm value)) := by
    apply supNorm_le (mul_nonnegative (abs_nonnegative scalar) (supNorm_nonnegative value))
    intro coordinate
    show le (abs (mul scalar (value coordinate))) _
    rw [abs_mul]
    exact mul_le_mul_nonnegative_left (coordinate_le_supNorm value coordinate)
      (abs_nonnegative scalar)
  apply le_antisymm upper
  by_cases vanishes : scalar = zero
  · rw [vanishes, abs_zero, zero_mul]
    exact supNorm_nonnegative _
  · have positive := abs_positive_of_nonzero vanishes
    have nonzero := nonzero_of_positive positive
    have inverseNonnegative := le_of_lt (inverse_of_positive_positive positive)
    have lower : le (supNorm value)
        (mul (inverse (abs scalar)) (supNorm (scaleVector scalar value))) := by
      apply supNorm_le (mul_nonnegative inverseNonnegative (supNorm_nonnegative _))
      intro coordinate
      have bound := mul_le_mul_nonnegative_left
        (coordinate_le_supNorm (scaleVector scalar value) coordinate) inverseNonnegative
      rwa [show abs (scaleVector scalar value coordinate) =
          mul (abs scalar) (abs (value coordinate)) from abs_mul _ _,
        ← mul_assoc, inverse_mul_cancel nonzero, one_mul] at bound
    have raised := mul_le_mul_nonnegative_left lower (abs_nonnegative scalar)
    rwa [← mul_assoc, mul_inverse_cancel nonzero, one_mul] at raised

/-- A vector is at distance zero from itself. -/
public theorem supNorm_sub_self {dimension : Nat} (value : carrier dimension) :
    supNorm (subVector value value) = zero := by
  apply le_antisymm _ (supNorm_nonnegative _)
  apply supNorm_le (le_refl zero)
  intro coordinate
  show le (abs (sub (value coordinate) (value coordinate))) zero
  rw [sub_self, abs_zero]
  exact le_refl zero

/-- Distance is symmetric. -/
public theorem supNorm_sub_comm {dimension : Nat} (left right : carrier dimension) :
    supNorm (subVector left right) = supNorm (subVector right left) := by
  have side (first second : carrier dimension) :
      le (supNorm (subVector first second)) (supNorm (subVector second first)) := by
    apply supNorm_le (supNorm_nonnegative _)
    intro coordinate
    show le (abs (sub (first coordinate) (second coordinate))) _
    rw [abs_sub_comm]
    exact coordinate_le_supNorm (subVector second first) coordinate
  exact le_antisymm (side left right) (side right left)

/-- The triangle inequality for distances. -/
public theorem supNorm_sub_triangle {dimension : Nat}
    (first middle last : carrier dimension) :
    le (supNorm (subVector first last))
      (add (supNorm (subVector first middle)) (supNorm (subVector middle last))) := by
  have split : subVector first last =
      addVector (subVector first middle) (subVector middle last) := by
    funext coordinate
    exact (sub_add_sub _ _ _).symm
  rw [split]
  exact supNorm_triangle _ _

/-- Subtracting the zero vector changes nothing. -/
public theorem subVector_zero {dimension : Nat} (value : carrier dimension) :
    subVector value (zeroVector dimension) = value := by
  funext coordinate
  exact sub_zero _

/-- The norm of a difference is at most the sum of the norms. -/
public theorem supNorm_sub_le_add {dimension : Nat} (left right : carrier dimension) :
    le (supNorm (subVector left right)) (add (supNorm left) (supNorm right)) := by
  apply supNorm_le (add_nonnegative (supNorm_nonnegative left) (supNorm_nonnegative right))
  intro coordinate
  show le (abs (sub (left coordinate) (right coordinate))) _
  rw [sub_eq_add_neg]
  refine le_trans (abs_add_le _ _) ?_
  rw [abs_neg]
  exact add_le_add (coordinate_le_supNorm left coordinate) (coordinate_le_supNorm right coordinate)

/-- Two vectors at distance at most zero are equal. -/
public theorem eq_of_supNorm_sub_nonpositive {dimension : Nat}
    {left right : carrier dimension}
    (vanishes : le (supNorm (subVector left right)) zero) : left = right := by
  funext coordinate
  have coordinateZero : abs (sub (left coordinate) (right coordinate)) = zero :=
    le_antisymm (le_trans (coordinate_le_supNorm (subVector left right) coordinate)
      vanishes) (abs_nonnegative _)
  rw [← add_sub_cancel (left coordinate) (right coordinate),
    abs_eq_zero_iff.mp coordinateZero, add_zero]

/-- Two vectors closer than every positive tolerance are equal. -/
public theorem eq_of_supNorm_sub_small {dimension : Nat}
    {left right : carrier dimension}
    (small : ∀ epsilon, lt zero epsilon →
      lt (supNorm (subVector left right)) epsilon) : left = right :=
  eq_of_supNorm_sub_nonpositive (le_of_forall_lt_add fun epsilon positive => by
    rw [zero_add]
    exact small epsilon positive)

@[expose, implicit_reducible] public def ball {dimension : Nat} (center : carrier dimension)
    (radius : selection.Carrier) : carrier dimension → Prop :=
  fun value => ∀ coordinate,
    lt (abs (sub (value coordinate) (center coordinate))) radius

public theorem ball_iff_supNorm {dimension : Nat} {center value : carrier dimension}
    {radius : selection.Carrier} (positive : lt zero radius) :
    ball center radius value ↔ lt (supNorm (subVector value center)) radius := by
  constructor
  · intro inside
    apply supNorm_lt positive
    exact inside
  · intro bounded coordinate
    exact lt_of_le_of_lt
      (coordinate_le_supNorm (subVector value center) coordinate) bounded

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
  have normInside := (ball_iff_supNorm positive).mp inside
  let gap := sub radius (supNorm (subVector point center))
  have gapPositive : lt zero gap := sub_positive_iff.mpr normInside
  refine ⟨gap, gapPositive, fun neighbor near => ?_⟩
  apply (ball_iff_supNorm positive).mpr
  have nearNorm := (ball_iff_supNorm gapPositive).mp near
  have split : subVector neighbor center =
      addVector (subVector neighbor point) (subVector point center) := by
    funext coordinate
    exact (sub_add_sub (neighbor coordinate) (point coordinate) (center coordinate)).symm
  rw [split]
  have triangle := supNorm_triangle (subVector neighbor point) (subVector point center)
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

@[expose] public def ConvergesTo {dimension : Nat}
    (values : Nat → carrier dimension) (limit : carrier dimension) : Prop :=
  ∀ radius : selection.Carrier, lt zero radius →
    ∃ stage : Nat, ∀ index : Nat, stage ≤ index → ball limit radius (values index)

private def indexMax {dimension : Nat} (stages : Fin dimension → Nat) :
    List (Fin dimension) → Nat → Nat
  | [], base => base
  | coordinate :: rest, base => indexMax stages rest (max base (stages coordinate))

private theorem base_le_indexMax {dimension : Nat} (stages : Fin dimension → Nat)
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
          (base_le_indexMax stages rest (max base (stages head)))
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

end

end Problib.Analysis.Real.FiniteVector
