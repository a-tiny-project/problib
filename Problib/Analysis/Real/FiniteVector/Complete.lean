module

public import Problib.Analysis.Real.Cauchy
public import Problib.Analysis.Real.FiniteVector

/-! Cauchy completeness of finite real vectors, and closed balls.

A sequence of vectors whose terms come within every tolerance of each other in
sup norm has coordinates that do the same, so each coordinate converges by the
completeness of the reals, and the coordinate limits assemble into a vector
limit. A closed ball keeps the limits of its sequences, which is what lets an
iteration that stays in the ball leave its limit there.
-/

set_option autoImplicit false

namespace Problib.Analysis.Real.FiniteVector

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real

noncomputable section

/-- A sequence of vectors whose terms come within every tolerance of each other
converges. -/
public theorem converges_of_cauchy {dimension : Nat} {values : Nat → carrier dimension}
    (cauchy : ∀ epsilon, lt zero epsilon → ∃ stage : Nat, ∀ first second,
      stage ≤ first → stage ≤ second →
        lt (supNorm (subVector (values first) (values second))) epsilon) :
    ∃ limit, ConvergesTo values limit := by
  have coordinates : ∀ coordinate : Fin dimension, ∃ limit,
      Problib.Analysis.Real.ConvergesTo (fun index => values index coordinate) limit := by
    intro coordinate
    apply cauchy_converges
    intro epsilon positive
    rcases cauchy epsilon positive with ⟨stage, close⟩
    exact ⟨stage, fun first second firstLater secondLater =>
      lt_of_le_of_lt (coordinate_le_supNorm (subVector (values first) (values second))
        coordinate) (close first second firstLater secondLater)⟩
  exact ⟨fun coordinate => Classical.choose (coordinates coordinate),
    converges_to_of_coordinates fun coordinate =>
      Classical.choose_spec (coordinates coordinate)⟩

/-- The vectors within `radius` of `center`, boundary included. -/
@[expose] public def closedBall {dimension : Nat} (center : carrier dimension)
    (radius : selection.Carrier) : carrier dimension → Prop :=
  fun value => le (supNorm (subVector value center)) radius

/-- A closed ball keeps the limit of a sequence inside it. -/
public theorem closedBall_limit {dimension : Nat} {center : carrier dimension}
    {radius : selection.Carrier} {values : Nat → carrier dimension}
    {limit : carrier dimension} (inside : ∀ index, closedBall center radius (values index))
    (converges : ConvergesTo values limit) : closedBall center radius limit := by
  apply le_of_forall_lt_add
  intro epsilon positive
  rcases converges epsilon positive with ⟨stage, close⟩
  have near : lt (supNorm (subVector limit (values stage))) epsilon := by
    rw [supNorm_sub_comm]
    exact (ball_iff_supNorm positive).mp (close stage (Nat.le_refl stage))
  refine lt_of_le_of_lt (supNorm_sub_triangle limit (values stage) center) ?_
  rw [add_comm radius]
  exact lt_of_lt_of_le (add_lt_add_right _ near) (add_le_add (le_refl _) (inside stage))

end

end Problib.Analysis.Real.FiniteVector
