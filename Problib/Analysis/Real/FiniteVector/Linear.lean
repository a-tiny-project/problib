module

public import Problib.Analysis.Real.FiniteVector
public import Problib.Real.Grind

/-! Bounded linear maps between finite real vector spaces.

A derivative of a map between vector spaces is a linear map, and every estimate
that reads one needs a bound on how far it stretches a vector. A
`BoundedLinear` is that map with its two linearity laws and a sup-norm bound.
It is a function, not a matrix: identity, composition and difference are built
from the laws alone, so the same structure serves every dimension. A matrix
enters by proving its action is one of these.
-/

set_option autoImplicit false

namespace Problib.Analysis.Real.FiniteVector

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real

noncomputable section

/-- A linear map between finite vector spaces, with a sup-norm bound. -/
public structure BoundedLinear (source target : Nat) where
  map : carrier source → carrier target
  additive : ∀ left right,
    map (addVector left right) = addVector (map left) (map right)
  homogeneous : ∀ scalar value,
    map (scaleVector scalar value) = scaleVector scalar (map value)
  bound : selection.Carrier
  boundNonnegative : le zero bound
  bounded : ∀ value, le (supNorm (map value)) (mul bound (supNorm value))

namespace BoundedLinear

/-- A linear map carries differences to differences. -/
public theorem map_sub {source target : Nat} (linear : BoundedLinear source target)
    (left right : carrier source) :
    linear.map (subVector left right) = subVector (linear.map left) (linear.map right) := by
  have split := linear.additive (subVector left right) right
  have rejoined : addVector (subVector left right) right = left := by
    funext coordinate
    exact sub_add_cancel _ _
  rw [rejoined] at split
  funext coordinate
  have atCoordinate := congrFun split coordinate
  simp only [addVector] at atCoordinate
  show linear.map (subVector left right) coordinate =
    sub (linear.map left coordinate) (linear.map right coordinate)
  rw [atCoordinate]
  real_grind

/-- A linear map stretches distances by at most its bound. -/
public theorem bounded_sub {source target : Nat} (linear : BoundedLinear source target)
    (left right : carrier source) :
    le (supNorm (subVector (linear.map left) (linear.map right)))
      (mul linear.bound (supNorm (subVector left right))) := by
  rw [← linear.map_sub]
  exact linear.bounded _

/-- The identity map. -/
@[expose] public def identity (dimension : Nat) : BoundedLinear dimension dimension where
  map := fun value => value
  additive := fun _ _ => rfl
  homogeneous := fun _ _ => rfl
  bound := one
  boundNonnegative := le_of_lt one_positive
  bounded := fun value => by
    rw [one_mul]
    exact le_refl _

/-- Apply `inner`, then `outer`. -/
@[expose] public def compose {source middle target : Nat}
    (outer : BoundedLinear middle target) (inner : BoundedLinear source middle) :
    BoundedLinear source target where
  map := fun value => outer.map (inner.map value)
  additive := fun left right => by
    rw [inner.additive, outer.additive]
  homogeneous := fun scalar value => by
    rw [inner.homogeneous, outer.homogeneous]
  bound := mul outer.bound inner.bound
  boundNonnegative := mul_nonnegative outer.boundNonnegative inner.boundNonnegative
  bounded := fun value => by
    refine le_trans (outer.bounded (inner.map value)) ?_
    rw [mul_assoc]
    exact mul_le_mul_nonnegative_left (inner.bounded value) outer.boundNonnegative

/-- The pointwise difference of two maps. -/
@[expose] public def difference {source target : Nat}
    (left right : BoundedLinear source target) : BoundedLinear source target where
  map := fun value => subVector (left.map value) (right.map value)
  additive := fun first second => by
    rw [left.additive, right.additive]
    funext coordinate
    simp only [addVector, subVector]
    real_grind
  homogeneous := fun scalar value => by
    rw [left.homogeneous, right.homogeneous]
    funext coordinate
    simp only [scaleVector, subVector]
    real_grind
  bound := add left.bound right.bound
  boundNonnegative := add_nonnegative left.boundNonnegative right.boundNonnegative
  bounded := fun value => by
    refine le_trans (supNorm_sub_triangle (left.map value) (zeroVector target)
      (right.map value)) ?_
    have leftZero : subVector (left.map value) (zeroVector target) = left.map value := by
      funext coordinate
      exact sub_zero _
    have zeroRight : supNorm (subVector (zeroVector target) (right.map value)) =
        supNorm (right.map value) := by
      rw [supNorm_sub_comm]
      congr 1
      funext coordinate
      exact sub_zero _
    rw [leftZero, zeroRight]
    have := add_le_add (left.bounded value) (right.bounded value)
    have distributed : add (mul left.bound (supNorm value)) (mul right.bound (supNorm value)) =
        mul (add left.bound right.bound) (supNorm value) := by
      real_grind
    rwa [distributed] at this

end BoundedLinear

/-- `right` undoes `left` on both sides. -/
@[expose] public def InverseOperators {dimension : Nat}
    (left right : BoundedLinear dimension dimension) : Prop :=
  (∀ value, right.map (left.map value) = value) ∧
    (∀ value, left.map (right.map value) = value)

/-- Two inverses of one map agree at every vector. -/
public theorem InverseOperators.map_eq {dimension : Nat}
    {left first second : BoundedLinear dimension dimension}
    (firstInverse : InverseOperators left first)
    (secondInverse : InverseOperators left second) (value : carrier dimension) :
    first.map value = second.map value := by
  calc first.map value = first.map (left.map (second.map value)) := by
        rw [secondInverse.right value]
    _ = second.map value := firstInverse.left _

end

end Problib.Analysis.Real.FiniteVector
