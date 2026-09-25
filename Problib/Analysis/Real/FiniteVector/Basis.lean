module

public import Problib.Analysis.Real.FiniteVector
public import Problib.Real.Basis
public import Problib.Measure.Set

set_option autoImplicit false

namespace Problib.Analysis.Real.FiniteVector

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real
open Problib.Measure

/-- Enumerate finite vectors of natural-number indices using Cantor pairing. -/
@[expose] public def natVectorCode : (dimension : Nat) → Nat → Fin dimension → Nat
  | 0, _, coordinate => coordinate.elim0
  | dimension + 1, code, coordinate =>
      let pair := Problib.Countable.Pair.decode code
      Fin.cases pair.1 (natVectorCode dimension pair.2) coordinate

public theorem natVectorCode_surjective (dimension : Nat)
    (indices : Fin dimension → Nat) :
    ∃ code, natVectorCode dimension code = indices := by
  induction dimension with
  | zero =>
      refine ⟨0, ?_⟩
      funext coordinate
      exact coordinate.elim0
  | succ dimension induction =>
      rcases induction (fun coordinate => indices coordinate.succ) with
        ⟨tailCode, tailEqual⟩
      refine ⟨Problib.Countable.Pair.encode (indices 0, tailCode), ?_⟩
      funext coordinate
      refine Fin.cases ?_ ?_ coordinate
      · simp only [natVectorCode, Problib.Countable.Pair.decode_encode,
          Fin.cases_zero]
      · intro tail
        simpa only [natVectorCode, Problib.Countable.Pair.decode_encode,
          Fin.cases_succ] using congrFun tailEqual tail

/-- A countable grid of rational points in every finite Euclidean carrier. -/
@[expose] public noncomputable def rationalCenter (dimension : Nat)
    (code : Nat) : carrier dimension :=
  fun coordinate => rationalBasis (natVectorCode dimension code coordinate)

/-- Choose a rational grid point between coordinatewise lower and upper
bounds. -/
public theorem exists_rationalCenter_between {dimension : Nat}
    {lower upper : carrier dimension}
    (ordered : ∀ coordinate, lt (lower coordinate) (upper coordinate)) :
    ∃ code, ∀ coordinate,
      lt (lower coordinate) (rationalCenter dimension code coordinate) ∧
        lt (rationalCenter dimension code coordinate) (upper coordinate) := by
  classical
  have choose (coordinate : Fin dimension) : ∃ index,
      lt (lower coordinate) (rationalBasis index) ∧
        lt (rationalBasis index) (upper coordinate) :=
    exists_rationalBasis_between (ordered coordinate)
  let indices : Fin dimension → Nat := fun coordinate =>
    Classical.choose (choose coordinate)
  rcases natVectorCode_surjective dimension indices with ⟨code, equal⟩
  refine ⟨code, ?_⟩
  intro coordinate
  have choice := Classical.choose_spec (choose coordinate)
  simpa only [rationalCenter, congrFun equal coordinate] using choice

private theorem sub_lt_self_of_positive (value radius : selection.Carrier)
    (positive : lt zero radius) : lt (sub value radius) value := by
  apply sub_positive_iff.mp
  rwa [sub_sub_cancel]

private theorem self_lt_add_of_positive (value radius : selection.Carrier)
    (positive : lt zero radius) : lt value (add value radius) := by
  simpa only [add_zero] using add_lt_add_left value positive

/-- A rational closed coordinate box. Its closed faces will be useful when
splitting complements into finitely many analytic inequalities. -/
@[expose] public def closedBox {dimension : Nat}
    (lower upper : carrier dimension) : Set (carrier dimension) :=
  fun point => ∀ coordinate,
    le (lower coordinate) (point coordinate) ∧
      le (point coordinate) (upper coordinate)

private theorem within_coordinate_ball {value center radius : selection.Carrier}
    (lower : lt (sub center radius) value)
    (upper : lt value (add center radius)) :
    lt (abs (sub value center)) radius := by
  apply abs_lt.mpr
  constructor
  · have shifted := add_lt_add_right (neg center) lower
    rw [← sub_eq_add_neg] at shifted
    have leftEqual : sub (sub center radius) center = neg radius := by
      rw [sub_eq_add_neg, sub_eq_add_neg, add_assoc,
        add_comm (neg radius) (neg center), ← add_assoc,
        add_neg, zero_add]
    rwa [leftEqual] at shifted
  · have shifted := add_lt_add_right (neg center) upper
    have rightEqual : add (add center radius) (neg center) = radius := by
      rw [← sub_eq_add_neg, add_sub_self]
    rwa [← sub_eq_add_neg, rightEqual] at shifted

public theorem closedBox_subset_ball {dimension : Nat}
    {center lower upper : carrier dimension}
    {radius : selection.Carrier}
    (lowerBound : ∀ coordinate,
      lt (sub (center coordinate) radius) (lower coordinate))
    (upperBound : ∀ coordinate,
      lt (upper coordinate) (add (center coordinate) radius)) :
    Problib.Measure.Set.Subset (closedBox lower upper) (ball center radius) := by
  intro point inside coordinate
  exact within_coordinate_ball
    (lt_of_lt_of_le (lowerBound coordinate) (inside coordinate).1)
    (lt_of_le_of_lt (inside coordinate).2 (upperBound coordinate))

/-- Every point in an open set lies in a rational closed box contained in
that set. The pair of rational corner codes is the countable index. -/
public theorem exists_rational_closedBox_inside {dimension : Nat}
    {region : Set (carrier dimension)} (openRegion : IsOpen region)
    {point : carrier dimension} (member : region point) :
    ∃ lowerCode upperCode,
      closedBox (rationalCenter dimension lowerCode)
        (rationalCenter dimension upperCode) point ∧
      Problib.Measure.Set.Subset
        (closedBox (rationalCenter dimension lowerCode)
          (rationalCenter dimension upperCode)) region := by
  rcases openRegion point member with ⟨radius, positive, ballInside⟩
  let lowerLimit : carrier dimension := fun coordinate =>
    sub (point coordinate) radius
  let upperLimit : carrier dimension := fun coordinate =>
    add (point coordinate) radius
  rcases exists_rationalCenter_between
    (lower := lowerLimit) (upper := point)
    (fun coordinate => sub_lt_self_of_positive _ _ positive) with
      ⟨lowerCode, lowerBetween⟩
  rcases exists_rationalCenter_between
    (lower := point) (upper := upperLimit)
    (fun coordinate => self_lt_add_of_positive _ _ positive) with
      ⟨upperCode, upperBetween⟩
  refine ⟨lowerCode, upperCode, ?_, ?_⟩
  · intro coordinate
    exact ⟨(lowerBetween coordinate).2.left,
      (upperBetween coordinate).1.left⟩
  · intro candidate inBox
    apply ballInside candidate
    apply closedBox_subset_ball
      (fun coordinate => (lowerBetween coordinate).1)
      (fun coordinate => (upperBetween coordinate).2)
    exact inBox

end Problib.Analysis.Real.FiniteVector
