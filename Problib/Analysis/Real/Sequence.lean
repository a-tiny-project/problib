module

public import Problib.Analysis.Real.Limit

/-! Limits of real sequences, and the sampling of a punctured limit by them.

Dominated convergence is a statement about `Nat`-indexed sequences, because
Fatou's lemma reads a countable envelope. A derivative is a punctured limit in
a real displacement. This module states the sequence limit once and proves the
two directions that connect it to `Approaches`: a punctured limit carries every
nonzero null sequence to its value, and a function that does so on one
neighborhood approaches that value. The second direction chooses a witness
sequence by `Classical.choice` and is the only step that does.
-/

set_option autoImplicit false

namespace Problib.Analysis.Real

open Problib.Real.Construction.Dedekind

noncomputable section

/-- `ConvergesTo values limit` holds when the sequence stays within every
positive tolerance of `limit` from some index on. -/
@[expose] public def ConvergesTo (values : Nat → selection.Carrier)
    (limit : selection.Carrier) : Prop :=
  ∀ epsilon : selection.Carrier, lt zero epsilon →
    ∃ stage : Nat, ∀ index : Nat, stage ≤ index →
      lt (abs (sub (values index) limit)) epsilon

/-- A strict bound above every positive margin is a weak bound. -/
public theorem le_of_forall_lt_add {left right : selection.Carrier}
    (close : ∀ epsilon : selection.Carrier, lt zero epsilon →
      lt left (add right epsilon)) :
    le left right := by
  classical
  by_cases below : le left right
  · exact below
  · have greater : lt right left := lt_of_not_le below
    have strict := close (sub left right) (sub_positive_iff.mpr greater)
    rw [add_sub_cancel] at strict
    exact False.elim (lt_irrefl left strict)

/-- A limit of values bounded in size by a constant is bounded in size by it. -/
public theorem abs_le_of_convergesTo {values : Nat → selection.Carrier}
    {limit bound : selection.Carrier} (converges : ConvergesTo values limit)
    (bounded : ∀ index, le (abs (values index)) bound) :
    le (abs limit) bound := by
  apply le_of_forall_lt_add
  intro epsilon positive
  rcases converges epsilon positive with ⟨stage, close⟩
  have near := close stage (Nat.le_refl stage)
  rw [abs_sub_comm] at near
  have triangle := abs_add_le (values stage) (sub limit (values stage))
  rw [add_sub_cancel] at triangle
  have summed := add_lt_add_le near (bounded stage)
  rw [add_comm (abs (sub limit (values stage))), add_comm epsilon] at summed
  exact lt_of_le_of_lt triangle summed

/-- A punctured limit carries every nonzero sequence converging to zero to
its value. -/
public theorem convergesTo_of_approaches
    {function : selection.Carrier → selection.Carrier}
    {limit : selection.Carrier} (approaches : Approaches function limit)
    {displacements : Nat → selection.Carrier}
    (nonzero : ∀ index, displacements index ≠ zero)
    (null : ConvergesTo displacements zero) :
    ConvergesTo (fun index => function (displacements index)) limit := by
  intro epsilon positive
  rcases approaches epsilon positive with ⟨radius, radiusPositive, bound⟩
  rcases null radius radiusPositive with ⟨stage, small⟩
  refine ⟨stage, fun index later => ?_⟩
  have inside := small index later
  rw [sub_zero] at inside
  exact bound (displacements index) (nonzero index) inside

/-- The reciprocal of a successor is positive. -/
private theorem successor_inverse_positive (index : Nat) :
    lt zero (inverse (selection.ofRat ((index + 1 : Nat) : Rat))) := by
  apply inverse_of_positive_positive
  have embedded := (ofRat_lt_iff 0 ((index + 1 : Nat) : Rat)).mpr
    (Rat.natCast_pos.mpr (Nat.succ_pos index))
  rwa [ofRat_zero] at embedded

/-- Reciprocals of successors fall below every positive tolerance. -/
private theorem successor_inverse_small {epsilon : selection.Carrier}
    (positive : lt zero epsilon) :
    ∃ stage : Nat, ∀ index : Nat, stage ≤ index →
      lt (inverse (selection.ofRat ((index + 1 : Nat) : Rat))) epsilon := by
  rcases exists_positive_inverse_below positive with ⟨stage, stagePositive, small⟩
  refine ⟨stage, fun index later => ?_⟩
  have grown : le (selection.ofRat (stage : Rat))
      (selection.ofRat ((index + 1 : Nat) : Rat)) :=
    (ofRat_le_iff _ _).mpr (Rat.natCast_le_natCast.mpr (Nat.le_succ_of_le later))
  exact lt_of_le_of_lt (inverse_le_inverse_of_positive stagePositive grown) small

/-- Every positive radius holds a nonzero sequence converging to zero. -/
public theorem exists_null_sequence {radius : selection.Carrier}
    (radiusPositive : lt zero radius) :
    ∃ displacements : Nat → selection.Carrier,
      (∀ index, displacements index ≠ zero) ∧
        (∀ index, lt (abs (displacements index)) radius) ∧
          ConvergesTo displacements zero := by
  have radii : ∀ index : Nat, ∃ inner : selection.Carrier, lt zero inner ∧
      le inner radius ∧
        le inner (inverse (selection.ofRat ((index + 1 : Nat) : Rat))) :=
    fun index => small_positive radiusPositive (successor_inverse_positive index)
  have within := fun index =>
    exists_nonzero_within (Classical.choose_spec (radii index)).left
  refine ⟨fun index => Classical.choose (within index),
    fun index => (Classical.choose_spec (within index)).left,
    fun index => lt_of_lt_of_le (Classical.choose_spec (within index)).right
      (Classical.choose_spec (radii index)).right.left, ?_⟩
  intro tolerance tolerancePositive
  rcases successor_inverse_small tolerancePositive with ⟨stage, small⟩
  refine ⟨stage, fun index later => ?_⟩
  rw [sub_zero]
  exact lt_of_lt_of_le (Classical.choose_spec (within index)).right
    (le_trans (Classical.choose_spec (radii index)).right.right
      (le_of_lt (small index later)))

/-- A function that carries every nonzero null sequence inside one radius to
`limit` approaches `limit`. The proof chooses, for a tolerance that fails, one
escaping displacement inside each reciprocal radius. -/
public theorem approaches_of_sequences
    {function : selection.Carrier → selection.Carrier}
    {limit radius : selection.Carrier} (radiusPositive : lt zero radius)
    (sampled : ∀ displacements : Nat → selection.Carrier,
      (∀ index, displacements index ≠ zero) →
        (∀ index, lt (abs (displacements index)) radius) →
          ConvergesTo displacements zero →
            ConvergesTo (fun index => function (displacements index)) limit) :
    Approaches function limit := by
  classical
  apply Classical.byContradiction
  intro fails
  have escape : ∃ epsilon : selection.Carrier, lt zero epsilon ∧
      ∀ inner : selection.Carrier, lt zero inner →
        ∃ displacement : selection.Carrier, displacement ≠ zero ∧
          lt (abs displacement) inner ∧
            ¬lt (abs (sub (function displacement) limit)) epsilon := by
    apply Classical.byContradiction
    intro none
    apply fails
    intro epsilon positive
    apply Classical.byContradiction
    intro noRadius
    apply none
    refine ⟨epsilon, positive, fun inner innerPositive => ?_⟩
    apply Classical.byContradiction
    intro noDisplacement
    apply noRadius
    refine ⟨inner, innerPositive, fun displacement nonzero small => ?_⟩
    apply Classical.byContradiction
    intro far
    exact noDisplacement ⟨displacement, nonzero, small, far⟩
  rcases escape with ⟨epsilon, positive, escaping⟩
  have radii : ∀ index : Nat, ∃ inner : selection.Carrier, lt zero inner ∧
      le inner radius ∧
        le inner (inverse (selection.ofRat ((index + 1 : Nat) : Rat))) :=
    fun index => small_positive radiusPositive (successor_inverse_positive index)
  let inner := fun index => Classical.choose (radii index)
  have innerSpec := fun index => Classical.choose_spec (radii index)
  let displacements := fun index =>
    Classical.choose (escaping (inner index) (innerSpec index).left)
  have displacementSpec := fun index =>
    Classical.choose_spec (escaping (inner index) (innerSpec index).left)
  have null : ConvergesTo displacements zero := by
    intro tolerance tolerancePositive
    rcases successor_inverse_small tolerancePositive with ⟨stage, small⟩
    refine ⟨stage, fun index later => ?_⟩
    rw [sub_zero]
    exact lt_of_lt_of_le (displacementSpec index).right.left
      (le_trans (innerSpec index).right.right (le_of_lt (small index later)))
  have carried := sampled displacements
    (fun index => (displacementSpec index).left)
    (fun index => lt_of_lt_of_le (displacementSpec index).right.left
      (innerSpec index).right.left)
    null
  rcases carried epsilon positive with ⟨stage, close⟩
  exact (displacementSpec stage).right.right (close stage (Nat.le_refl stage))

end

end Problib.Analysis.Real
