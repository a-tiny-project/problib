module

public import Problib.Analysis.PAP.Null
public import Problib.Analysis.PAP.Measurable
public import Problib.Measure.Integral.Lebesgue.AlmostEverywhere
public import Problib.Measure.Integral.Lebesgue.Algebra

/-! Zero sets of analytic functions on coordinate balls are null.

The statement holds for every family of measures on the finite Euclidean
carriers that integrates out the first coordinate against volume, which is
how the Lebesgue product measure is built. On a ball of dimension one more
than the induction hypothesis, fix the remaining coordinates at one point
where the function is nonzero. The line through that point gives a nonzero
analytic function of the first coordinate, so the first coordinates whose
whole slice vanishes form a null set. Every other slice is null by
induction, and Tonelli adds the slices.
-/

set_option autoImplicit false

namespace Problib.Analysis.PAP

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real
open Problib.Analysis.Real.FiniteVector
open Problib.Analysis.Real.PowerSeries
open Problib.Measure

noncomputable section

/-- Put a first coordinate in front of a vector. -/
@[expose] public def prependCoordinate {dimension : Nat}
    (first : selection.Carrier) (rest : carrier dimension) :
    carrier (dimension + 1) :=
  fun coordinate => Fin.cases first rest coordinate

/-- The coordinates after the first. -/
@[expose] public def tailVector {dimension : Nat}
    (point : carrier (dimension + 1)) : carrier dimension :=
  fun coordinate => point coordinate.succ

public theorem prependCoordinate_head_tail {dimension : Nat}
    (point : carrier (dimension + 1)) :
    prependCoordinate (point 0) (tailVector point) = point := by
  funext coordinate
  refine Fin.cases ?_ (fun _ => ?_) coordinate <;> rfl

public theorem ball_prependCoordinate_iff {dimension : Nat}
    {center : carrier (dimension + 1)} {radius first : selection.Carrier}
    {rest : carrier dimension} :
    ball center radius (prependCoordinate first rest) ↔
      lt (abs (sub first (center 0))) radius ∧
        ball (tailVector center) radius rest := by
  constructor
  · intro inside
    exact ⟨inside 0, fun coordinate => inside coordinate.succ⟩
  · rintro ⟨head, tail⟩ coordinate
    refine Fin.cases ?_ (fun later => ?_) coordinate
    · exact head
    · exact tail later

/-- A family of measures on the finite Euclidean carriers that integrates out
the first coordinate against volume on every measurable set. -/
@[expose] public def FirstCoordinateTonelli
    (law : (dimension : Nat) → Measure (vectorBorel dimension)) : Prop :=
  ∀ (dimension : Nat) (region : Set (carrier (dimension + 1))),
    (vectorBorel (dimension + 1)).Measurable region →
      law (dimension + 1) region =
        lintegral Problib.Measure.Real.volume (fun first =>
          law dimension (fun rest => region (prependCoordinate first rest)))

private theorem analytic_vector_prepend_rest {dimension : Nat}
    {region : Set (carrier dimension)} (openRegion : IsOpen region)
    (first : selection.Carrier) :
    AnalyticVectorOn region (fun rest => prependCoordinate first rest) := by
  intro coordinate
  refine Fin.cases ?_ (fun later => ?_) coordinate
  · exact analytic_on_constant openRegion first
  · exact analytic_on_coordinate openRegion later

private theorem analytic_vector_prepend_line {dimension : Nat}
    {region : Set (carrier 1)} (openRegion : IsOpen region)
    (rest : carrier dimension) :
    AnalyticVectorOn region
      (fun line : carrier 1 => prependCoordinate (line 0) rest) := by
  intro coordinate
  refine Fin.cases ?_ (fun later => ?_) coordinate
  · exact analytic_on_coordinate openRegion 0
  · exact analytic_on_constant openRegion (rest later)

/-- The zeros of an analytic function inside its open domain form a Borel
set. -/
public theorem analytic_zero_measurable {dimension : Nat}
    {region : Set (carrier dimension)}
    {function : carrier dimension → selection.Carrier}
    (analytic : AnalyticOn region function) :
    (vectorBorel dimension).Measurable
      (fun point => region point ∧ function point = zero) := by
  apply analytic_set_measurable
  refine ⟨region, [function, fun point => mul (neg one) (function point)],
    analytic.left, ?_, ?_⟩
  · intro constraint member
    rcases List.mem_cons.mp member with equal | rest
    · rw [equal]
      exact analytic
    · rw [List.mem_singleton.mp rest]
      exact analytic_on_scale analytic (neg one)
  · intro point
    constructor
    · rintro ⟨inside, vanished⟩
      refine ⟨inside, fun constraint member => ?_⟩
      rcases List.mem_cons.mp member with equal | rest
      · rw [equal, vanished]
        exact le_refl zero
      · rw [List.mem_singleton.mp rest]
        change le (mul (neg one) (function point)) zero
        rw [vanished, mul_zero]
        exact le_refl zero
    · rintro ⟨inside, bounded⟩
      refine ⟨inside, le_antisymm (bounded function List.mem_cons_self) ?_⟩
      have negated := bounded (fun point => mul (neg one) (function point))
        (List.mem_cons_of_mem _ List.mem_cons_self)
      rw [neg_mul, one_mul] at negated
      exact neg_nonpositive_iff.mpr negated

/-- An analytic function on a coordinate ball either vanishes on the whole
ball, or its zeros in the ball are null for every measure family that
integrates out the first coordinate. -/
public theorem analytic_zero_null
    {law : (dimension : Nat) → Measure (vectorBorel dimension)}
    (tonelli : FirstCoordinateTonelli law) :
    ∀ (dimension : Nat) (center : carrier dimension)
      (radius : selection.Carrier) (function : carrier dimension → selection.Carrier),
      AnalyticOn (ball center radius) function →
      (∀ point, ball center radius point → function point = zero) ∨
        (law dimension).NullSet
          (fun point => ball center radius point ∧ function point = zero) := by
  intro dimension
  induction dimension with
  | zero =>
      intro center radius function _
      classical
      by_cases vanish : ∀ point, ball center radius point → function point = zero
      · exact Or.inl vanish
      · refine Or.inr (Measure.NullSet.mono (Measure.null_empty _) ?_)
        intro point member
        apply vanish
        intro other otherInside
        have same : other = point := funext fun coordinate => coordinate.elim0
        rw [same]
        exact member.2
  | succ dimension induction =>
      intro center radius function analytic
      classical
      by_cases vanish : ∀ point, ball center radius point → function point = zero
      · exact Or.inl vanish
      refine Or.inr ?_
      rcases Classical.not_forall.mp vanish with ⟨witness, failure⟩
      rcases Classical.not_imp.mp failure with ⟨witnessInside, witnessNonzero⟩
      have radiusPositive : lt zero radius :=
        lt_of_le_of_lt (abs_nonnegative _) (witnessInside 0)
      let rest := tailVector witness
      have restInside : ball (tailVector center) radius rest :=
        (ball_prependCoordinate_iff.mp
          ((prependCoordinate_head_tail witness).symm ▸ witnessInside)).2
      let slice (first : selection.Carrier) : Set (carrier dimension) :=
        fun other => ball center radius (prependCoordinate first other) ∧
          function (prependCoordinate first other) = zero
      let flatFirst : Set selection.Carrier := fun first =>
        lt (abs (sub first (center 0))) radius ∧
          ∀ other, ball (tailVector center) radius other →
            function (prependCoordinate first other) = zero
      have sliceNull : ∀ first, ¬flatFirst first →
          (law dimension).NullSet (slice first) := by
        intro first notFlat
        by_cases firstInside : lt (abs (sub first (center 0))) radius
        · let sliced : carrier dimension → selection.Carrier := fun other =>
            function (prependCoordinate first other)
          have slicedAnalytic : AnalyticOn (ball (tailVector center) radius)
              sliced :=
            analytic_on_comp (ball_is_open _ radiusPositive)
              (analytic_vector_prepend_rest (ball_is_open _ radiusPositive) first)
              analytic
              (fun other inside =>
                ball_prependCoordinate_iff.mpr ⟨firstInside, inside⟩)
          rcases induction (tailVector center) radius sliced slicedAnalytic with
            allZero | null
          · exact False.elim (notFlat ⟨firstInside, allZero⟩)
          · apply null.mono
            intro other member
            exact ⟨(ball_prependCoordinate_iff.mp member.1).2, member.2⟩
        · apply Measure.NullSet.mono (Measure.null_empty _)
          intro other member
          exact firstInside (ball_prependCoordinate_iff.mp member.1).1
      have flatNull : Problib.Measure.Real.volume.NullSet flatFirst := by
        let line : carrier 1 → selection.Carrier := fun point =>
          function (prependCoordinate (point 0) rest)
        have lineAnalytic : AnalyticOn (ball (linePoint (center 0)) radius)
            line :=
          analytic_on_comp (ball_is_open _ radiusPositive)
            (analytic_vector_prepend_line (ball_is_open _ radiusPositive) rest)
            analytic
            (fun point inside => ball_prependCoordinate_iff.mpr
              ⟨inside 0, restInside⟩)
        have lineNonzero : ¬∀ value, lt (abs (sub value (center 0))) radius →
            line (linePoint value) = zero := by
          intro allZero
          apply witnessNonzero
          have atWitness := allZero (witness 0) (witnessInside 0)
          change function (prependCoordinate (witness 0) (tailVector witness)) =
            zero at atWitness
          rwa [prependCoordinate_head_tail] at atWitness
        apply (line_zero_null lineAnalytic lineNonzero).mono
        intro first member
        exact ⟨member.1, member.2 rest restInside⟩
      have zeroMeasurable := analytic_zero_measurable analytic
      unfold Measure.NullSet
      rw [tonelli dimension _ zeroMeasurable]
      have almostZero : Problib.Measure.Real.volume.AEEq
          (fun first => law dimension (slice first))
          (fun _ => Problib.Real.ENNReal.zero) := by
        apply flatNull.mono
        intro first disagree
        apply Classical.byContradiction
        intro notFlat
        exact disagree (sliceNull first notFlat)
      rw [lintegral_congr_ae almostZero, lintegral_zero]

end

end Problib.Analysis.PAP
