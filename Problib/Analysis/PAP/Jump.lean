module

public import Problib.Analysis.PAP.Almost
public import Problib.Analysis.PAP.Lebesgue
public import Problib.Analysis.Real.Limit
public import Problib.Measure.Real.Pi

/-! # Dense upward jumps are not PAP

A PAP representation's pieces are analytic sets, and off a null set of
constraint exceptions every point of a piece has a ball inside the piece.
So on any set the measure charges, some point has such a ball, and there the
map is the piece's analytic witness, which is continuous. A map with an upward
jump at a dense set of points of an interval cannot be continuous on any ball
around a point of the interval, so it has no PAP representation on a domain
containing the interval. This is the step of ωPAP's Lemma E.7 done by measure
rather than by category. Almost-everywhere differentiability alone would not
exclude dense jumps, and the argument does not use it.
-/

set_option autoImplicit false

namespace Problib.Analysis.PAP

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real
open Problib.Analysis.Real.FiniteVector
open Problib.Analysis.Real.PowerSeries
open Problib.Measure
open Problib.Real (ENNReal)

/-- On a set the measure charges inside the domain, some point has a ball
inside one piece of the representation. -/
public theorem PAPRepresentation.exists_ball_in_piece {source target : Nat}
    {domain : Set (carrier source)} {function : carrier source → carrier target}
    (representation : PAPRepresentation domain function)
    {measure : Measure (vectorBorel source)} (nullZeros : NullAnalyticZeros measure)
    {region : Set (carrier source)} (inside : ∀ point, region point → domain point)
    (charged : ¬measure.NullSet region) :
    ∃ index point radius, region point ∧ lt zero radius ∧
      ∀ other, ball point radius other → representation.pieces index other := by
  classical
  have regular : ∃ point, region point ∧ ¬exceptions representation point := by
    apply Classical.byContradiction
    intro none
    apply charged
    apply Measure.NullSet.mono (exceptions_null representation nullZeros)
    intro point member
    exact Classical.byContradiction fun outside => none ⟨point, member, outside⟩
  rcases regular with ⟨point, member, outside⟩
  have covered : Set.iUnion representation.pieces point := by
    rw [← representation.cover]
    exact inside point member
  rcases covered with ⟨index, inPiece⟩
  rcases piece_neighborhood representation inPiece outside with ⟨radius, positive, near⟩
  exact ⟨index, point, radius, member, positive, near⟩

/-- Lebesgue measure on one coordinate gives a half-open interval its
length. -/
public theorem volumePi_interval (lower upper : selection.Carrier) :
    Problib.Measure.Real.volumePi 1
        (fun point => Problib.Measure.Real.Ioc lower upper (point 0)) =
      Problib.Real.ENNReal.ofReal (sub upper lower) := by
  let region : Set (carrier 1) := fun point => Problib.Measure.Real.Ioc lower upper (point 0)
  have regionMeasurable : (vectorBorel 1).Measurable region :=
    Space.coordinate_measurable (fun _ : Fin 1 => Problib.Measure.Real.borel) 0
      (Problib.Measure.Real.measurable_ioc lower upper)
  have indicatorMeasurable :=
    ENNRealMeasurable.indicator regionMeasurable (ENNRealMeasurable.constant (vectorBorel 1) ENNReal.one)
  have total : lintegral (Problib.Measure.Real.volumePi 1 : Measure (vectorBorel 1))
        (ennrealIndicator region (fun _ => ENNReal.one)) =
      Problib.Measure.Real.volumePi 1 region := by
    refine (lintegral_indicator _ _ regionMeasurable _).trans ?_
    refine (lintegral_const _ _).trans ?_
    refine (ENNReal.one_mul _).trans ?_
    exact Measure.restrict_apply_univ _ _
  have line : lintegral (Problib.Measure.Real.volumePi 1 : Measure (vectorBorel 1))
        (ennrealIndicator region (fun _ => ENNReal.one)) =
      lintegral Problib.Measure.Real.volume
        (ennrealIndicator (Problib.Measure.Real.Ioc lower upper) (fun _ => ENNReal.one)) := by
    have joint := indicatorMeasurable.comp (Problib.Measure.Real.finCons_measurable 0)
    rw [Problib.Measure.Real.volumePi_succ]
    refine (lintegral_map _ _ (Problib.Measure.Real.finCons_measurable 0) indicatorMeasurable).trans ?_
    refine (lintegral_prod _ _ _ joint).trans ?_
    apply lintegral_congr
    intro value
    rw [Problib.Measure.Real.volumePi_zero, lintegral_dirac _ _ (joint.comp (Space.pair_measurable
      (MeasurableMap.constant _ Problib.Measure.Real.borel value) (MeasurableMap.identity _)))]
    rfl
  have interval : lintegral Problib.Measure.Real.volume
        (ennrealIndicator (Problib.Measure.Real.Ioc lower upper) (fun _ => ENNReal.one)) =
      Problib.Measure.Real.volume (Problib.Measure.Real.Ioc lower upper) := by
    rw [lintegral_indicator _ _ (Problib.Measure.Real.measurable_ioc lower upper), lintegral_const,
      ENNReal.one_mul, Measure.restrict_apply_univ]
  exact total.symm.trans (line.trans (interval.trans (Problib.Measure.Real.volume_ioc lower upper)))

/-- Lebesgue measure charges every nondegenerate half-open interval of the
coordinate line. -/
public theorem volumePi_interval_not_null {lower upper : selection.Carrier}
    (below : lt lower upper) :
    ¬(Problib.Measure.Real.volumePi 1).NullSet
      (fun point => Problib.Measure.Real.Ioc lower upper (point 0)) := fun null =>
  (sub_positive_iff.mpr below).right
    (Problib.Real.ENNReal.ofReal_eq_zero_iff.mp ((volumePi_interval lower upper).symm.trans null))

/-- A map of one coordinate that jumps upward at a set of points dense in a
half-open interval has no PAP representation on any domain containing the
interval. -/
public theorem not_pap_of_dense_jumps {domain : Set (carrier 1)}
    {function : carrier 1 → carrier 1} {lower upper : selection.Carrier}
    (below : lt lower upper)
    (inside : ∀ point, lt lower (point 0) → le (point 0) upper → domain point)
    (jumps : Set (carrier 1))
    (dense : ∀ point radius, lt lower (point 0) → le (point 0) upper → lt zero radius →
      ∃ jump, jumps jump ∧ ball point radius jump)
    (upward : ∀ jump, jumps jump → ∃ gap, lt zero gap ∧
      ∀ later : carrier 1, lt (jump 0) (later 0) →
        le (add (function jump 0) gap) (function later 0))
    (representation : PAPRepresentation domain function) : False := by
  rcases representation.exists_ball_in_piece (Problib.Analysis.PAP.volumePi_null_analytic_zeros 1)
      (region := fun point => Problib.Measure.Real.Ioc lower upper (point 0))
      (fun point member => inside point member.1 member.2) (volumePi_interval_not_null below) with
    ⟨index, center, radius, member, positive, near⟩
  rcases dense center (half radius) member.1 member.2 (half_positive positive) with
    ⟨jump, isJump, close⟩
  rcases upward jump isJump with ⟨gap, gapPositive, rises⟩
  have halfBelow : ∀ value : selection.Carrier, lt zero value → lt (half value) value := by
    intro value valuePositive
    have step := (add_lt_add_left_iff (shift := half value)).mpr (half_positive valuePositive)
    rw [add_zero, add_half] at step
    exact step
  have jumpPiece := near jump (ball_mono (halfBelow radius positive).left close)
  have jumpRegion := representation.pieces_in_regions index jumpPiece
  rcases analytic_on_continuous_at (representation.analytic_witnesses index 0) jump jumpRegion
      gap gapPositive with ⟨reach, reachPositive, continuous⟩
  let radii : Fin 2 → selection.Carrier := fun choice => Fin.cases reach (fun _ => half radius) choice
  rcases finite_small_radius radii
      (fun choice => Fin.cases (motive := fun choice => lt zero (radii choice)) reachPositive
        (fun _ => half_positive positive) choice)
      (List.finRange 2) with ⟨step, stepPositive, stepBelow⟩
  let shift := half step
  have shiftPositive : lt zero shift := half_positive stepPositive
  have shiftReach : lt shift reach :=
    lt_of_lt_of_le (halfBelow step stepPositive) (stepBelow 0 (List.mem_finRange 0))
  have shiftRadius : lt shift (half radius) :=
    lt_of_lt_of_le (halfBelow step stepPositive) (stepBelow 1 (List.mem_finRange 1))
  let later : carrier 1 := fun _ => add (jump 0) shift
  have laterClose : ball jump reach later := by
    intro coordinate
    rw [fin_one_eq_zero coordinate]
    change lt (abs (sub (add (jump 0) shift) (jump 0))) reach
    rw [add_sub_self, abs_of_nonnegative shiftPositive.left]
    exact shiftReach
  have laterNear : ball center radius later := by
    intro coordinate
    rw [fin_one_eq_zero coordinate]
    change lt (abs (sub (add (jump 0) shift) (center 0))) radius
    have regroup : sub (add (jump 0) shift) (center 0) = add (sub (jump 0) (center 0)) shift := by
      rw [sub_eq_add_neg, sub_eq_add_neg, add_assoc, add_comm shift (neg (center 0)), ← add_assoc]
    rw [regroup]
    refine lt_of_le_of_lt (abs_add_le _ _) ?_
    rw [abs_of_nonnegative shiftPositive.left, ← add_half radius]
    exact add_lt_add (close 0) shiftRadius
  have laterAbove : lt (jump 0) (later 0) := by
    have step := (add_lt_add_left_iff (shift := jump 0)).mpr shiftPositive
    rw [add_zero] at step
    exact step
  have bound := rises later laterAbove
  rw [representation.agrees index later (near later laterNear),
    representation.agrees index jump jumpPiece] at bound
  have lower : le gap (sub (representation.witnesses index later 0)
      (representation.witnesses index jump 0)) := by
    apply add_le_add_left_iff.mp
    rw [add_sub_cancel]
    exact bound
  exact (lt_of_le_of_lt (le_trans lower (le_abs _)) (continuous later laterClose)).right
    (le_refl gap)

end Problib.Analysis.PAP
