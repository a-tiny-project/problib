module

public import Problib.Analysis.Real.FiniteVector.Complete
public import Problib.Analysis.Real.GeometricSeries
public import Problib.Real.Grind

/-! Fixed points of maps that halve distances.

A map that sends a closed set into itself and halves the distance between any
two of its points has exactly one fixed point there. Iterating from a start, the
`k`-th step moves at most `2⁻ᵏ` times the first step, so the iterates are Cauchy
and converge, and the set keeps their limit. The limit is fixed because the map
moves it no further than it moves the iterates, which come arbitrarily close.
The ratio is one half rather than an arbitrary constant below one: the inverse
function theorem chooses its radii for one half, and the geometric bounds then
need no general ratio.
-/

set_option autoImplicit false

namespace Problib.Analysis.Real.FiniteVector

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real
open Problib.Analysis.Real.SignedSeries

noncomputable section

/-- The iterates of `map` from `start`. -/
private def iterateFrom {dimension : Nat} (map : carrier dimension → carrier dimension)
    (start : carrier dimension) : Nat → carrier dimension
  | 0 => start
  | index + 1 => map (iterateFrom map start index)

private theorem half_one_lt_one : lt (half one) one := by
  have := one_positive
  simp only [half, two]
  real_grind

private theorem double_nonnegative {value : selection.Carrier} (nonnegative : le zero value) :
    le zero (mul two value) := by
  simp only [two]
  real_grind

private theorem spread_step (distance first last : selection.Carrier) :
    add (mul last distance) (mul (mul two distance) (sub first last)) =
      mul (mul two distance) (sub first (mul (half one) last)) := by
  simp only [half, two]
  real_grind

private theorem sub_le_self_of_nonnegative {value subtracted : selection.Carrier}
    (nonnegative : le zero subtracted) : le (sub value subtracted) value := by
  have := nonnegative
  real_grind

private theorem add_mul_self (factor value : selection.Carrier) :
    add (mul factor value) (mul factor value) = mul (add factor factor) value := by
  real_grind

private theorem half_lt_half {left right : selection.Carrier} (less : lt left right) :
    lt (half left) (half right) := by
  simp only [half, two]
  real_grind

private theorem quarter_add_half_lt {value : selection.Carrier} (positive : lt zero value) :
    lt (add (half (half value)) (half value)) value := by
  simp only [half, two]
  real_grind

private theorem nonpositive_of_le_half {value : selection.Carrier}
    (nonnegative : le zero value) (halved : le value (half value)) : le value zero := by
  have := nonnegative
  simp only [half, two] at halved
  real_grind

/-- A map that keeps a closed set and halves distances in it has a unique fixed
point there, within twice the first step of the start. -/
public theorem contraction_fixed {dimension : Nat} {closed : carrier dimension → Prop}
    (limits : ∀ values limit, (∀ index, closed (values index)) →
      ConvergesTo values limit → closed limit)
    {map : carrier dimension → carrier dimension}
    (mapsTo : ∀ value, closed value → closed (map value))
    (contracts : ∀ first second, closed first → closed second →
      le (supNorm (subVector (map first) (map second)))
        (half (supNorm (subVector first second))))
    {start : carrier dimension} (startClosed : closed start) :
    ∃ fixed, closed fixed ∧ map fixed = fixed ∧
      le (supNorm (subVector fixed start))
        (mul two (supNorm (subVector (map start) start))) ∧
      ∀ other, closed other → map other = other → other = fixed := by
  let ratio := half one
  let distance := supNorm (subVector (map start) start)
  let scale := mul two distance
  have ratioPositive : lt zero ratio := half_positive one_positive
  have ratioNonnegative := le_of_lt ratioPositive
  have ratioBelowOne : lt ratio one := half_one_lt_one
  have distanceNonnegative : le zero distance := supNorm_nonnegative _
  have scaleNonnegative : le zero scale := double_nonnegative distanceNonnegative
  have closedIterate : ∀ index, closed (iterateFrom map start index) := by
    intro index
    induction index with
    | zero => exact startClosed
    | succ index induction => exact mapsTo _ induction
  -- Each step is at most `ratio ^ index` times the first.
  have step : ∀ index,
      le (supNorm (subVector (iterateFrom map start (index + 1)) (iterateFrom map start index)))
        (mul (power ratio index) distance) := by
    intro index
    induction index with
    | zero =>
        rw [power_zero, one_mul]
        exact le_refl _
    | succ index induction =>
        refine le_trans (contracts _ _ (closedIterate (index + 1)) (closedIterate index)) ?_
        rw [half_eq_mul, power_succ, mul_assoc]
        exact mul_le_mul_nonnegative_left induction ratioNonnegative
  -- The steps from `index` on sum to at most `scale` times `ratio ^ index`.
  have spread : ∀ index count,
      le (supNorm (subVector (iterateFrom map start (index + count)) (iterateFrom map start index)))
        (mul scale (sub (power ratio index) (power ratio (index + count)))) := by
    intro index count
    induction count with
    | zero =>
        rw [Nat.add_zero, supNorm_sub_self, sub_self, mul_zero]
        exact le_refl _
    | succ count induction =>
        refine le_trans (supNorm_sub_triangle _ (iterateFrom map start (index + count)) _) ?_
        have last := step (index + count)
        rw [show index + (count + 1) = index + count + 1 from rfl]
        have equal : add (mul (power ratio (index + count)) distance)
            (mul scale (sub (power ratio index) (power ratio (index + count)))) =
            mul scale (sub (power ratio index) (power ratio (index + count + 1))) :=
          spread_step distance _ _
        have bound := add_le_add last induction
        rw [equal] at bound
        exact bound
  have nearStage : ∀ index count,
      le (supNorm (subVector (iterateFrom map start (index + count)) (iterateFrom map start index)))
        (mul scale (power ratio index)) := by
    intro index count
    refine le_trans (spread index count) (mul_le_mul_nonnegative_left ?_ scaleNonnegative)
    exact sub_le_self_of_nonnegative (power_nonnegative ratioNonnegative (index + count))
  -- The iterates are Cauchy.
  have shrinking := converges_to_scale (add scale scale)
    (terms_converge_zero (geometric_summable ratioNonnegative ratioBelowOne))
  rw [mul_zero] at shrinking
  have cauchy : ∀ epsilon, lt zero epsilon → ∃ stage : Nat, ∀ first second,
      stage ≤ first → stage ≤ second →
        lt (supNorm (subVector (iterateFrom map start first)
          (iterateFrom map start second))) epsilon := by
    intro epsilon positive
    rcases shrinking epsilon positive with ⟨stage, small⟩
    refine ⟨stage, fun first second firstLater secondLater => ?_⟩
    have tail := lt_of_le_of_lt (le_abs _) (small stage (Nat.le_refl stage))
    rw [sub_zero] at tail
    have firstNear := nearStage stage (first - stage)
    have secondNear := nearStage stage (second - stage)
    rw [Nat.add_sub_cancel' firstLater] at firstNear
    rw [Nat.add_sub_cancel' secondLater, supNorm_sub_comm] at secondNear
    refine lt_of_le_of_lt (supNorm_sub_triangle _ (iterateFrom map start stage) _) ?_
    refine lt_of_le_of_lt (add_le_add firstNear secondNear) ?_
    rwa [add_mul_self]
  rcases converges_of_cauchy cauchy with ⟨fixed, converges⟩
  have fixedClosed := limits _ fixed closedIterate converges
  have closeTo : ∀ epsilon, lt zero epsilon → ∃ stage : Nat, ∀ index, stage ≤ index →
      lt (supNorm (subVector fixed (iterateFrom map start index))) epsilon := by
    intro epsilon positive
    rcases converges epsilon positive with ⟨stage, close⟩
    exact ⟨stage, fun index later => by
      rw [supNorm_sub_comm]
      exact (ball_iff_supNorm positive).mp (close index later)⟩
  -- The map moves the limit no further than half its distance to an iterate,
  -- plus that iterate's distance to the next one.
  have isFixed : map fixed = fixed := by
    apply eq_of_supNorm_sub_small
    intro epsilon positive
    rcases closeTo (half epsilon) (half_positive positive) with ⟨stage, close⟩
    have mapped := contracts _ _ fixedClosed (closedIterate stage)
    have before := close stage (Nat.le_refl stage)
    have after := close (stage + 1) (Nat.le_succ stage)
    rw [supNorm_sub_comm] at after
    refine lt_of_le_of_lt (supNorm_sub_triangle _ (iterateFrom map start (stage + 1)) _) ?_
    exact lt_trans (add_lt_add (lt_of_le_of_lt mapped (half_lt_half before)) after)
      (quarter_add_half_lt positive)
  refine ⟨fixed, fixedClosed, isFixed, ?_, ?_⟩
  · -- Every iterate is within `scale` of the start, so the limit is too.
    apply le_of_forall_lt_add
    intro epsilon positive
    rcases closeTo epsilon positive with ⟨stage, close⟩
    have reach := nearStage 0 stage
    rw [Nat.zero_add, power_zero, mul_one] at reach
    refine lt_of_le_of_lt (supNorm_sub_triangle _ (iterateFrom map start stage) _) ?_
    rw [add_comm scale]
    exact lt_of_lt_of_le (add_lt_add_right _ (close stage (Nat.le_refl stage)))
      (add_le_add (le_refl _) reach)
  · intro other otherClosed otherFixed
    apply eq_of_supNorm_sub_nonpositive
    have halved := contracts _ _ otherClosed fixedClosed
    rw [otherFixed, isFixed] at halved
    exact nonpositive_of_le_half (supNorm_nonnegative _) halved

end

end Problib.Analysis.Real.FiniteVector
