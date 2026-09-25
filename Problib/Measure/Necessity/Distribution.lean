module

public import Problib.Measure.Distribution.Basic
public import Problib.Measure.AlmostEverywhere.Basic
public import Problib.Measure.Additive.Partition
public import Problib.Measure.Additive.Finite

set_option autoImplicit false

namespace Problib.Measure.Necessity.Distribution

open Problib.Real
open Problib.Real.Construction

open Problib.Measure.Real

public section

private theorem probability_ae {measure : Measure unitBorel}
    (probability : Measure.IsProbability measure) {set : Set UnitInterval}
    (measurable : unitBorel.Measurable set) (mass : measure set = ENNReal.one) :
    measure.AE set := by
  have partition := measure.add_complement measurable
  rw [mass, probability.univ_eq_one] at partition
  exact ENNReal.add_left_cancel_of_finite (show ENNReal.Finite ENNReal.one from True.intro)
    (partition.trans (ENNReal.add_zero ENNReal.one).symm)

/-- Countable almost-everywhere intersection along positive reciprocals `1 / (n + 1)`
excludes any probability measure assigning zero mass to `{0}` and mass one to every
initial interval `[0, ε]` with `ε > 0`. -/
theorem no_right_jump_at_zero {measure : Measure unitBorel}
    (probability : Measure.IsProbability measure)
    (zero : measure (unitInitial unitZero) = ENNReal.zero)
    (positive : ∀ point : UnitInterval, Dedekind.lt Dedekind.zero point.val →
      measure (unitInitial point) = ENNReal.one) : False := by
  have onePositive : Dedekind.lt Dedekind.zero Dedekind.one :=
    Dedekind.positive_iff_nonnegative_and_nonzero.mpr
      ⟨Dedekind.one_nonnegative, Dedekind.one_ne_zero⟩
  let boundary := fun index => Dedekind.inverse
    (Dedekind.selection.ofRat (Nat.succ index : Rat))
  let regions := fun index => fun value : UnitInterval => Dedekind.le value.val (boundary index)
  have boundaryPositive : ∀ index, Dedekind.lt Dedekind.zero (boundary index) := by
    intro index
    apply Dedekind.inverse_of_positive_positive
    rw [← Dedekind.ofRat_zero]
    apply (Dedekind.ofRat_lt_iff 0 (Nat.succ index : Rat)).mpr
    exact Rat.natCast_pos.mpr (Nat.zero_lt_succ index)
  have eachAE : ∀ index, measure.AE (regions index) := by
    intro index
    apply probability_ae probability (unitInclusion_measurable (measurable_iic (boundary index)))
    rcases exists_unit_right_below unitZero (boundary index) onePositive (boundaryPositive index) with
      ⟨point, above, below⟩
    apply ENNReal.le_antisymm
    · exact probability.univ_eq_one ▸ measure.mono (Set.subset_univ (regions index))
    · rw [← positive point above]
      exact measure.mono (fun {_} member => Dedekind.le_trans member below.1)
  have atZero : measure.AE (unitInitial unitZero) := by
    apply (Measure.ae_all_iff.mpr eachAE).mono
    intro value included
    apply Classical.byContradiction
    intro nonzero
    have strictlyPositive := not_le_iff_lt.mp nonzero
    rcases Dedekind.exists_positive_inverse_below strictlyPositive with
      ⟨index, indexPositive, inverseBelow⟩
    cases index with
    | zero =>
        change Dedekind.lt Dedekind.zero (Dedekind.selection.ofRat (0 : Rat)) at indexPositive
        rw [Dedekind.ofRat_zero] at indexPositive
        exact Dedekind.lt_irrefl Dedekind.zero indexPositive
    | succ predecessor =>
        exact inverseBelow.2 (included predecessor)
  have partition := measure.add_complement (unitInitial_measurable unitZero)
  change measure (Set.complement (unitInitial unitZero)) = ENNReal.zero at atZero
  rw [zero, atZero, ENNReal.zero_add, probability.univ_eq_one] at partition
  exact ENNReal.one_ne_zero partition.symm

/-- Step function jumping from `0` at `0` to `1` for all `x > 0`. Monotone and normalized
at one, but lacks right-continuity at zero. -/
@[expose] noncomputable def jumpAtZero (point : UnitInterval) : UnitInterval := by
  classical
  exact if point.val = Dedekind.zero then unitZero else unitOne

theorem jumpAtZero_monotone {left right : UnitInterval}
    (included : Dedekind.le left.val right.val) :
    Dedekind.le (jumpAtZero left).val (jumpAtZero right).val := by
  classical
  unfold jumpAtZero
  by_cases leftZero : left.val = Dedekind.zero
  · rw [if_pos leftZero]
    exact (if right.val = Dedekind.zero then unitZero else unitOne).property.1
  · have rightNonzero : right.val ≠ Dedekind.zero := by
      intro rightZero
      rw [rightZero] at included
      exact leftZero (Dedekind.le_antisymm included left.property.1)
    rw [if_neg leftZero, if_neg rightNonzero]
    exact Dedekind.le_refl _

theorem jumpAtZero_upper : jumpAtZero unitOne = unitOne := by
  classical
  unfold jumpAtZero
  exact if_neg Dedekind.one_ne_zero

/-- Sharpness / Necessity witness: no measure on `unitBorel` can realize the initial-interval
masses prescribed by `jumpAtZero`. The proof derives probability from the endpoint equation
at one, refuting existence without an assumed probability premise. -/
theorem jumpAtZero_no_measure {measure : Measure unitBorel}
    (reconstruct : ∀ point, measure (unitInitial point) =
      ENNReal.ofReal (jumpAtZero point).val) : False := by
  have probability : Measure.IsProbability measure := by
    constructor
    rw [← unitInitial_one, reconstruct, jumpAtZero_upper]
    exact ENNReal.ofReal_toReal_finite NNReal.one
  apply no_right_jump_at_zero probability
  · rw [reconstruct]
    have same : jumpAtZero unitZero = unitZero := by
      classical
      unfold jumpAtZero
      exact if_pos rfl
    rw [same]
    exact ENNReal.ofReal_eq_zero_iff.mpr (Dedekind.le_refl _)
  · intro point positive
    have nonzero : point.val ≠ Dedekind.zero := by
      intro equal
      rw [equal] at positive
      exact Dedekind.lt_irrefl Dedekind.zero positive
    have same : jumpAtZero point = unitOne := by
      classical
      unfold jumpAtZero
      exact if_neg nonzero
    rw [reconstruct, same]
    exact ENNReal.ofReal_toReal_finite NNReal.one

end

end Problib.Measure.Necessity.Distribution
