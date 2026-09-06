module

public import Foundations.Measure.Distribution.Basic
public import Foundations.Measure.AlmostEverywhere.Basic
public import Foundations.Measure.Additive.Partition
public import Foundations.Measure.Additive.Finite

set_option autoImplicit false

namespace Foundations.Measure.Necessity.Distribution

open Foundations.Real
open Foundations.Real.Construction

open Foundations.Measure.Real

public section

private theorem probabilityAE {measure : Measure unitBorel}
    (probability : Measure.IsProbability measure) {set : Set UnitInterval}
    (measurable : unitBorel.Measurable set) (mass : measure set = ENNReal.one) :
    measure.AE set := by
  have partition := measure.add_complement measurable
  rw [mass, probability.univ_eq_one] at partition
  exact ENNReal.addLeftCancelOfFinite (show ENNReal.Finite ENNReal.one from True.intro)
    (partition.trans (ENNReal.addZero ENNReal.one).symm)

/-- Countable almost-everywhere intersection along positive reciprocals `1 / (n + 1)`
excludes any probability measure assigning zero mass to `{0}` and mass one to every
initial interval `[0, ε]` with `ε > 0`. -/
theorem noRightJumpAtZero {measure : Measure unitBorel}
    (probability : Measure.IsProbability measure)
    (zero : measure (unitInitial unitZero) = ENNReal.zero)
    (positive : ∀ point : UnitInterval, Dedekind.lt Dedekind.zero point.val →
      measure (unitInitial point) = ENNReal.one) : False := by
  have onePositive : Dedekind.lt Dedekind.zero Dedekind.one :=
    Dedekind.positiveIffNonnegativeAndNonzero.mpr
      ⟨Dedekind.oneNonnegative, Dedekind.oneNeZero⟩
  let boundary := fun index => Dedekind.inverse
    (Dedekind.selection.ofRat (Nat.succ index : Rat))
  let regions := fun index => fun value : UnitInterval => Dedekind.le value.val (boundary index)
  have boundaryPositive : ∀ index, Dedekind.lt Dedekind.zero (boundary index) := by
    intro index
    apply Dedekind.inverseOfPositivePositive
    rw [← Dedekind.ofRatZero]
    apply (Dedekind.ofRatLtIff 0 (Nat.succ index : Rat)).mpr
    exact Rat.natCast_pos.mpr (Nat.zero_lt_succ index)
  have eachAE : ∀ index, measure.AE (regions index) := by
    intro index
    apply probabilityAE probability (unitInclusionMeasurable (measurable_Iic (boundary index)))
    rcases existsUnitRightBelow unitZero (boundary index) onePositive (boundaryPositive index) with
      ⟨point, above, below⟩
    apply ENNReal.leAntisymm
    · exact probability.univ_eq_one ▸ measure.mono (Set.subset_univ (regions index))
    · rw [← positive point above]
      exact measure.mono (fun {_} member => Dedekind.leTrans member below.1)
  have atZero : measure.AE (unitInitial unitZero) := by
    apply (Measure.ae_all_iff.mpr eachAE).mono
    intro value included
    apply Classical.byContradiction
    intro nonzero
    have strictlyPositive := notLeIffLt.mp nonzero
    rcases Dedekind.existsPositiveInverseBelow strictlyPositive with
      ⟨index, indexPositive, inverseBelow⟩
    cases index with
    | zero =>
        change Dedekind.lt Dedekind.zero (Dedekind.selection.ofRat (0 : Rat)) at indexPositive
        rw [Dedekind.ofRatZero] at indexPositive
        exact Dedekind.ltIrrefl Dedekind.zero indexPositive
    | succ predecessor =>
        exact inverseBelow.2 (included predecessor)
  have partition := measure.add_complement (unitInitialMeasurable unitZero)
  change measure (Set.complement (unitInitial unitZero)) = ENNReal.zero at atZero
  rw [zero, atZero, ENNReal.zeroAdd, probability.univ_eq_one] at partition
  exact ENNReal.oneNeZero partition.symm

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
      exact leftZero (Dedekind.leAntisymm included left.property.1)
    rw [if_neg leftZero, if_neg rightNonzero]
    exact Dedekind.leRefl _

theorem jumpAtZero_upper : jumpAtZero unitOne = unitOne := by
  classical
  unfold jumpAtZero
  exact if_neg Dedekind.oneNeZero

/-- Sharpness / Necessity witness: no measure on `unitBorel` can realize the initial-interval
masses prescribed by `jumpAtZero`. The proof derives probability from the endpoint equation
at one, refuting existence without an assumed probability premise. -/
theorem jumpAtZero_no_measure {measure : Measure unitBorel}
    (reconstruct : ∀ point, measure (unitInitial point) =
      ENNReal.ofReal (jumpAtZero point).val) : False := by
  have probability : Measure.IsProbability measure := by
    constructor
    rw [← unitInitial_one, reconstruct, jumpAtZero_upper]
    exact ENNReal.ofRealToRealFinite NNReal.one
  apply noRightJumpAtZero probability
  · rw [reconstruct]
    have same : jumpAtZero unitZero = unitZero := by
      classical
      unfold jumpAtZero
      exact if_pos rfl
    rw [same]
    exact ENNReal.ofRealEqZeroIff.mpr (Dedekind.leRefl _)
  · intro point positive
    have nonzero : point.val ≠ Dedekind.zero := by
      intro equal
      rw [equal] at positive
      exact Dedekind.ltIrrefl Dedekind.zero positive
    have same : jumpAtZero point = unitOne := by
      classical
      unfold jumpAtZero
      exact if_neg nonzero
    rw [reconstruct, same]
    exact ENNReal.ofRealToRealFinite NNReal.one

end

end Foundations.Measure.Necessity.Distribution
