module

public import Foundations.Measure.Extended.Unit.Basis

set_option autoImplicit false

namespace Foundations.Measure.Coding.Unit

open Foundations.Real
open Foundations.Real.Construction
open Foundations.Measure.Real

universe u

/-- Boolean indicators comparing each unit rational basis element against a unit interval point. -/
@[expose] public noncomputable def bits (point : UnitInterval) (index : Nat) : Bool := by
  classical
  exact decide (Dedekind.le (unitRationalBasis index).val point.val)

/-- Value of the indexed unit rational basis element when selected, or zero. -/
@[expose] public noncomputable def selected (digits : Nat → Bool) (index : Nat) : ENNReal :=
  if digits index = true then ENNReal.ofReal (unitRationalBasis index).val else ENNReal.zero

/-- Reconstruct a unit interval point as the supremum of selected rational basis elements. -/
@[expose] public noncomputable def value (digits : Nat → Bool) : UnitInterval :=
  unitClamp (ENNReal.iSup (selected digits))

/-- Each selected rational basis element is bounded above by the target point. -/
public theorem selected_bits_le (point : UnitInterval) (index : Nat) :
    ENNReal.le (selected (bits point) index) (ENNReal.ofReal point.val) := by
  classical
  unfold selected bits
  simp only [decide_eq_true_eq]
  split
  · rename_i included
    exact ENNReal.ofRealMonotone included
  · exact ENNReal.zeroLe _

/-- Reconstructing the unit point from its rational basis indicators recovers the original point. -/
public theorem value_bits (point : UnitInterval) : value (bits point) = point := by
  classical
  apply Subtype.ext
  apply Dedekind.leAntisymm
  · have included := unitClamp_mono (ENNReal.iSupLe (selected_bits_le point))
    rw [unitClamp_ofReal] at included
    exact included
  · apply Classical.byContradiction
    intro missing
    have less := notLeIffLt.mp missing
    rcases existsUnitRationalBasisBetween less with ⟨index, above, below⟩
    have chosen : selected (bits point) index = ENNReal.ofReal (unitRationalBasis index).val := by
      simp only [selected, bits, decide_eq_true_eq, if_pos below.1]
    have included := ENNReal.leISup (selected (bits point)) index
    rw [chosen] at included
    have bound := unitClamp_mono included
    rw [unitClamp_ofReal] at bound
    exact above.2 bound

/-- Each rational comparison indicator event is measurable in unit interval Borel space. -/
public theorem bits_measurable (index : Nat) :
    unitBorel.Measurable (fun point => bits point index = true) := by
  classical
  have equal : (fun point => bits point index = true) =
      Set.preimage unitInclusion (Ici (unitRationalBasis index).val) := by
    apply Set.ext
    intro point
    simp only [bits, decide_eq_true_eq, Set.preimage, unitInclusion, Ici]
  rw [equal]
  exact unitInclusionMeasurable (measurable_Ici (unitRationalBasis index).val)

/-- Reconstructing unit interval points from measurable indicator events is measurable. -/
public theorem value_measurable {α : Type u} {source : Space α} {digits : α → Nat → Bool}
    (events : ∀ index, source.Measurable (fun point => digits point index = true)) :
    MeasurableMap source unitBorel (fun point => value (digits point)) := by
  classical
  have selections : ∀ index, ENNRealMeasurable source
      (fun point => selected (digits point) index) := by
    intro index
    have equal : (fun point => selected (digits point) index) =
        ennrealPiecewise (fun point => digits point index = true)
          (fun _ => ENNReal.ofReal (unitRationalBasis index).val) (fun _ => ENNReal.zero) := by
      funext point
      by_cases present : digits point index = true <;>
        simp [selected, ennrealPiecewise, present]
    rw [equal]
    exact ENNRealMeasurable.piecewise (events index)
      (ENNRealMeasurable.constant source (ENNReal.ofReal (unitRationalBasis index).val))
      (ENNRealMeasurable.constant source ENNReal.zero)
  unfold value
  intro region measurable
  exact (ENNRealMeasurable.iSup selections).measurableMap (unitClampMeasurable measurable)

end Foundations.Measure.Coding.Unit
