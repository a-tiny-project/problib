module

public import Problib.Measure.Integral.Density.Algebra
public import Problib.Measure.Integral.Density.AlmostEverywhere
public import Problib.Measure.Integral.Lebesgue.Zero

set_option autoImplicit false

namespace Problib.Measure.Measure

open Problib.Real

universe u

variable {alpha : Type u} {space : Space alpha} {measure : Measure space}

/-- A density-weighted measure is zero if and only if the measurable density
vanishes almost everywhere. -/
public theorem withDensity_eq_zero_iff {density : alpha → ENNReal}
    (measurable : ENNRealMeasurable space density) :
    measure.withDensity density = Measure.zero space ↔
      measure.AEEq density (fun _ => ENNReal.zero) := by
  constructor
  · intro equal
    have massZero := congrArg (fun current : Measure space => current Set.univ) equal
    rw [measure.withDensity_apply density space.univ,
      measure.restrict_univ, Measure.zero_apply] at massZero
    exact ae_zero_of_lintegral_eq_zero measurable massZero
  · intro equal
    exact (withDensity_congr_ae equal).trans measure.withDensity_zero

/-- A measurable set has zero weighted measure under a measurable density if
and only if its intersection with the nonzero support has zero reference measure. -/
public theorem withDensity_apply_eq_zero_iff {reference : Measure space} {density : alpha → ENNReal}
    (measurable : ENNRealMeasurable space density) {set : Set alpha}
    (setMeasurable : space.Measurable set) :
    (reference.withDensity density) set = ENNReal.zero ↔
      reference (Set.inter set (fun value => density value ≠ ENNReal.zero)) = ENNReal.zero := by
  rw [reference.withDensity_apply density setMeasurable, lintegral_eq_zero_iff measurable]
  change (reference.restrict set) (fun value => density value ≠ ENNReal.zero) = ENNReal.zero ↔ _
  have supportMeasurable : space.Measurable (fun value => density value ≠ ENNReal.zero) :=
    space.complement (measurable.eq_set (ENNRealMeasurable.constant space ENNReal.zero))
  rw [reference.restrict_apply set supportMeasurable, Set.inter_comm]

/-- Measurable densities producing identical weighted measures agree almost
everywhere on zero versus strictly positive values without finiteness premises. -/
public theorem ae_zero_iff_of_withDensity_eq {measure : Measure space} {left right : alpha → ENNReal}
    (leftMeasurable : ENNRealMeasurable space left)
    (rightMeasurable : ENNRealMeasurable space right)
    (equal : measure.withDensity left = measure.withDensity right) :
    measure.AE (fun value => left value = ENNReal.zero ↔ right value = ENNReal.zero) := by
  have directional : ∀ (first second : alpha → ENNReal),
      ENNRealMeasurable space first → ENNRealMeasurable space second →
      measure.withDensity first = measure.withDensity second →
      measure.NullSet (Set.inter (fun value => first value = ENNReal.zero)
        (fun value => second value ≠ ENNReal.zero)) := by
    intro first second firstMeasurable secondMeasurable equal
    have zerosMeasurable := firstMeasurable.eq_set
      (ENNRealMeasurable.constant space ENNReal.zero)
    apply (Measure.withDensity_apply_eq_zero_iff secondMeasurable zerosMeasurable).mp
    rw [← equal]
    apply (Measure.withDensity_apply_eq_zero_iff firstMeasurable zerosMeasurable).mpr
    apply measure.null_empty.mono
    intro value member
    exact member.2 member.1
  have forward := directional left right leftMeasurable rightMeasurable equal
  have reverse := directional right left rightMeasurable leftMeasurable equal.symm
  apply (forward.union reverse).mono
  intro value failure
  classical
  by_cases leftZero : left value = ENNReal.zero
  · exact Or.inl ⟨leftZero, fun rightZero => failure ⟨fun _ => rightZero, fun _ => leftZero⟩⟩
  · exact Or.inr ⟨Classical.byContradiction (fun rightNonzero =>
      failure ⟨fun zero => False.elim (leftZero zero), fun zero => False.elim (rightNonzero zero)⟩), leftZero⟩

end Problib.Measure.Measure
