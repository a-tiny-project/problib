module

public import Foundations.Measure.Decomposition.ZeroInfinity.Uniqueness.Basic
public import Foundations.Measure.Decomposition.ZeroInfinity.Density
public import Foundations.Measure.Decomposition.ZeroInfinity.Construction
public import Foundations.Measure.Integral.Density.Uniqueness

/-!
# Weighted-measure equivalence for almost-everywhere-infinity equality

This module proves that two measurable densities induce identical weighted
measures if and only if the densities are almost-everywhere-infinity equal.
The characterization requires an s-finite reference measure but no target
finiteness.
-/

set_option autoImplicit false

namespace Foundations.Measure.Measure

open Foundations.Real

universe u

variable {alpha : Type u} {space : Space alpha}

/-- Two measurable densities under an s-finite reference measure induce identical
weighted measures if and only if the densities are almost-everywhere-infinity
equal. -/
public theorem withDensity_eq_iff_aeInfinityEq {measure : Measure space}
    (finite : SFinite measure) (top : TopZeroInfinitySet measure)
    {left right : alpha → ENNReal}
    (leftMeasurable : ENNRealMeasurable space left)
    (rightMeasurable : ENNRealMeasurable space right) :
    measure.withDensity left = measure.withDensity right ↔ top.AEInfinityEq left right := by
  constructor
  · intro equal
    constructor
    · apply Measure.ae_eq_of_withDensity_eq (top.sigmaFinite_complement finite)
        leftMeasurable rightMeasurable
      rw [measure.withDensity_restrict left (space.complement top.zeroInfinity.measurable),
        measure.withDensity_restrict right (space.complement top.zeroInfinity.measurable), equal]
    · exact (ae_zero_iff_of_withDensity_eq leftMeasurable rightMeasurable equal).restrict top.set
  · intro agree
    have inside : (measure.restrict top.set).withDensity left =
        (measure.restrict top.set).withDensity right := by
      rw [IsZeroInfinitySet.withDensity_restrict_eq_restrict_support top.zeroInfinity leftMeasurable,
        IsZeroInfinitySet.withDensity_restrict_eq_restrict_support top.zeroInfinity rightMeasurable]
      apply Measure.restrict_congr_ae
      exact agree.2.mono (fun _ zeros => propext
        ⟨fun leftNonzero rightZero => leftNonzero (zeros.mpr rightZero),
          fun rightNonzero leftZero => rightNonzero (zeros.mp leftZero)⟩)
    have outside : (measure.restrict (Set.complement top.set)).withDensity left =
        (measure.restrict (Set.complement top.set)).withDensity right :=
      Measure.withDensity_congr_ae agree.1
    rw [measure.withDensity_restrict left top.zeroInfinity.measurable,
      measure.withDensity_restrict right top.zeroInfinity.measurable] at inside
    rw [measure.withDensity_restrict left (space.complement top.zeroInfinity.measurable),
      measure.withDensity_restrict right (space.complement top.zeroInfinity.measurable)] at outside
    apply Measure.ext
    intro set setMeasurable
    have insideMass := congrArg (fun current : Measure space => current set) inside
    have outsideMass := congrArg (fun current : Measure space => current set) outside
    rw [(measure.withDensity left).restrict_apply top.set setMeasurable,
      (measure.withDensity right).restrict_apply top.set setMeasurable] at insideMass
    rw [(measure.withDensity left).restrict_apply (Set.complement top.set) setMeasurable,
      (measure.withDensity right).restrict_apply (Set.complement top.set) setMeasurable] at outsideMass
    rw [← (measure.withDensity left).inter_add_difference set top.zeroInfinity.measurable,
      ← (measure.withDensity right).inter_add_difference set top.zeroInfinity.measurable,
      insideMass]
    exact congrArg (fun mass : ENNReal =>
      ENNReal.add ((measure.withDensity right) (Set.inter set top.set)) mass) outsideMass

/-- Two measurable densities reconstructing the same target measure are
almost-everywhere-infinity equal under an s-finite reference measure. -/
public theorem IsDensity.aeInfinityEq {target reference : Measure space}
    {left right : alpha → ENNReal}
    (first : IsDensity target reference left)
    (second : IsDensity target reference right)
    (finite : SFinite reference) (top : TopZeroInfinitySet reference)
    (leftMeasurable : ENNRealMeasurable space left)
    (rightMeasurable : ENNRealMeasurable space right) :
    top.AEInfinityEq left right :=
  (withDensity_eq_iff_aeInfinityEq finite top leftMeasurable rightMeasurable).mp
    (first.eq_withDensity.symm.trans second.eq_withDensity)

end Foundations.Measure.Measure
