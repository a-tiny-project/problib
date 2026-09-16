module

public import Foundations.Measure.Integral.Density.Order

set_option autoImplicit false

namespace Foundations.Measure.Measure

open Foundations.Real

universe u

variable {alpha : Type u} {space : Space alpha} {measure : Measure space}

/-- Measurable densities producing the same weighted measure agree almost
everywhere under a sigma-finite reference measure. -/
public theorem ae_eq_of_withDensity_eq {left right : alpha → ENNReal}
    (finite : SigmaFinite measure)
    (leftMeasurable : ENNRealMeasurable space left)
    (rightMeasurable : ENNRealMeasurable space right)
    (equal : measure.withDensity left = measure.withDensity right) :
    measure.AEEq left right := by
  have forward := ae_le_of_withDensity_le finite leftMeasurable rightMeasurable
    (fun set _ => by
      rw [equal]
      exact ENNReal.leRefl _)
  have reverse := ae_le_of_withDensity_le finite rightMeasurable leftMeasurable
    (fun set _ => by
      rw [equal]
      exact ENNReal.leRefl _)
  exact (forward.and reverse).mono
    (fun _ both => ENNReal.leAntisymm both.1 both.2)

/-- Under a sigma-finite reference measure, two density-weighted measures agree
if and only if their measurable densities agree almost everywhere. -/
public theorem withDensity_eq_iff_ae_eq {left right : alpha → ENNReal}
    (finite : SigmaFinite measure)
    (leftMeasurable : ENNRealMeasurable space left)
    (rightMeasurable : ENNRealMeasurable space right) :
    measure.withDensity left = measure.withDensity right ↔
      measure.AEEq left right :=
  ⟨ae_eq_of_withDensity_eq finite leftMeasurable rightMeasurable,
    withDensity_congr_ae⟩

/-- Two density certificates with measurable integrands for the same target
measure have almost-everywhere equal densities under a sigma-finite reference
measure. -/
public theorem IsDensity.ae_eq {target reference : Measure space}
    {left right : alpha → ENNReal}
    (first : IsDensity target reference left)
    (second : IsDensity target reference right)
    (finite : SigmaFinite reference)
    (leftMeasurable : ENNRealMeasurable space left)
    (rightMeasurable : ENNRealMeasurable space right) :
    reference.AEEq left right :=
  ae_eq_of_withDensity_eq finite leftMeasurable rightMeasurable
    (first.eq_withDensity.symm.trans second.eq_withDensity)

end Foundations.Measure.Measure
