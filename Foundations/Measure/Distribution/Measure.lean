module

public import Foundations.Measure.Distribution.Quantile
public import Foundations.Measure.Uniform

set_option autoImplicit false

namespace Foundations.Measure.Real

open Foundations.Real
open Foundations.Real.Construction

public section

/-- Probability measure induced on `unitBorel` by pushing the uniform measure
`uniform01` through the measurable quantile function `Q`. -/
@[expose] noncomputable def DistributionFunction.measure (distribution : DistributionFunction) : Measure unitBorel :=
  uniform01.map distribution.quantile distribution.quantile_measurable

theorem DistributionFunction.measure_isProbability (distribution : DistributionFunction) :
    Measure.IsProbability distribution.measure :=
  uniform01_isProbability.map distribution.quantile distribution.quantile_measurable

/-- Reconstruction equation: the pushforward measure assigns mass `F(x)` to each
initial closed interval `[0, x]`. -/
theorem DistributionFunction.measure_initial (distribution : DistributionFunction) (point : UnitInterval) :
    distribution.measure (unitInitial point) =
      ENNReal.ofReal (distribution.function point).val := by
  rw [DistributionFunction.measure,
    Measure.map_apply uniform01 distribution.quantile distribution.quantile_measurable
      (unitInitialMeasurable point)]
  have same : Set.preimage distribution.quantile (unitInitial point) =
      unitInitial (distribution.function point) := by
    apply Set.ext
    intro threshold
    exact distribution.quantile_le_iff threshold point
  rw [same, uniform01_unitInitial]

end

end Foundations.Measure.Real
