module

public import Foundations.Measure.Distribution.Measure
public import Foundations.Measure.Real.Uniqueness

set_option autoImplicit false

namespace Foundations.Measure.Real

open Foundations.Real
open Foundations.Real.Construction

public section

/-- Any measure on `unitBorel` satisfying the initial-interval reconstruction
equations equals `distribution.measure`. Probability and finiteness of the
competing measure are derived directly from the upper endpoint equation at
`unitOne` (`measure univ = F(1) = 1`), needing no separate finiteness premise. -/
theorem DistributionFunction.measure_unique (distribution : DistributionFunction)
    {measure : Measure unitBorel}
    (reconstruct : ∀ point, measure (unitInitial point) =
      ENNReal.ofReal (distribution.function point).val) :
    measure = distribution.measure := by
  have probability : Measure.IsProbability measure := by
    constructor
    rw [← unitInitial_one, reconstruct, distribution.upper]
    exact ENNReal.ofRealToRealFinite NNReal.one
  apply finiteMeasure_ext_unitInitial probability.toFinite distribution.measure_isProbability.toFinite
  intro point
  rw [reconstruct, distribution.measure_initial]

end

end Foundations.Measure.Real
