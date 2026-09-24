module

public import Problib.Measure.Distribution.Measure
public import Problib.Measure.Real.Uniqueness

set_option autoImplicit false

namespace Problib.Measure.Real

open Problib.Real
open Problib.Real.Construction

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
    exact ENNReal.ofReal_toReal_finite NNReal.one
  apply finite_measure_ext_unitInitial probability.to_finite distribution.measure_isProbability.to_finite
  intro point
  rw [reconstruct, distribution.measure_initial]

end

end Problib.Measure.Real
