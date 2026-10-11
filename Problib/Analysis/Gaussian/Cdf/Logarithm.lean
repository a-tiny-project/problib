module

public import Problib.Analysis.Gaussian.Cdf.Analytic
public import Problib.Analysis.Logarithm.Analytic
public import Problib.Analysis.Logarithm.Derivative
import Problib.Real.Grind

/-! The logarithm of the standard Gaussian distribution function.

A probit link scores `log Φ(x)`, and at large negative scores `Φ(x)` itself
underflows in floating point long before its logarithm does. So the library
states `logCdf` as its own function, for a native lowering that never forms
`Φ(x)`. Since `Φ` is positive everywhere, `logCdf` is defined on the whole
line, analytic, nonpositive, and differentiates to the inverse Mills ratio
`φ(x) / Φ(x)`. Upper tails are `logCdf (-x)`, as for `cdf`.
-/

set_option autoImplicit false

namespace Problib.Analysis.Gaussian

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real
open Problib.Analysis.Real.PowerSeries
open Problib.Analysis.Logarithm

noncomputable section

/-- The logarithm of the standard Gaussian distribution function, `log Φ(x)`. -/
@[expose] public def logCdf (x : Carrier) : Carrier := logIntegral (cdf x)

/-- The logarithm of a probability is nonpositive. -/
public theorem logCdf_nonpositive (x : Carrier) : le (logCdf x) zero := by
  have bound := log_monotone (cdf x) one (cdf_positive x) (cdf_le_one x)
  rwa [log_one] at bound

/-- `logCdf` differentiates to `φ(x) / Φ(x)` at every point. -/
public theorem hasDerivative_logCdf (x : Carrier) :
    HasDerivative logCdf x (div (density zero one x).toReal (cdf x)) := by
  have chain := hasDerivative_comp (hasDerivative_log (cdf_positive x)) (hasDerivative_cdf x)
  rw [mul_comm, ← div_eq_mul_inverse] at chain
  exact chain

/-- `logCdf` is Borel measurable. -/
public theorem logCdf_measurable : MeasurableMap borel borel logCdf :=
  MeasurableMap.comp log_measurable cdf_measurable

/-- `logCdf` is analytic on the whole line. -/
public theorem analytic_on_logCdf :
    AnalyticOn (fun _ : FiniteVector.carrier 1 => True) (fun point => logCdf (point 0)) :=
  analytic_on_log_comp analytic_on_cdf (fun point _ => cdf_positive (point 0))

end

end Problib.Analysis.Gaussian
