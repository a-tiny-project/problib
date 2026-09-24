module

public import Problib.Analysis.Gaussian.Quadrant

set_option autoImplicit false

namespace Problib.Analysis

open Problib.Real Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

/-- The finite rational half-line mass survives the library's totalized
`ENNReal.toReal` projection. Finiteness is supplied by the quadrant identity. -/
public theorem rationalHalf_projection :
    ENNReal.ofReal (ENNReal.toReal Gaussian.rationalHalf) = Gaussian.rationalHalf :=
  ENNReal.ofReal_toReal Gaussian.rational_finite

/-- Twice the rational half-line integral, projected only after its finiteness
has been proved. Agreement with circle or trigonometric pi is separate. -/
@[expose] public def pi : Carrier :=
  mul (selection.ofRat 2) (ENNReal.toReal Gaussian.rationalHalf)

public theorem pi_positive : lt zero pi := by
  apply mul_positive ofRat_two_positive
  exact (ENNReal.toReal_lt_toReal_iff (show ENNReal.Finite ENNReal.zero from trivial)
    Gaussian.rational_finite).mpr Gaussian.rational_positive

/-- Re-embedding pi recovers twice the original extended-real integral. -/
public theorem pi_ofReal : ENNReal.ofReal pi =
    ENNReal.mul (ENNReal.ofReal (selection.ofRat 2)) Gaussian.rationalHalf := by
  rw [pi, Measure.Real.ofReal_mul ofRat_two_positive.1 (ENNReal.toReal_nonnegative _),
    rationalHalf_projection]

end
end Problib.Analysis
