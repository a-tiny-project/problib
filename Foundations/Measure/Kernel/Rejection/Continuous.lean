module

public import Foundations.Measure.Kernel.Rejection.Restriction
public import Foundations.Measure.Uniform

set_option autoImplicit false

namespace Foundations.Measure.Kernel.Rejection
open Foundations.Real

/-- Repeated unit-interval proposals accepted below a positive threshold give the exact normalized interval law. -/
public theorem uniform_initial_retry (upper : Real.UnitInterval)
    (positive : ENNReal.lt ENNReal.zero (ENNReal.ofReal upper.val)) :
    loop (retry (fun _ : Unit => Real.uniform01 (Set.complement (Real.unitInitial upper)))
        (ENNRealMeasurable.constant (Space.discrete Unit) _))
      (Kernel.const (Space.discrete Unit) (Real.uniform01.restrict (Real.unitInitial upper))) () =
      Measure.normalize (Real.uniform01.restrict (Real.unitInitial upper))
        ⟨Real.uniform01_isProbability.toFinite.restrict _, by
          rw [Measure.restrict_apply_univ, Real.uniform01_unitInitial]
          exact ENNReal.zeroLtIffNeZero.mp positive⟩ := by
  apply loop_restriction_retry_eq_normalize Real.uniform01 Real.uniform01_isProbability
    (Real.unitInitial upper) (Real.unitInitialMeasurable upper)
  rw [Real.uniform01_unitInitial]
  exact positive

public theorem uniform_initial_retry_isProbability (upper : Real.UnitInterval)
    (positive : ENNReal.lt ENNReal.zero (ENNReal.ofReal upper.val)) :
    Measure.IsProbability
      (loop (retry (fun _ : Unit => Real.uniform01 (Set.complement (Real.unitInitial upper)))
          (ENNRealMeasurable.constant (Space.discrete Unit) _))
        (Kernel.const (Space.discrete Unit) (Real.uniform01.restrict (Real.unitInitial upper))) ()) := by
  rw [uniform_initial_retry upper positive]
  exact Measure.normalize_isProbability _ _

end Foundations.Measure.Kernel.Rejection
