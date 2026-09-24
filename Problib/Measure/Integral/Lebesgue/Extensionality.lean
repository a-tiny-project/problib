module

public import Problib.Measure.Integral.Lebesgue.Algebra

set_option autoImplicit false

/-!
# Extensionality of measures through nonnegative Lebesgue integrals

This module characterizes equality of measures through agreement of Lebesgue
integrals against all nonnegative measurable functions.
The equivalence holds without s-finiteness premises on either measure.
-/

namespace Problib.Measure

open Problib.Real (ENNReal)

universe u

/-- Two measures agree if and only if their Lebesgue integrals against every
nonnegative extended real measurable function coincide. -/
public theorem Measure.eq_iff_lintegral {alpha : Type u} {space : Space alpha}
    (left right : Measure space) :
    left = right ↔ ∀ function : alpha → ENNReal, ENNRealMeasurable space function →
      lintegral left function = lintegral right function := by
  constructor
  · intro equal function measurable
    rw [equal]
  · intro equal
    apply Measure.ext
    intro region measurable
    have integrals := equal (ennrealIndicator region (fun _ => ENNReal.one))
      (ENNRealMeasurable.indicator measurable (ENNRealMeasurable.constant space ENNReal.one))
    simpa only [lintegral_indicator _ region measurable, lintegral_const,
      ENNReal.one_mul, Measure.restrict_apply_univ] using integrals

end Problib.Measure
