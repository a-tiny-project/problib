module

public import Foundations.QuasiBorel.SFinite.Standard.Presentation
public import Foundations.Measure.Integral.Lebesgue.Extensionality
public import Foundations.Measure.Integral.Lebesgue.Transport

set_option autoImplicit false

/-!
# Nonnegative Lebesgue integrals of standard-Borel presentations

This module interprets standard-Borel presentations as nonnegative Lebesgue
integral operators.
It characterizes equality of presented measures and laws through agreement
of integrals against nonnegative measurable functions across independent
source universes.
-/

namespace Foundations.QuasiBorel.SFinite.Standard.Presentation

public section

open Foundations.Measure hiding Space
open Foundations.Real (ENNReal)

universe u v w

variable {space : Space.{0, u} realSource}

/-- Evaluates a standard presentation as an integral operator on nonnegative
functions through source integration. -/
@[expose] noncomputable def integral (presentation : Presentation.{u, v} space)
    (function : space.Carrier → ENNReal) : ENNReal :=
  lintegral presentation.sourceMeasure (fun seed => function (presentation.random seed))

/-- Proves that the Lebesgue integral against the presented measure coincides
with the presentation integral on measurable functions. -/
theorem toMeasure_lintegral (presentation : Presentation.{u, v} space)
    {function : space.Carrier → ENNReal} (measurable : ENNRealMeasurable space.toMeasurable function) :
    lintegral presentation.toMeasure function = presentation.integral function :=
  lintegral_map presentation.sourceMeasure presentation.random presentation.measurable measurable

/-- Proves that two standard presentations induce the same measure if and only
if their integrals agree for all nonnegative measurable functions. -/
theorem toMeasure_eq_iff_integral (left : Presentation.{u, v} space)
    (right : Presentation.{u, w} space) :
    left.toMeasure = right.toMeasure ↔
      ∀ function : space.Carrier → ENNReal, ENNRealMeasurable space.toMeasurable function →
        left.integral function = right.integral function := by
  rw [Measure.eq_iff_lintegral]
  constructor
  · intro equal function measurable
    rw [← left.toMeasure_lintegral measurable, ← right.toMeasure_lintegral measurable]
    exact equal function measurable
  · intro equal function measurable
    rw [left.toMeasure_lintegral measurable, right.toMeasure_lintegral measurable]
    exact equal function measurable

/-- Proves that two standard presentations define the same law if and only if
their integrals agree for all nonnegative measurable functions. -/
theorem toLaw_eq_iff_integral (left : Presentation.{u, v} space)
    (right : Presentation.{u, w} space) :
    left.toLaw = right.toLaw ↔
      ∀ function : space.Carrier → ENNReal, ENNRealMeasurable space.toMeasurable function →
        left.integral function = right.integral function := by
  rw [← toMeasure_eq_iff_integral]
  constructor
  · intro equal
    exact congrArg Subtype.val equal
  · intro equal
    apply Law.ext
    exact equal

end

end Foundations.QuasiBorel.SFinite.Standard.Presentation
