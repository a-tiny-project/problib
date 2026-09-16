module

public import Foundations.QuasiBorel.SFinite.Bind
public import Foundations.QuasiBorel.SFinite.Standard.Presentation

set_option autoImplicit false

/-!
# Bind transport for standard-Borel presentations

This module proves the measure-level bind transport formula for variable
standard-Borel presentations of s-finite quasi-Borel laws.
-/

namespace Foundations.QuasiBorel.SFinite.Standard.Presentation

public section

open Foundations.Measure hiding Space

universe u v w

variable {domain : Space.{0, u} realSource} {codomain : Space.{0, v} realSource}

/-- Proves that monadic bind of a standard-Borel presentation transports to source measure bind. -/
theorem bind_toMeasure (presentation : Presentation.{u, w} domain)
    (kernel : Hom domain (object codomain)) :
    (bind presentation.toLaw kernel).val = presentation.sourceMeasure.bind
      ((toKernel kernel).precomp presentation.random presentation.measurable) :=
  Measure.bind_map presentation.sourceMeasure presentation.random presentation.measurable (toKernel kernel)

end

end Foundations.QuasiBorel.SFinite.Standard.Presentation
