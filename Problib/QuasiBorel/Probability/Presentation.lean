import Problib.Measure.Kernel.Presentation
import Problib.QuasiBorel.Probability.Representation

set_option autoImplicit false

/-!
# Quasi-Borel presentations as kernel presentations

A quasi-Borel probability presentation pushes a law on the real random source
forward along an accepted random element. That is a kernel presentation whose
trace is the random source, constant in the input.
-/

namespace Problib.Measure.Kernel

open Problib.Measure.Real (Carrier borel)

universe u

/-- The kernel presentation of a quasi-Borel probability presentation: the
trace is the real random source, the joint is the source law at every input,
and the return is the accepted random element. -/
noncomputable def Presentation.ofQuasiBorel {α : Type u} (source : Space α)
    {space : QuasiBorel.Space (QuasiBorel.Source.ofMeasurable borel)}
    (presentation : QuasiBorel.Probability.Presentation space) :
    Presentation.{u, _, 0} (Kernel.const source presentation.toGiry.val) where
  Trace := Carrier
  space := borel
  joint := Kernel.const source presentation.sourceLaw.val
  finite := (IsFinite.const source presentation.sourceLaw.property.to_finite).toSFinite
  ret := fun pair => presentation.random pair.2
  measurable := MeasurableMap.comp (QuasiBorel.Space.random_measurable presentation.accepted)
    (Space.second_measurable source borel)
  presents := fun _ => rfl

end Problib.Measure.Kernel
