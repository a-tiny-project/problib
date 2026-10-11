module

public import Problib.QuasiBorel.Initial
public import Problib.QuasiBorel.Measurable.Induced

set_option autoImplicit false

/-!
# Induced measurable space of the initial quasi-Borel space

This module proves that the induced measurable space of the initial quasi-Borel
space is the discrete measurable space on `PEmpty`.
-/
namespace Problib.QuasiBorel.Space

universe u v

/-- Proves that the induced measurable space of the initial quasi-Borel space
is the discrete measurable space on `PEmpty`. -/
public theorem toMeasurable_initial {Ω : Type u} (source : Problib.Measure.Space Ω) :
    (initial.{u, v} (Source.ofMeasurable source)).toMeasurable =
      Problib.Measure.Space.discrete PEmpty.{v + 1} := by
  apply Problib.Measure.Space.ext
  intro region
  constructor
  · intro _
    exact True.intro
  · intro _ random accepted
    exact accepted.elim

end Problib.QuasiBorel.Space
