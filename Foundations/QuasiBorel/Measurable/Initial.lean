module

public import Foundations.QuasiBorel.Initial
public import Foundations.QuasiBorel.Measurable.Induced

set_option autoImplicit false

/-!
# Induced measurable space of the initial quasi-Borel space

This module proves that the induced measurable space of the initial quasi-Borel
space is the discrete measurable space on `PEmpty`.
-/
namespace Foundations.QuasiBorel.Space

universe u v

/-- Proves that the induced measurable space of the initial quasi-Borel space
is the discrete measurable space on `PEmpty`. -/
public theorem toMeasurable_initial {Ω : Type u} (source : Foundations.Measure.Space Ω) :
    (initial.{u, v} (Source.ofMeasurable source)).toMeasurable =
      Foundations.Measure.Space.discrete PEmpty.{v + 1} := by
  apply Foundations.Measure.Space.ext
  intro region
  constructor
  · intro _
    exact True.intro
  · intro _ random accepted
    exact accepted.elim

end Foundations.QuasiBorel.Space
