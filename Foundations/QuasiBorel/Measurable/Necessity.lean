module

public import Foundations.QuasiBorel.Measurable.Basic

set_option autoImplicit false

namespace Foundations.QuasiBorel

open Foundations.Measure

universe u v w x

public section

variable {Ω : Type u} {α : Type v} {β : Type w}

/-- Quasi-Borel morphism from indiscrete to discrete Boolean space over the
discrete singleton random source. -/
@[expose] def Necessity.singletonSourceHom : Hom
    (Space.ofMeasurable (Foundations.Measure.Space.discrete Unit)
      (Foundations.Measure.Space.indiscrete Bool))
    (Space.ofMeasurable (Foundations.Measure.Space.discrete Unit)
      (Foundations.Measure.Space.discrete Bool)) where
  toFun := fun value => value
  mapRandom := by
    intro random accepted
    exact MeasurableMap.fromDiscrete _ _

/-- The underlying identity function of `singletonSourceHom` is not measurable,
refuting unrestricted measurable-map recovery. -/
theorem Necessity.singletonSourceHom_not_measurable :
    ¬MeasurableMap (Foundations.Measure.Space.indiscrete Bool)
      (Foundations.Measure.Space.discrete Bool) Necessity.singletonSourceHom.toFun := by
  intro measurable
  have accepted := measurable (set := fun value => value = true) True.intro
  rcases (Foundations.Measure.Space.indiscrete_measurable_iff _).mp accepted with empty | whole
  · have impossible : (true = true) = False := congrArg (fun region => region true) empty
    exact impossible.mp rfl
  · have impossible : (false = true) = True := congrArg (fun region => region false) whole
    exact Bool.noConfusion (impossible.mpr True.intro)

end

end Foundations.QuasiBorel
