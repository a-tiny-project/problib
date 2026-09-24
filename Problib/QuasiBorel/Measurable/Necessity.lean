module

public import Problib.QuasiBorel.Measurable.Basic

set_option autoImplicit false

namespace Problib.QuasiBorel

open Problib.Measure

universe u v w x

public section

variable {Ω : Type u} {α : Type v} {β : Type w}

/-- Quasi-Borel morphism from indiscrete to discrete Boolean space over the
discrete singleton random source. -/
@[expose] def Necessity.singletonSourceHom : Hom
    (Space.ofMeasurable (Problib.Measure.Space.discrete Unit)
      (Problib.Measure.Space.indiscrete Bool))
    (Space.ofMeasurable (Problib.Measure.Space.discrete Unit)
      (Problib.Measure.Space.discrete Bool)) where
  toFun := fun value => value
  map_random := by
    intro random accepted
    exact MeasurableMap.from_discrete _ _

/-- The underlying identity function of `singletonSourceHom` is not measurable,
refuting unrestricted measurable-map recovery. -/
theorem Necessity.singletonSourceHom_not_measurable :
    ¬MeasurableMap (Problib.Measure.Space.indiscrete Bool)
      (Problib.Measure.Space.discrete Bool) Necessity.singletonSourceHom.toFun := by
  intro measurable
  have accepted := measurable (set := fun value => value = true) True.intro
  rcases (Problib.Measure.Space.indiscrete_measurable_iff _).mp accepted with empty | whole
  · have impossible : (true = true) = False := congrArg (fun region => region true) empty
    exact impossible.mp rfl
  · have impossible : (false = true) = True := congrArg (fun region => region false) whole
    exact Bool.noConfusion (impossible.mpr True.intro)

end

end Problib.QuasiBorel
