module

public import Problib.QuasiBorel.CartesianClosed
public import Problib.QuasiBorel.SFinite.Strength

set_option autoImplicit false

/-!
# Internalized bind and Kleisli extension for exponential spaces

This module internalizes monadic bind over quasi-Borel exponential spaces.
It constructs `bindValue` and `internalExtend` via Cartesian closed evaluation
and tensorial strength, and establishes parameterized contextual bind.
-/

namespace Problib.QuasiBorel.SFinite

public section

open Problib.Measure hiding Space

universe u v w

/-- Internalized monadic bind evaluation morphism on exponential-law product spaces. -/
@[expose] noncomputable def bindValue (domain : Space.{0, u} realSource) (codomain : Space.{0, v} realSource) :
    Hom (Space.product (Space.exponential domain (object codomain)) (object domain)) (object codomain) :=
  Hom.comp (extend (Space.evaluate domain (object codomain)))
    (strength (Space.exponential domain (object codomain)) domain)

/-- Proves that internalized bindValue agrees with monadic bind on kernel-law pairs. -/
theorem bindValue_apply {domain : Space.{0, u} realSource} {codomain : Space.{0, v} realSource}
    (kernel : Hom domain (object codomain)) (law : Law domain) :
    bindValue domain codomain (kernel, law) = bind law kernel := by
  apply Law.ext
  change (bind (strength (Space.exponential domain (object codomain)) domain (kernel, law))
    (Space.evaluate domain (object codomain))).val = _
  rw [bind_val, strength_val, Measure.bind_map, bind_val]
  rfl

/-- Internalized Kleisli extension morphism between exponential function spaces. -/
@[expose] noncomputable def internalExtend (domain : Space.{0, u} realSource) (codomain : Space.{0, v} realSource) :
    Hom (Space.exponential domain (object codomain))
      (Space.exponential (object domain) (object codomain)) :=
  Space.curry (bindValue domain codomain)

/-- Proves that internalized internalExtend agrees with the Kleisli extend operation. -/
theorem internalExtend_apply {domain : Space.{0, u} realSource} {codomain : Space.{0, v} realSource}
    (kernel : Hom domain (object codomain)) : internalExtend domain codomain kernel = extend kernel := by
  apply Hom.ext
  intro law
  exact bindValue_apply kernel law

/-- Internalized contextual bind for parameter-dependent law families and kernels. -/
@[expose] noncomputable def bindContext {parameter : Space.{0, u} realSource}
    {domain : Space.{0, v} realSource} {codomain : Space.{0, w} realSource}
    (laws : Hom parameter (object domain)) (kernel : Hom (Space.product parameter domain) (object codomain)) :
    Hom parameter (object codomain) :=
  Hom.comp (bindValue domain codomain) (Space.pair (Space.curry kernel) laws)

/-- Proves that contextual bind evaluates pointwise to monadic bind of the law against the curried kernel. -/
theorem bindContext_apply {parameter : Space.{0, u} realSource}
    {domain : Space.{0, v} realSource} {codomain : Space.{0, w} realSource}
    (laws : Hom parameter (object domain)) (kernel : Hom (Space.product parameter domain) (object codomain))
    (point : parameter.Carrier) :
    bindContext laws kernel point = bind (laws point) (Space.curry kernel point) :=
  bindValue_apply (Space.curry kernel point) (laws point)

end

end Problib.QuasiBorel.SFinite
