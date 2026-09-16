import Foundations.QuasiBorel.CartesianClosed
import Foundations.QuasiBorel.Probability.Strength

set_option autoImplicit false

namespace Foundations.QuasiBorel.Probability

open Foundations.Measure hiding Space
open Foundations.Measure.Real (borel)

universe u v w

/-- Higher-order joint evaluation morphism combining a probability kernel from the exponential space with a probability law into the bound law. -/
noncomputable def bindValue (domain codomain : Space (Source.ofMeasurable borel)) :
    Hom (Space.product (Space.exponential domain (object codomain)) (object domain)) (object codomain) :=
  Hom.comp (extend (Space.evaluate domain (object codomain)))
    (strength (Space.exponential domain (object codomain)) domain)

/-- Evaluating the higher-order bind morphism on a concrete kernel and law pair recovers standard monadic bind. -/
theorem bindValue_apply {domain codomain : Space (Source.ofMeasurable borel)}
    (kernel : Hom domain (object codomain)) (law : Law domain) :
    bindValue domain codomain (kernel, law) = bind law kernel := by
  apply Law.ext
  change (bind (strength (Space.exponential domain (object codomain)) domain (kernel, law))
    (Space.evaluate domain (object codomain))).val = _
  rw [bind_val, strength_val, Giry.bind_map, bind_val]
  rfl

/-- Internalized Kleisli extension as a quasi-Borel morphism between exponential spaces. -/
noncomputable def internalExtend (domain codomain : Space (Source.ofMeasurable borel)) :
    Hom (Space.exponential domain (object codomain))
      (Space.exponential (object domain) (object codomain)) :=
  Space.curry (bindValue domain codomain)

/-- Applying the internalized extension morphism to a concrete kernel yields the standard Kleisli extension morphism. -/
theorem internalExtend_apply {domain codomain : Space (Source.ofMeasurable borel)}
    (kernel : Hom domain (object codomain)) : internalExtend domain codomain kernel = extend kernel := by
  apply Hom.ext
  intro law
  exact bindValue_apply kernel law

/-- Monadic bind in context, composing a parameter-dependent law with a parameter-dependent kernel. -/
noncomputable def bindContext {parameter domain codomain : Space (Source.ofMeasurable borel)}
    (laws : Hom parameter (object domain)) (kernel : Hom (Space.product parameter domain) (object codomain)) :
    Hom parameter (object codomain) :=
  Hom.comp (bindValue domain codomain) (Space.pair (Space.curry kernel) laws)

/-- Pointwise evaluation of bind in context applies monadic bind to the pointwise law and curried kernel. -/
theorem bindContext_apply {parameter domain codomain : Space (Source.ofMeasurable borel)}
    (laws : Hom parameter (object domain)) (kernel : Hom (Space.product parameter domain) (object codomain))
    (point : parameter.Carrier) :
    bindContext laws kernel point = bind (laws point) (Space.curry kernel point) :=
  bindValue_apply (Space.curry kernel point) (laws point)

end Foundations.QuasiBorel.Probability
