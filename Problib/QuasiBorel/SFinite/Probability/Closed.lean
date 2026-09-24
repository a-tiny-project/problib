import Problib.QuasiBorel.SFinite.Probability.Strength
import Problib.QuasiBorel.SFinite.Closed
import Problib.QuasiBorel.Probability.Closed

/-!
# Cartesian closed exponential evaluation under s-finite inclusion

This module proves that the inclusion of probability laws into s-finite laws
preserves internalized bind evaluation on exponential spaces, internal extension,
and contextual bind.
-/

set_option autoImplicit false

namespace Problib.QuasiBorel.SFinite

universe u v w

variable {domain : Space.{0, u} realSource} {codomain : Space.{0, v} realSource}

/-- Internalized bind value evaluation commutes with inclusion into s-finite laws. -/
theorem ofProbability_bindValue (kernel : Hom domain (Probability.object codomain))
    (law : Probability.Law domain) :
    ofProbability (Probability.bindValue domain codomain (kernel, law)) =
      bindValue domain codomain (Hom.comp (ofProbabilityHom codomain) kernel, ofProbability law) := by
  rw [Probability.bindValue_apply, bindValue_apply]
  exact ofProbability_bind law kernel

/-- Internal continuation extension commutes with inclusion into s-finite laws. -/
theorem of_probability_internalExtend (kernel : Hom domain (Probability.object codomain)) :
    Hom.comp (ofProbabilityHom codomain) (Probability.internalExtend domain codomain kernel) =
      Hom.comp (internalExtend domain codomain (Hom.comp (ofProbabilityHom codomain) kernel))
        (ofProbabilityHom domain) := by
  rw [Probability.internalExtend_apply, internalExtend_apply]
  exact of_probability_extend kernel

/-- Contextual bind morphism on parameter spaces commutes with inclusion into s-finite laws. -/
theorem of_probability_bindContext {parameter : Space.{0, w} realSource}
    (laws : Hom parameter (Probability.object domain))
    (kernel : Hom (Space.product parameter domain) (Probability.object codomain)) :
    Hom.comp (ofProbabilityHom codomain) (Probability.bindContext laws kernel) =
      bindContext (Hom.comp (ofProbabilityHom domain) laws) (Hom.comp (ofProbabilityHom codomain) kernel) := by
  apply Hom.ext
  intro point
  change ofProbability (Probability.bindContext laws kernel point) = _
  rw [Probability.bindContext_apply, bindContext_apply, ofProbability_bind]
  rfl

end Problib.QuasiBorel.SFinite
