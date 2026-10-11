import Problib.QuasiBorel.SFinite.Probability.Inclusion
import Problib.QuasiBorel.SFinite.Monad
import Problib.QuasiBorel.Probability.Monad

/-!
# Probability monad operations under s-finite inclusion

This module proves that the canonical inclusion from probability laws to
s-finite laws preserves Dirac units, pushforward functorial maps, monadic bind,
and Kleisli extension.
-/

set_option autoImplicit false

namespace Problib.QuasiBorel.SFinite

open Problib.Measure hiding Space

universe u v

variable {domain : Space.{0, u} realSource} {codomain : Space.{0, v} realSource}

/-- Probability Dirac unit inclusion equals the s-finite Dirac unit. -/
@[simp] theorem ofProbability_pure (point : domain.Carrier) :
    ofProbability (Probability.pure domain point) = pure domain point := by
  apply Law.ext
  rfl

/-- Pushforward map on probability laws commutes with inclusion into s-finite laws. -/
theorem ofProbability_map (function : Hom domain codomain) (law : Probability.Law domain) :
    ofProbability (Probability.map function law) = map function (ofProbability law) := by
  apply Law.ext
  rw [ofProbability_val, map_val, ofProbability_val, Probability.map_val]
  rfl

theorem toKernel_of_probability (kernel : Hom domain (Probability.object codomain)) :
    toKernel (Hom.comp (ofProbabilityHom codomain) kernel) =
      Giry.toKernel (fun point => (kernel point).val) (Probability.kernel_measurable kernel) := by
  apply Kernel.ext
  intro point
  rfl

/-- Monadic bind of probability laws commutes with inclusion into s-finite laws. -/
theorem ofProbability_bind (law : Probability.Law domain)
    (kernel : Hom domain (Probability.object codomain)) :
    ofProbability (Probability.bind law kernel) =
      bind (ofProbability law) (Hom.comp (ofProbabilityHom codomain) kernel) := by
  apply Law.ext
  rw [ofProbability_val, bind_val, ofProbability_val, toKernel_of_probability, Probability.bind_val]
  rfl

theorem of_probability_unit (space : Space.{0, u} realSource) :
    Hom.comp (ofProbabilityHom space) (Probability.unit space) = unit space := by
  apply Hom.ext
  exact ofProbability_pure

theorem of_probability_natural (function : Hom domain codomain) :
    Hom.comp (ofProbabilityHom codomain) (Probability.map function) =
      Hom.comp (map function) (ofProbabilityHom domain) := by
  apply Hom.ext
  exact ofProbability_map function

theorem of_probability_extend (kernel : Hom domain (Probability.object codomain)) :
    Hom.comp (ofProbabilityHom codomain) (Probability.extend kernel) =
      Hom.comp (extend (Hom.comp (ofProbabilityHom codomain) kernel)) (ofProbabilityHom domain) := by
  apply Hom.ext
  intro law
  exact ofProbability_bind law kernel

end Problib.QuasiBorel.SFinite
