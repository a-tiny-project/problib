import Problib.QuasiBorel.SFinite.Probability.Normalized
import Problib.QuasiBorel.SFinite.Scale
import Problib.QuasiBorel.Probability.Monad
import Problib.Measure.Extended.Ratio
import Problib.Measure.Normalization

/-!
# Normalization of s-finite law families

This module assembles normalization as a quasi-Borel morphism. A family of
s-finite laws whose mass is finite and nonzero at every point normalizes to a
family of probability laws:

```
normalize f = toProbabilityHom ∘ subtypeLift (scale ∘ ⟨reciprocal ∘ mass, id⟩ ∘ f)
```

The reciprocal weight is the measurable density ratio `1 / w`, so no new
random-family argument is needed. Each normalized law is the measure-level
`Measure.normalize` of its input. Normalization fixes probability families,
ignores finite nonzero rescaling, and commutes with pushforward.
-/

set_option autoImplicit false

namespace Problib.QuasiBorel.SFinite

open Problib.Measure hiding Space
open Problib.Real (ENNReal NNReal)

universe u v w

/-- Reciprocal weight `w ↦ 1 / w` as a quasi-Borel endomorphism of the weight space. -/
noncomputable def reciprocal : Hom weightSpace weightSpace :=
  Hom.ofMeasurable (ENNRealMeasurable.densityRatio
    (ENNRealMeasurable.constant ennrealBorel ENNReal.one) ENNRealMeasurable.identity).measurableMap

@[simp] theorem reciprocal_apply (weight : ENNReal) :
    reciprocal weight = ENNReal.densityRatio ENNReal.one weight := rfl

/-- Scaling a normalizable measure by the reciprocal of its mass normalizes it. -/
private theorem smul_reciprocal_eq_normalize {α : Type v} {measurable : Problib.Measure.Space α}
    (measure : Measure measurable) (defined : Measure.IsNormalizable measure) :
    Measure.smul (ENNReal.densityRatio ENNReal.one (measure Set.univ)) measure =
      Measure.normalize measure defined := by
  rcases ENNReal.exists_finite_of_finite defined.finite.univ_finite with ⟨mass, total⟩
  have nonzero : mass ≠ NNReal.zero := by
    intro equal
    apply defined.nonzero
    rw [total, equal]
    rfl
  have inverse : ENNReal.mul (measure Set.univ)
      (ENNReal.finite (NNReal.div NNReal.one mass)) = ENNReal.one := by
    rw [total]
    change ENNReal.finite (NNReal.mul mass (NNReal.div NNReal.one mass)) = ENNReal.one
    rw [NNReal.mul_div_cancel NNReal.one nonzero]
    rfl
  have ratio := ENNReal.densityRatio_mul_of_finite defined.finite.univ_finite
    defined.nonzero (ENNReal.finite (NNReal.div NNReal.one mass))
  rw [inverse] at ratio
  rw [ratio, Measure.normalize_eq_of_total_eq measure defined total]

variable {space : Space.{0, u} realSource}

/-- Rescale an s-finite law by the reciprocal of its total mass. -/
noncomputable def rescale (space : Space.{0, u} realSource) : Hom (object space) (object space) :=
  Hom.comp (scale space)
    (Space.pair (Hom.comp reciprocal (mass space)) (Hom.identity (object space)))

theorem rescale_val (law : Law space) :
    (rescale space law).val =
      Measure.smul (ENNReal.densityRatio ENNReal.one (law.val Set.univ)) law.val :=
  scale_val (ENNReal.densityRatio ENNReal.one (law.val Set.univ)) law

/-- On a law of finite nonzero mass, rescaling is measure-level normalization. -/
theorem rescale_eq_normalize (law : Law space) (ready : Measure.IsNormalizable law.val) :
    (rescale space law).val = Measure.normalize law.val ready := by
  rw [rescale_val]
  exact smul_reciprocal_eq_normalize law.val ready

theorem rescale_probability (law : Law space) (ready : Measure.IsNormalizable law.val) :
    Measure.IsProbability (rescale space law).val := by
  rw [rescale_eq_normalize law ready]
  exact Measure.normalize_isProbability law.val ready

variable {domain : Space.{0, v} realSource}

/-- Normalize a family of s-finite laws whose mass is finite and nonzero at every point. -/
noncomputable def normalize (family : Hom domain (object space))
    (ready : ∀ point, Measure.IsNormalizable (family point).val) :
    Hom domain (Probability.object space) :=
  Hom.comp (Normalized.toProbabilityHom space)
    ((Hom.comp (rescale space) family).subtypeLift (fun law => Measure.IsProbability law.val)
      (fun point => rescale_probability (family point) (ready point)))

/-- Each normalized law is the measure-level normalization of its input. -/
theorem normalize_val (family : Hom domain (object space))
    (ready : ∀ point, Measure.IsNormalizable (family point).val) (point : domain.Carrier) :
    (normalize family ready point).val.val = Measure.normalize (family point).val (ready point) :=
  rescale_eq_normalize (family point) (ready point)

/-- Normalization fixes families of probability laws. -/
theorem normalize_ofProbability (family : Hom domain (Probability.object space))
    (ready : ∀ point,
      Measure.IsNormalizable ((Hom.comp (ofProbabilityHom space) family) point).val) :
    normalize (Hom.comp (ofProbabilityHom space) family) ready = family := by
  apply Hom.ext
  intro point
  apply Probability.Law.ext
  apply Subtype.ext
  rw [normalize_val]
  exact Measure.normalize_eq_self (ofProbability_probability (family point))

/-- Normalization ignores a pointwise weight that keeps every law normalizable. -/
theorem normalize_scale (weight : Hom domain weightSpace) (family : Hom domain (object space))
    (ready : ∀ point, Measure.IsNormalizable (family point).val)
    (scaledReady : ∀ point, Measure.IsNormalizable
      ((Hom.comp (scale space) (Space.pair weight family)) point).val) :
    normalize (Hom.comp (scale space) (Space.pair weight family)) scaledReady =
      normalize family ready := by
  apply Hom.ext
  intro point
  apply Probability.Law.ext
  apply Subtype.ext
  rw [normalize_val, normalize_val]
  have equal := scale_val (weight point) (family point)
  have scaled : Measure.IsNormalizable (Measure.smul (weight point) (family point).val) :=
    equal ▸ scaledReady point
  exact (Measure.normalize_congr equal (scaledReady point) scaled).trans
    (Measure.normalize_smul (family point).val (ready point) (weight point) scaled)

/-- Normalization commutes with pushforward along a quasi-Borel morphism. -/
theorem map_normalize {target : Space.{0, w} realSource} (function : Hom space target)
    (family : Hom domain (object space))
    (ready : ∀ point, Measure.IsNormalizable (family point).val)
    (mappedReady : ∀ point,
      Measure.IsNormalizable ((Hom.comp (map function) family) point).val) :
    Hom.comp (Probability.map function) (normalize family ready) =
      normalize (Hom.comp (map function) family) mappedReady := by
  apply Hom.ext
  intro point
  apply Probability.Law.ext
  apply Subtype.ext
  rw [normalize_val, Hom.comp_apply, Probability.map_val]
  change (normalize family ready point).val.val.map function function.toMeasurable = _
  rw [normalize_val, ← Measure.normalize_map]
  exact Measure.normalize_congr (map_val function (family point)).symm _ _

end Problib.QuasiBorel.SFinite
