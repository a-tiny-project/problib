module

public import Foundations.QuasiBorel.SFinite.Closed
public import Foundations.QuasiBorel.SFinite.Standard.Bind
public import Foundations.Measure.Kernel.Product

set_option autoImplicit false

/-!
# Commutativity of independent s-finite quasi-Borel binds

This module proves that independent monadic binds commute in the s-finite
quasi-Borel monad (Vakár & Ong 2018 / 2026-05-05 arXiv:1810.01837v2 Theorem 19).
Commutativity is established on standard-Borel presentations via Tonelli's theorem
on source measures and transported to canonical law quotients.
-/

namespace Foundations.QuasiBorel.SFinite

public section

open Foundations.Measure hiding Space
open Foundations.Measure.Real (borel)

universe u v w x y

variable {left : Space.{0, u} realSource} {right : Space.{0, v} realSource}
  {target : Space.{0, w} realSource}

private theorem bind_context_source (first : Standard.Presentation.{u, x} left)
    (second : Standard.Presentation.{v, y} right)
    (family : Hom (Space.product left right) (object target))
    {region : Set target.Carrier} (measurable : target.toMeasurable.Measurable region) :
    (bind first.toLaw (bindContext (Hom.constant left (object right) second.toLaw) family)).val region =
      lintegral first.sourceMeasure (fun firstSeed => lintegral second.sourceMeasure
        (fun secondSeed => (family (first.random firstSeed, second.random secondSeed)).val region)) := by
  rw [Standard.Presentation.bind_toMeasure, Measure.bind_apply _ _ @measurable]
  apply lintegral_congr
  intro firstSeed
  change (bindContext (Hom.constant left (object right) second.toLaw) family
    (first.random firstSeed)).val region = _
  rw [bindContext_apply]
  change (bind second.toLaw (Space.curry family (first.random firstSeed))).val region = _
  rw [Standard.Presentation.bind_toMeasure, Measure.bind_apply _ _ @measurable]
  rfl

/-- Proves independent bind commutativity for standard-Borel presentations via Tonelli integration on source measures. -/
theorem Standard.Presentation.bind_comm (first : Standard.Presentation.{u, x} left)
    (second : Standard.Presentation.{v, y} right)
    (family : Hom (Space.product left right) (object target)) :
    bind first.toLaw (bindContext (Hom.constant left (object right) second.toLaw) family) =
      bind second.toLaw (bindContext (Hom.constant right (object left) first.toLaw)
        (Hom.comp family (Space.swap right left))) := by
  apply Law.ext
  apply Measure.ext
  intro region measurable
  rw [bind_context_source first second family @measurable,
    bind_context_source second first (Hom.comp family (Space.swap right left)) @measurable]
  let joint : Hom (Space.ofMeasurable borel (Foundations.Measure.Space.product first.source second.source))
      (Space.product left right) :=
    Space.pair
      (Hom.comp first.random (Hom.ofMeasurable
        (Foundations.Measure.Space.first_measurable first.source second.source)))
      (Hom.comp second.random (Hom.ofMeasurable
        (Foundations.Measure.Space.second_measurable first.source second.source)))
  have jointMeasurable : MeasurableMap
      (Foundations.Measure.Space.product first.source second.source)
      (Space.product left right).toMeasurable joint :=
    joint.toMeasurable_ofEmbedding (first.standard.product second.standard).embeddingReal
  have integrand : ENNRealMeasurable (Foundations.Measure.Space.product first.source second.source)
      (fun point => (family (first.random point.1, second.random point.2)).val region) :=
    ENNRealMeasurable.comp (evaluation_measurable target @measurable)
      (MeasurableMap.comp family.toMeasurable jointMeasurable)
  exact (lintegral_prod first.sourceMeasure second.sourceMeasure second.sfinite integrand).symm.trans
    (lintegral_prod_symm first.sourceMeasure second.sourceMeasure first.sfinite second.sfinite integrand)

/-- Proves independent bind commutativity for arbitrary s-finite quasi-Borel laws. -/
theorem bind_comm (first : Law left) (second : Law right)
    (family : Hom (Space.product left right) (object target)) :
    bind first (bindContext (Hom.constant left (object right) second) family) =
      bind second (bindContext (Hom.constant right (object left) first)
        (Hom.comp family (Space.swap right left))) := by
  have law := Standard.Presentation.bind_comm
    (Standard.Presentation.ofPartial first.presentation)
    (Standard.Presentation.ofPartial second.presentation) family
  simpa only [Standard.Presentation.ofPartial_toLaw, Law.presentation_toLaw] using law

end

end Foundations.QuasiBorel.SFinite
