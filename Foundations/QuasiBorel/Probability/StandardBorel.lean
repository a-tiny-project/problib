import Foundations.QuasiBorel.Measurable.StandardBorel
import Foundations.QuasiBorel.Probability.Monad

set_option autoImplicit false

namespace Foundations.QuasiBorel.Probability.StandardBorel

open Foundations.Measure hiding Space
open Foundations.Measure.Real (Carrier borel)

universe u v

variable {α : Type u} {β : Type v} {source : Foundations.Measure.Space α}
  {target : Foundations.Measure.Space β}

private theorem forward_measurable (presentation : Foundations.Measure.StandardBorel source) :
    MeasurableMap (Space.ofMeasurable borel source).toMeasurable source (fun point => point) := by
  rw [Space.toMeasurable_ofStandardBorelReal presentation]
  exact MeasurableMap.identity source

private theorem inverse_measurable (presentation : Foundations.Measure.StandardBorel source) :
    MeasurableMap source (Space.ofMeasurable borel source).toMeasurable (fun point => point) := by
  rw [Space.toMeasurable_ofStandardBorelReal presentation]
  exact MeasurableMap.identity source

private def correspondence (presentation : Foundations.Measure.StandardBorel source) :
    MeasurableEquivalence (Space.ofMeasurable borel source).toMeasurable source where
  forward := fun point => point
  inverse := fun point => point
  inverse_forward := fun _ => rfl
  forward_inverse := fun _ => rfl
  forward_measurable := forward_measurable presentation
  inverse_measurable := inverse_measurable presentation

private theorem retract_map (presentation : Foundations.Measure.StandardBorel source)
    (fallback : α) (law : Giry.Law source) :
    Giry.map (presentation.embeddingReal.retract fallback)
        (Space.random_measurable (space := Space.ofMeasurable borel source)
          (presentation.embeddingReal.retract_measurable fallback))
        (Giry.map presentation.embeddingReal.function presentation.embeddingReal.measurable law) =
      Giry.map (correspondence presentation).inverse (correspondence presentation).inverse_measurable law := by
  rw [Giry.map_comp]
  have equal : (fun point => presentation.embeddingReal.retract fallback
      (presentation.embeddingReal.function point)) = (correspondence presentation).inverse :=
    funext (presentation.embeddingReal.retract_forward fallback)
  simp only [equal]
  rfl

/-- Maps a Giry probability law on a standard-Borel space to a representable law on the induced quasi-Borel space through real retraction decoding. -/
noncomputable def ofGiry (presentation : Foundations.Measure.StandardBorel source)
    (law : Giry.Law source) : Law (Space.ofMeasurable borel source) := by
  refine ⟨Giry.map (correspondence presentation).inverse (correspondence presentation).inverse_measurable law, ?_⟩
  let fallback := Classical.choice law.property.nonempty
  refine ⟨⟨presentation.embeddingReal.retract fallback,
    presentation.embeddingReal.retract_measurable fallback,
    Giry.map presentation.embeddingReal.function presentation.embeddingReal.measurable law⟩, ?_⟩
  exact retract_map presentation fallback law

/-- The underlying Giry law of an imported standard-Borel law matches the pushforward along the canonical measurable correspondence. -/
theorem ofGiry_val (presentation : Foundations.Measure.StandardBorel source)
    (law : Giry.Law source) :
    (ofGiry presentation law).val =
      Giry.map (correspondence presentation).inverse (correspondence presentation).inverse_measurable law := rfl

/-- Maps a representable law on the induced quasi-Borel space of a standard-Borel space to a Giry probability law. -/
noncomputable def toGiry (presentation : Foundations.Measure.StandardBorel source)
    (law : Law (Space.ofMeasurable borel source)) : Giry.Law source :=
  Giry.map (correspondence presentation).forward (correspondence presentation).forward_measurable law.val

/-- Round-trip from Giry law through representable QBS law and back is the identity. -/
theorem toGiry_ofGiry (presentation : Foundations.Measure.StandardBorel source)
    (law : Giry.Law source) : toGiry presentation (ofGiry presentation law) = law := by
  unfold toGiry
  rw [ofGiry_val, Giry.map_comp]
  exact Giry.map_id law
  exact (correspondence presentation).forward_measurable

/-- Round-trip from representable QBS law through Giry law and back is the identity. -/
theorem ofGiry_toGiry (presentation : Foundations.Measure.StandardBorel source)
    (law : Law (Space.ofMeasurable borel source)) : ofGiry presentation (toGiry presentation law) = law := by
  apply Law.ext
  rw [ofGiry_val]
  unfold toGiry
  rw [Giry.map_comp]
  exact Giry.map_id law.val
  exact (correspondence presentation).forward_measurable

/-- Quasi-Borel isomorphism mapping the induced Giry law space to the QBS probability space on a standard-Borel carrier. -/
noncomputable def ofGiryHom (presentation : Foundations.Measure.StandardBorel source) :
    Hom (Space.ofMeasurable borel (Giry.space source)) (object (Space.ofMeasurable borel source)) where
  toFun := ofGiry presentation
  mapRandom := by
    intro random accepted
    let fallback := Classical.choice (random Foundations.Real.Construction.Dedekind.zero).property.nonempty
    refine ⟨{
      random := presentation.embeddingReal.retract fallback
      accepted := presentation.embeddingReal.retract_measurable fallback
      kernel := fun seed => Giry.map presentation.embeddingReal.function
        presentation.embeddingReal.measurable (random seed)
      measurable := MeasurableMap.comp
        (Giry.map_measurable presentation.embeddingReal.function presentation.embeddingReal.measurable) accepted
      law := fun seed => retract_map presentation fallback (random seed)
    }⟩

/-- Quasi-Borel isomorphism mapping the QBS probability space on a standard-Borel carrier to the induced Giry law space. -/
noncomputable def toGiryHom (presentation : Foundations.Measure.StandardBorel source) :
    Hom (object (Space.ofMeasurable borel source)) (Space.ofMeasurable borel (Giry.space source)) where
  toFun := toGiry presentation
  mapRandom := by
    intro random accepted
    have measured : MeasurableMap borel (Giry.space (Space.ofMeasurable borel source).toMeasurable)
        (fun seed => (random seed).val) :=
      (Space.measurableMap_iff_random.mp (Probability.toGiry_measurable (Space.ofMeasurable borel source)))
        accepted
    intro region measurable
    exact measured (Giry.map_measurable (correspondence presentation).forward
      (correspondence presentation).forward_measurable measurable)

/-- Composition of toGiryHom and ofGiryHom is the identity morphism on the induced Giry law space. -/
theorem toGiryHom_ofGiryHom (presentation : Foundations.Measure.StandardBorel source) :
    Hom.comp (toGiryHom presentation) (ofGiryHom presentation) =
      Hom.identity (Space.ofMeasurable borel (Giry.space source)) := by
  apply Hom.ext
  exact toGiry_ofGiry presentation

/-- Composition of ofGiryHom and toGiryHom is the identity morphism on the QBS probability space. -/
theorem ofGiryHom_toGiryHom (presentation : Foundations.Measure.StandardBorel source) :
    Hom.comp (ofGiryHom presentation) (toGiryHom presentation) =
      Hom.identity (object (Space.ofMeasurable borel source)) := by
  apply Hom.ext
  exact ofGiry_toGiry presentation

/-- ofGiry preserves the monadic unit (Dirac point mass). -/
theorem ofGiry_pure (presentation : Foundations.Measure.StandardBorel source) (point : α) :
    ofGiry presentation (Giry.pure source point) = pure (Space.ofMeasurable borel source) point := by
  apply Law.ext
  rw [ofGiry_val]
  exact Giry.map_pure (correspondence presentation).inverse (correspondence presentation).inverse_measurable point

/-- ofGiry commutes with functorial pushforward along measurable maps. -/
theorem ofGiry_map (first : Foundations.Measure.StandardBorel source)
    (second : Foundations.Measure.StandardBorel target) (function : α → β)
    (measurable : MeasurableMap source target function) (law : Giry.Law source) :
    map (Hom.ofMeasurable (source := borel) measurable) (ofGiry first law) =
      ofGiry second (Giry.map function measurable law) := by
  apply Law.ext
  rw [map_val, ofGiry_val, ofGiry_val, Giry.map_comp, Giry.map_comp]
  rfl

/-- ofGiry commutes with monadic bind for standard-Borel target spaces. -/
theorem ofGiry_bind (first : Foundations.Measure.StandardBorel source)
    (second : Foundations.Measure.StandardBorel target) (law : Giry.Law source)
    (family : α → Giry.Law target) (measurable : MeasurableMap source (Giry.space target) family) :
    bind (ofGiry first law) (Hom.comp (ofGiryHom second) (Hom.ofMeasurable measurable)) =
      ofGiry second (Giry.bind law family measurable) := by
  apply Law.ext
  rw [bind_val, ofGiry_val, Giry.bind_map, ofGiry_val, Giry.map_bind]
  rfl

/-- A QBS probability kernel between standard-Borel spaces induces a measurable probability kernel between the underlying measurable spaces. -/
theorem kernel_measurable (first : Foundations.Measure.StandardBorel source)
    (second : Foundations.Measure.StandardBorel target)
    (kernel : Hom (Space.ofMeasurable borel source) (object (Space.ofMeasurable borel target))) :
    MeasurableMap source (Giry.space target) (fun point => toGiry second (kernel point)) :=
  Hom.measurable_ofStandardBorelReal first (Hom.comp (toGiryHom second) kernel)

/-- toGiry commutes with monadic bind, recovering the Giry bind of exported kernels. -/
theorem toGiry_bind (first : Foundations.Measure.StandardBorel source)
    (second : Foundations.Measure.StandardBorel target) (law : Law (Space.ofMeasurable borel source))
    (kernel : Hom (Space.ofMeasurable borel source) (object (Space.ofMeasurable borel target))) :
    toGiry second (bind law kernel) =
      Giry.bind (toGiry first law) (fun point => toGiry second (kernel point))
        (kernel_measurable first second kernel) := by
  unfold toGiry
  rw [bind_val, Giry.map_bind, Giry.bind_map]
  rfl
  exact (correspondence first).forward_measurable
  exact (correspondence second).forward_measurable

end Foundations.QuasiBorel.Probability.StandardBorel
