import Foundations.QuasiBorel.SFinite.Probability.Inclusion
import Foundations.QuasiBorel.SFinite.Standard.Family
import Foundations.QuasiBorel.Subtype

/-!
# Quasi-Borel isomorphism between probability laws and mass-one s-finite laws

This module establishes an exact quasi-Borel space isomorphism between
probability laws and the subtype of mass-one s-finite laws. The inverse morphism
converts a mass-one s-finite presentation into a probability presentation.
The success-domain source already has mass one, and `totalRandom` totalizes the
generator by routing failure seeds to the target image of a fallback seed.
This isomorphism reflects and preserves random families without requiring an
inhabited target space or a finite raw source measure.
-/

set_option autoImplicit false

namespace Foundations.QuasiBorel.SFinite

open Foundations.Measure hiding Space
open Foundations.Measure.Real (Carrier borel)
open Foundations.Real (ENNReal)

universe u v

variable {space : Space.{0, u} realSource}

/-- Totalize a partial generator by routing failure seeds to the target image
of a fallback source seed. -/
noncomputable def Standard.Generator.totalRandom (generator : Standard.Generator.{u, v} space)
    (fallback : generator.Seed) : Carrier → space.Carrier :=
  fun seed => Space.copair
    (Hom.constant (Space.terminal realSource) space (generator.random fallback))
    (Hom.identity space) (generator.toPartial.random seed)

theorem Standard.Generator.totalRandom_accepted (generator : Standard.Generator.{u, v} space)
    (fallback : generator.Seed) : space.Random (generator.totalRandom fallback) :=
  (Space.copair (Hom.constant (Space.terminal realSource) space (generator.random fallback))
    (Hom.identity space)).mapRandom generator.toPartial.accepted

theorem Standard.Generator.totalRandom_forward (generator : Standard.Generator.{u, v} space)
    (fallback point : generator.Seed) :
    generator.totalRandom fallback (generator.standard.embeddingReal.function point) =
      generator.random point := by
  unfold totalRandom
  rw [generator.toPartial_forward]
  rfl

theorem Standard.Generator.totalRandom_map (generator : Standard.Generator.{u, v} space)
    (fallback : generator.Seed) (measure : Measure generator.source) :
    (measure.map generator.standard.embeddingReal.function generator.standard.embeddingReal.measurable).map
      (generator.totalRandom fallback) (Space.random_measurable (generator.totalRandom_accepted fallback)) =
        measure.map generator.random generator.measurable := by
  rw [Measure.map_comp]
  have equal : (fun point => generator.totalRandom fallback
      (generator.standard.embeddingReal.function point)) = generator.random :=
    funext (generator.totalRandom_forward fallback)
  simp only [equal]

theorem Standard.Generator.source_probability (generator : Standard.Generator.{u, v} space)
    (measure : Measure generator.source)
    (normalized : Measure.IsProbability (measure.map generator.random generator.measurable)) :
    Measure.IsProbability measure := by
  constructor
  calc
    measure Set.univ = (measure.map generator.random generator.measurable) Set.univ :=
      (Measure.map_apply measure generator.random generator.measurable space.toMeasurable.univ).symm
    _ = ENNReal.one := normalized.univ_eq_one

theorem Standard.Family.kernel_probability {laws : Carrier → Law space}
    (family : Standard.Family.{u, v} space laws)
    (normalized : ∀ seed, Measure.IsProbability (laws seed).val) (seed : Carrier) :
    Measure.IsProbability (family.kernel seed) :=
  family.toGenerator.source_probability (family.kernel seed) (family.law seed ▸ normalized seed)

/-- Every s-finite law with total mass one admits a probability presentation. -/
theorem probability_representable (law : Law space) (normalized : Measure.IsProbability law.val) :
    ∃ presentation : Probability.Presentation space, presentation.toGiry.val = law.val := by
  let presentation := Standard.Presentation.ofPartial law.presentation
  have represented : presentation.toMeasure = law.val :=
    (Standard.Presentation.ofPartial_toMeasure law.presentation).trans law.presentation_toMeasure
  have sourceNormalized : Measure.IsProbability presentation.sourceMeasure :=
    presentation.toGenerator.source_probability presentation.sourceMeasure (by
      change Measure.IsProbability presentation.toMeasure
      rw [represented]
      exact normalized)
  let fallback := Classical.choice sourceNormalized.nonempty
  let sourceLaw : Giry.Law presentation.source := ⟨presentation.sourceMeasure, sourceNormalized⟩
  refine ⟨{
    random := presentation.toGenerator.totalRandom fallback
    accepted := presentation.toGenerator.totalRandom_accepted fallback
    sourceLaw := Giry.map presentation.standard.embeddingReal.function
      presentation.standard.embeddingReal.measurable sourceLaw
  }, ?_⟩
  exact (presentation.toGenerator.totalRandom_map fallback presentation.sourceMeasure).trans represented

namespace Normalized

/-- Subtype of s-finite laws with total mass one. -/
def Law (space : Space.{0, u} realSource) :=
  {law : SFinite.Law space // Measure.IsProbability law.val}

/-- Quasi-Borel space structure on mass-one s-finite laws as a QBS subtype. -/
noncomputable def object (space : Space.{0, u} realSource) : Space.{0, u} realSource :=
  (SFinite.object space).subtype (fun law => Measure.IsProbability law.val)

/-- Canonical inclusion morphism from mass-one s-finite laws into all s-finite laws. -/
noncomputable def inclusion (space : Space.{0, u} realSource) :
    Hom (object space) (SFinite.object space) :=
  (SFinite.object space).subtypeVal (fun law => Measure.IsProbability law.val)

/-- Map a probability law to the mass-one s-finite law subtype. -/
noncomputable def ofProbability (law : Probability.Law space) : Law space :=
  ⟨SFinite.ofProbability law, SFinite.ofProbability_probability law⟩

/-- Quasi-Borel morphism embedding probability laws into the mass-one s-finite subtype. -/
noncomputable def ofProbabilityHom (space : Space.{0, u} realSource) :
    Hom (Probability.object space) (object space) :=
  (SFinite.ofProbabilityHom space).subtypeLift
    (fun law => Measure.IsProbability law.val) SFinite.ofProbability_probability

/-- Inverse map recovering a probability law from a mass-one s-finite law. -/
noncomputable def toProbability (law : Law space) : Probability.Law space := by
  refine ⟨⟨law.val.val, law.property⟩, ?_⟩
  rcases probability_representable law.val law.property with ⟨presentation, equal⟩
  exact ⟨presentation, Subtype.ext equal⟩

@[simp] theorem toProbability_val (law : Law space) :
    (toProbability law).val.val = law.val.val := rfl

@[simp] theorem toProbability_ofProbability (law : Probability.Law space) :
    toProbability (ofProbability law) = law := by
  apply Probability.Law.ext
  apply Subtype.ext
  rfl

@[simp] theorem ofProbability_toProbability (law : Law space) :
    ofProbability (toProbability law) = law := by
  apply Subtype.ext
  apply SFinite.Law.ext
  rfl

/-- Quasi-Borel isomorphism from mass-one s-finite laws to probability laws. -/
noncomputable def toProbabilityHom (space : Space.{0, u} realSource) :
    Hom (object space) (Probability.object space) where
  toFun := toProbability
  mapRandom := by
    intro random accepted
    let family := Standard.Family.ofPartial (Classical.choice accepted)
    let normalized := family.kernel_probability (fun seed => (random seed).property)
    let fallback := Classical.choice (normalized Foundations.Real.Construction.Dedekind.zero).nonempty
    refine ⟨{
      random := family.toGenerator.totalRandom fallback
      accepted := family.toGenerator.totalRandom_accepted fallback
      kernel := fun seed => Giry.map family.standard.embeddingReal.function
        family.standard.embeddingReal.measurable (Giry.ofKernel family.kernel normalized seed)
      measurable := MeasurableMap.comp
        (Giry.map_measurable family.standard.embeddingReal.function family.standard.embeddingReal.measurable)
        (Giry.ofKernel_measurable family.kernel normalized)
      law := ?_
    }⟩
    intro seed
    apply Subtype.ext
    exact (family.toGenerator.totalRandom_map fallback (family.kernel seed)).trans (family.law seed)

@[simp] theorem inclusion_ofProbability (space : Space.{0, u} realSource) :
    Hom.comp (inclusion space) (ofProbabilityHom space) = SFinite.ofProbabilityHom space := by
  apply Hom.ext
  intro law
  rfl

@[simp] theorem toProbabilityHom_ofProbabilityHom (space : Space.{0, u} realSource) :
    Hom.comp (toProbabilityHom space) (ofProbabilityHom space) =
      Hom.identity (Probability.object space) := by
  apply Hom.ext
  exact toProbability_ofProbability

@[simp] theorem ofProbabilityHom_toProbabilityHom (space : Space.{0, u} realSource) :
    Hom.comp (ofProbabilityHom space) (toProbabilityHom space) = Hom.identity (object space) := by
  apply Hom.ext
  exact ofProbability_toProbability

end Normalized

theorem ofProbability_range (law : Law space) :
    (∃ probability : Probability.Law space, ofProbability probability = law) ↔
      Measure.IsProbability law.val := by
  constructor
  · rintro ⟨probability, rfl⟩
    exact ofProbability_probability probability
  · intro normalized
    refine ⟨Normalized.toProbability ⟨law, normalized⟩, ?_⟩
    apply Law.ext
    rfl

/-- A family of probability laws is random iff its s-finite image is random. -/
theorem ofProbability_random_iff (laws : Carrier → Probability.Law space) :
    Random space (fun seed => ofProbability (laws seed)) ↔ Probability.Random space laws := by
  constructor
  · intro accepted
    have normalized : (Normalized.object space).Random (fun seed => Normalized.ofProbability (laws seed)) :=
      accepted
    have recovered := (Normalized.toProbabilityHom space).mapRandom normalized
    have equal : (fun seed => Normalized.toProbability (Normalized.ofProbability (laws seed))) = laws :=
      funext (fun seed => Normalized.toProbability_ofProbability (laws seed))
    change Probability.Random space (fun seed => Normalized.toProbability (Normalized.ofProbability (laws seed))) at recovered
    rw [equal] at recovered
    exact recovered
  · intro accepted
    exact (ofProbabilityHom space).mapRandom accepted

end Foundations.QuasiBorel.SFinite
