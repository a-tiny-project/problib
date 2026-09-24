module

public import Problib.QuasiBorel.SFinite.Generator
public import Problib.Measure.Additive.Comap.Finite

set_option autoImplicit false

/-!
# Concrete presentations of s-finite measures on quasi-Borel spaces

This module pairs an accepted partial generator with an explicit s-finite real
source measure.
Pushforward along the generator followed by pullback along the right summand
injection interprets the presentation as an s-finite measure on the induced
measurable space.
-/
namespace Problib.QuasiBorel.SFinite

public section

open Problib.Measure hiding Space
open Problib.Measure.Real (Carrier borel)
open Problib.Real (ENNReal)

universe u v

/-- Pairs a partial random generator with an s-finite real source measure. -/
structure Presentation (space : Space realSource) extends Generator space where
  /-- S-finite source measure on the real Borel line. -/
  sourceMeasure : Measure borel
  /-- Certificate that the source measure is s-finite. -/
  sfinite : Measure.SFinite sourceMeasure

namespace Presentation

variable {space : Space realSource}

/-- Interprets a presentation by pushing forward the source measure and pulling back along the result injection. -/
@[expose] noncomputable def toMeasure (presentation : Presentation space) : Measure space.toMeasurable :=
  (presentation.sourceMeasure.map presentation.random
    (Space.random_measurable presentation.accepted)).comap
      (Space.inrEmbedding (Space.terminal realSource) space)

/-- Proves that the interpreted measure of any presentation is s-finite. -/
@[expose] noncomputable def toMeasure_sfinite (presentation : Presentation space) :
    Measure.SFinite presentation.toMeasure :=
  (presentation.sfinite.map presentation.random
    (Space.random_measurable presentation.accepted)).comap
      (Space.inrEmbedding (Space.terminal realSource) space)

/-- Constructs a presentation from a total accepted random element and an s-finite measure. -/
@[expose] noncomputable def total (random : Carrier → space.Carrier) (accepted : space.Random random)
    (measure : Measure borel) (sfinite : Measure.SFinite measure) : Presentation space where
  random := fun seed => Sum.inr (random seed)
  accepted := SumRandom.inr accepted
  sourceMeasure := measure
  sfinite := sfinite

/-- Proves that a total presentation interprets as the standard pushforward measure. -/
theorem total_toMeasure (random : Carrier → space.Carrier) (accepted : space.Random random)
    (measure : Measure borel) (sfinite : Measure.SFinite measure) :
    (total random accepted measure sfinite).toMeasure =
      measure.map random (Space.random_measurable accepted) := by
  change (measure.map (fun seed => Sum.inr (random seed)) _).comap
    (Space.inrEmbedding (Space.terminal realSource) space) = _
  rw [← Measure.map_comp measure random Sum.inr (Space.random_measurable accepted)
    (Space.inr (Space.terminal realSource) space).toMeasurable]
  exact Measure.comap_map _ (Space.inrEmbedding (Space.terminal realSource) space)

/-- Constructs a presentation sending all source mass to the failure point. -/
@[expose] noncomputable def failed (space : Space realSource)
    (measure : Measure borel) (sfinite : Measure.SFinite measure) : Presentation space where
  random := fun _ => Sum.inl ()
  accepted := (withFailure space).constant (Sum.inl ())
  sourceMeasure := measure
  sfinite := sfinite

/-- Proves that a failed presentation interprets as the zero measure. -/
theorem failed_toMeasure (space : Space realSource)
    (measure : Measure borel) (sfinite : Measure.SFinite measure) :
    (failed space measure sfinite).toMeasure = Measure.zero space.toMeasurable := by
  apply Measure.ext
  intro region measurable
  let presentation := failed space measure sfinite
  let embedding := Space.inrEmbedding (Space.terminal realSource) space
  have empty : Set.preimage presentation.random
      (Set.image embedding.function region) = Set.empty := by
    apply Set.ext
    intro seed
    change (∃ point, region point ∧ Sum.inr point = Sum.inl ()) ↔ False
    constructor
    · rintro ⟨point, member, equal⟩
      cases equal
    · intro impossible
      exact impossible.elim
  calc
    presentation.toMeasure region =
        (presentation.sourceMeasure.map presentation.random
          (Space.random_measurable presentation.accepted))
            (Set.image embedding.function region) :=
      Measure.comap_apply _ embedding @measurable
    _ = presentation.sourceMeasure
        (Set.preimage presentation.random (Set.image embedding.function region)) :=
      Measure.map_apply presentation.sourceMeasure presentation.random
        (Space.random_measurable presentation.accepted)
        (embedding.image_measurable region @measurable)
    _ = ENNReal.zero := by rw [empty, Measure.empty_apply]
    _ = Measure.zero space.toMeasurable region := (Measure.zero_apply region).symm

end Presentation

end

end Problib.QuasiBorel.SFinite
