module

public import Problib.QuasiBorel.SFinite.Standard.Transport
public import Problib.QuasiBorel.SFinite.Representation

set_option autoImplicit false

/-!
# Standard-Borel presentations of s-finite measures

This module defines standard-Borel presentations pairing a standard generator
with an s-finite source measure.
It proves bidirectional measure and law preserving conversions with partial
real presentations and establishes representability equivalence.
-/

namespace Problib.QuasiBorel.SFinite.Standard

public section

open Problib.Measure hiding Space

universe u v

/-- Concrete presentation pairing a standard-Borel generator with an s-finite
source measure. -/
structure Presentation (space : Space.{0, u} realSource) extends Generator.{u, v} space where
  sourceMeasure : Measure source
  sfinite : Measure.SFinite sourceMeasure

namespace Presentation

variable {space : Space.{0, u} realSource}

/-- Interprets a standard presentation as a measure through generator pushforward. -/
@[expose] noncomputable def toMeasure (presentation : Presentation.{u, v} space) :
    Measure space.toMeasurable :=
  presentation.sourceMeasure.map presentation.random presentation.measurable

/-- Converts a standard presentation into a partial presentation from the real line. -/
@[expose] noncomputable def toPartial (presentation : Presentation.{u, v} space) :
    SFinite.Presentation space where
  toGenerator := presentation.toGenerator.toPartial
  sourceMeasure := presentation.sourceMeasure.map presentation.standard.embeddingReal.function
    presentation.standard.embeddingReal.measurable
  sfinite := presentation.sfinite.map presentation.standard.embeddingReal.function
    presentation.standard.embeddingReal.measurable

/-- Proves that standard-to-partial presentation conversion preserves the measure. -/
theorem toPartial_toMeasure (presentation : Presentation.{u, v} space) :
    presentation.toPartial.toMeasure = presentation.toMeasure :=
  presentation.toGenerator.toPartial_map presentation.sourceMeasure

/-- Interprets a standard presentation as a representable s-finite law. -/
@[expose] noncomputable def toLaw (presentation : Presentation.{u, v} space) : Law space :=
  ⟨presentation.toMeasure, presentation.toPartial, presentation.toPartial_toMeasure⟩

/-- Converts a partial presentation into a standard presentation with Type 0 source. -/
@[expose] noncomputable def ofPartial (presentation : SFinite.Presentation space) :
    Presentation.{u, 0} space where
  toGenerator := Generator.ofPartial presentation.toGenerator
  sourceMeasure := presentation.sourceMeasure.comap presentation.toGenerator.seedEmbedding
  sfinite := presentation.sfinite.comap presentation.toGenerator.seedEmbedding

/-- Proves that partial-to-standard presentation conversion preserves the measure. -/
theorem ofPartial_toMeasure (presentation : SFinite.Presentation space) :
    (ofPartial presentation).toMeasure = presentation.toMeasure :=
  presentation.toGenerator.map_comap_decode presentation.sourceMeasure

/-- Proves that partial-to-standard presentation conversion preserves the law. -/
theorem ofPartial_toLaw (presentation : SFinite.Presentation space) :
    (ofPartial presentation).toLaw = presentation.toLaw :=
  Law.ext (ofPartial_toMeasure presentation)

/-- Proves that a measure is representable by a partial presentation if and only
if it is representable by a standard presentation. -/
theorem representable_iff (measure : Measure space.toMeasurable) :
    (∃ presentation : SFinite.Presentation space, presentation.toMeasure = measure) ↔
      ∃ presentation : Presentation.{u, 0} space, presentation.toMeasure = measure := by
  constructor
  · rintro ⟨presentation, equal⟩
    exact ⟨ofPartial presentation, (ofPartial_toMeasure presentation).trans equal⟩
  · rintro ⟨presentation, equal⟩
    exact ⟨presentation.toPartial, presentation.toPartial_toMeasure.trans equal⟩

end Presentation

end

end Problib.QuasiBorel.SFinite.Standard
