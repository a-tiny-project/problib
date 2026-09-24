module

public import Problib.QuasiBorel.SFinite.Presentation

set_option autoImplicit false

/-!
# Representable s-finite laws and presentation quotients

This module defines the subtype of representable s-finite measures and the
presentation quotient on quasi-Borel spaces.
It establishes two-sided inverse bijections between represented laws and
presentation quotient equivalence classes.
-/
namespace Problib.QuasiBorel.SFinite

public section

open Problib.Measure hiding Space
open Problib.Measure.Real (Carrier borel)

universe u v

/-- Subtype of measures on a quasi-Borel space admitting a presentation. -/
@[expose] def Law (space : Space realSource) :=
  { measure : Measure space.toMeasurable //
    ∃ presentation : Presentation space, presentation.toMeasure = measure }

/-- Maps a presentation into its represented s-finite law. -/
@[expose] noncomputable def Presentation.toLaw {space : Space realSource}
    (presentation : Presentation space) : Law space :=
  ⟨presentation.toMeasure, presentation, rfl⟩

namespace Law

variable {space : Space realSource}

/-- Extensionality for represented laws by equality of underlying measures. -/
@[ext] theorem ext {left right : Law space} (equal : left.val = right.val) : left = right :=
  Subtype.ext equal

/-- Chooses a representing presentation for any represented law. -/
@[expose] noncomputable def presentation (law : Law space) : Presentation space :=
  Classical.choose law.property

/-- Proves that the chosen presentation interprets as the law's underlying measure. -/
theorem presentation_toMeasure (law : Law space) : law.presentation.toMeasure = law.val :=
  Classical.choose_spec law.property

/-- Proves that mapping the chosen presentation back to a law recovers the original law. -/
theorem presentation_toLaw (law : Law space) : law.presentation.toLaw = law :=
  ext (presentation_toMeasure law)

/-- Derives an s-finite certificate for the underlying measure of any represented law. -/
@[expose] noncomputable def sfinite (law : Law space) : Measure.SFinite law.val :=
  law.presentation_toMeasure ▸ law.presentation.toMeasure_sfinite

end Law

/-- The zero measure as a represented law on any quasi-Borel space. -/
@[expose] noncomputable def zero (space : Space realSource) : Law space :=
  ⟨Measure.zero space.toMeasurable,
    Presentation.failed space (Measure.zero borel) (Measure.SFinite.zero borel),
    Presentation.failed_toMeasure space _ _⟩

/-- Proves that the zero law evaluates to the zero measure. -/
@[simp] theorem zero_val (space : Space realSource) :
    (zero space).val = Measure.zero space.toMeasurable := rfl

/-- Proves that the space of represented laws is always nonempty. -/
theorem law_nonempty (space : Space realSource) : Nonempty (Law space) :=
  ⟨zero space⟩

/-- Equivalence relation identifying presentations with equal interpreted measures. -/
@[expose] def Presentation.setoid (space : Space realSource) : Setoid (Presentation space) where
  r := fun left right => left.toMeasure = right.toMeasure
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

/-- Presentation quotient identifying presentations that induce the same measure. -/
@[expose] def QuotientLaw (space : Space realSource) :=
  Quotient (Presentation.setoid space)

/-- Well-defined map from presentation quotient classes to represented laws. -/
@[expose] noncomputable def QuotientLaw.toLaw {space : Space realSource} :
    QuotientLaw space → Law space :=
  Quotient.lift Presentation.toLaw (fun _ _ equal => Law.ext equal)

/-- Maps a represented law into its presentation quotient class. -/
@[expose] noncomputable def Law.toQuotient {space : Space realSource}
    (law : Law space) : QuotientLaw space :=
  Quotient.mk _ law.presentation

/-- Proves that mapping a law to the quotient and back recovers the original law. -/
theorem Law.toQuotient_toLaw {space : Space realSource} (law : Law space) :
    law.toQuotient.toLaw = law :=
  law.presentation_toLaw

/-- Proves that mapping a quotient class to a law and back recovers the quotient class. -/
theorem QuotientLaw.toLaw_toQuotient {space : Space realSource} (law : QuotientLaw space) :
    law.toLaw.toQuotient = law := by
  refine Quotient.inductionOn law ?_
  intro presentation
  apply Quotient.sound
  exact Law.presentation_toMeasure presentation.toLaw

/-- Proves injectivity of the canonical map from quotient classes to laws. -/
theorem QuotientLaw.toLaw_injective {space : Space realSource} :
    Function.Injective (@QuotientLaw.toLaw space) := by
  intro left right equal
  calc
    left = left.toLaw.toQuotient := (toLaw_toQuotient left).symm
    _ = right.toLaw.toQuotient := congrArg Law.toQuotient equal
    _ = right := toLaw_toQuotient right

/-- Proves surjectivity of the canonical map from quotient classes to laws. -/
theorem QuotientLaw.toLaw_surjective {space : Space realSource} :
    Function.Surjective (@QuotientLaw.toLaw space) := by
  intro law
  exact ⟨law.toQuotient, law.toQuotient_toLaw⟩

/-- Proves that two presentations yield equal quotient classes iff their measures coincide. -/
theorem Presentation.quotient_eq_iff {space : Space realSource}
    (left right : Presentation space) :
    Quotient.mk (Presentation.setoid space) left = Quotient.mk _ right ↔
      left.toMeasure = right.toMeasure := by
  constructor
  · exact Quotient.exact
  · intro equal
    apply Quotient.sound
    exact equal

end

end Problib.QuasiBorel.SFinite
