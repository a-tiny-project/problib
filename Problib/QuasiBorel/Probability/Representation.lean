import Problib.Measure.Giry.Monad
import Problib.Measure.Real.Borel
import Problib.QuasiBorel.Measurable.Induced

set_option autoImplicit false

namespace Problib.QuasiBorel.Probability

open Problib.Measure hiding Space
open Problib.Measure.Real (Carrier borel)

universe u v

/-- Raw probability presentation on a quasi-Borel space, pairing an accepted random element with a probability law on the real Borel source. -/
structure Presentation (space : Space (Source.ofMeasurable borel)) where
  random : Carrier → space.Carrier
  accepted : space.Random random
  sourceLaw : Giry.Law borel

/-- Pushes forward the real source law along the accepted random element to obtain a Giry law on the induced measurable space. -/
noncomputable def Presentation.toGiry {space : Space (Source.ofMeasurable borel)}
    (presentation : Presentation space) : Giry.Law space.toMeasurable :=
  Giry.map presentation.random (Space.random_measurable presentation.accepted)
    presentation.sourceLaw

/-- Subtype of Giry probability laws on the induced measurable space that admit a quasi-Borel presentation. -/
def Law (space : Space (Source.ofMeasurable borel)) :=
  { law : Giry.Law space.toMeasurable //
    ∃ presentation : Presentation space, presentation.toGiry = law }

/-- Packages a raw presentation as a representable quasi-Borel probability law. -/
noncomputable def Presentation.toLaw {space : Space (Source.ofMeasurable borel)}
    (presentation : Presentation space) : Law space :=
  ⟨presentation.toGiry, presentation, rfl⟩

namespace Law

variable {space : Space (Source.ofMeasurable borel)}

/-- Extensionality for probability laws on a quasi-Borel space via equality of underlying Giry measures. -/
theorem ext {left right : Law space} (equal : left.val = right.val) : left = right :=
  Subtype.ext equal

/-- Nonconstructively chooses a presentation realizing the representable law. -/
noncomputable def presentation (law : Law space) : Presentation space :=
  Classical.choose law.property

/-- The chosen presentation pushes forward to the representable law value. -/
theorem presentation_toGiry (law : Law space) : law.presentation.toGiry = law.val :=
  Classical.choose_spec law.property

/-- Packaging the chosen presentation recovers the original representable law. -/
theorem presentation_toLaw (law : Law space) : law.presentation.toLaw = law :=
  ext (presentation_toGiry law)

end Law

/-- Equivalence relation identifying presentations that induce the same Giry probability law. -/
def Presentation.setoid (space : Space (Source.ofMeasurable borel)) :
    Setoid (Presentation space) where
  r := fun left right => left.toGiry = right.toGiry
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

/-- Quotient of raw probability presentations by equal pushforward measure. -/
def QuotientLaw (space : Space (Source.ofMeasurable borel)) :=
  Quotient (Presentation.setoid space)

/-- Canonical bijection mapping an equivalence class of presentations to its representable law. -/
noncomputable def QuotientLaw.toLaw {space : Space (Source.ofMeasurable borel)} :
    QuotientLaw space → Law space :=
  Quotient.lift Presentation.toLaw (fun _ _ equal => Law.ext equal)

/-- Maps a representable law to its presentation equivalence class in the quotient. -/
noncomputable def Law.toQuotient {space : Space (Source.ofMeasurable borel)}
    (law : Law space) : QuotientLaw space :=
  Quotient.mk _ law.presentation

/-- Round-trip from representable law to quotient and back is the identity. -/
theorem Law.toQuotient_toLaw {space : Space (Source.ofMeasurable borel)}
    (law : Law space) : law.toQuotient.toLaw = law :=
  law.presentation_toLaw

/-- Round-trip from presentation quotient to representable law and back is the identity. -/
theorem QuotientLaw.toLaw_toQuotient {space : Space (Source.ofMeasurable borel)}
    (law : QuotientLaw space) : law.toLaw.toQuotient = law := by
  refine Quotient.inductionOn law ?_
  intro presentation
  apply Quotient.sound
  exact Law.presentation_toGiry presentation.toLaw

/-- The canonical mapping from presentation quotient to representable laws is injective. -/
theorem QuotientLaw.toLaw_injective {space : Space (Source.ofMeasurable borel)} :
    Function.Injective (@QuotientLaw.toLaw space) := by
  intro left right equal
  calc
    left = left.toLaw.toQuotient := (toLaw_toQuotient left).symm
    _ = right.toLaw.toQuotient := congrArg Law.toQuotient equal
    _ = right := toLaw_toQuotient right

/-- The canonical mapping from presentation quotient to representable laws is surjective. -/
theorem QuotientLaw.toLaw_surjective {space : Space (Source.ofMeasurable borel)} :
    Function.Surjective (@QuotientLaw.toLaw space) := by
  intro law
  exact ⟨law.toQuotient, law.toQuotient_toLaw⟩

end Problib.QuasiBorel.Probability
