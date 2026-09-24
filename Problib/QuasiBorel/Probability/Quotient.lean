import Problib.QuasiBorel.Probability.Random

set_option autoImplicit false

namespace Problib.QuasiBorel.Probability

open Problib.Measure hiding Space
open Problib.Measure.Real (Carrier borel)

/-- Acceptance predicate for random elements into the presentation quotient space, matching Heunen et al.'s shared-random-element family definition. -/
def QuotientLaw.Random (space : Space (Source.ofMeasurable borel)) (laws : Carrier → QuotientLaw space) : Prop :=
  ∃ (random : Carrier → space.Carrier) (accepted : space.Random random)
    (kernel : Carrier → Giry.Law borel), MeasurableMap borel (Giry.space borel) kernel ∧
    ∀ seed, Quotient.mk (Presentation.setoid space) ⟨random, accepted, kernel seed⟩ = laws seed

/-- A family into the presentation quotient is an accepted random element if and only if its image under the canonical law bijection is accepted. -/
theorem QuotientLaw.random_iff {space : Space (Source.ofMeasurable borel)}
    (laws : Carrier → QuotientLaw space) :
    QuotientLaw.Random space laws ↔ Probability.Random space (fun seed => (laws seed).toLaw) := by
  constructor
  · rintro ⟨random, accepted, kernel, measurable, equal⟩
    refine ⟨⟨random, accepted, kernel, @measurable, ?_⟩⟩
    intro seed
    exact congrArg (fun law => (QuotientLaw.toLaw law).val) (equal seed)
  · rintro ⟨family⟩
    refine ⟨family.random, family.accepted, family.kernel, family.measurable, ?_⟩
    intro seed
    apply QuotientLaw.toLaw_injective
    exact Law.ext (family.law seed)

/-- The quasi-Borel space structure on presentation quotient laws. -/
noncomputable def QuotientLaw.object (space : Space (Source.ofMeasurable borel)) :
    Space (Source.ofMeasurable borel) where
  Carrier := QuotientLaw space
  Random := QuotientLaw.Random space
  constant := fun law => (random_iff _).mpr ((Probability.object space).constant law.toLaw)
  reparam := by
    intro parameter random measurable accepted
    exact (random_iff _).mpr ((Probability.object space).reparam measurable ((random_iff _).mp accepted))
  piecewise := by
    intro partition branches measurable accepted
    exact (random_iff _).mpr ((Probability.object space).piecewise measurable
      (fun index => (random_iff _).mp (accepted index)))

/-- Canonical quasi-Borel morphism from the presentation quotient space to the representable probability space. -/
noncomputable def QuotientLaw.toLawHom (space : Space (Source.ofMeasurable borel)) :
    Hom (QuotientLaw.object space) (Probability.object space) where
  toFun := QuotientLaw.toLaw
  map_random := fun accepted => (random_iff _).mp accepted

/-- Canonical quasi-Borel morphism from the representable probability space to the presentation quotient space. -/
noncomputable def Law.toQuotientHom (space : Space (Source.ofMeasurable borel)) :
    Hom (Probability.object space) (QuotientLaw.object space) where
  toFun := Law.toQuotient
  map_random := by
    intro random accepted
    change Probability.Random space random at accepted
    apply (QuotientLaw.random_iff _).mpr
    simpa only [Law.toQuotient_toLaw] using accepted

/-- The composite of the quotient-to-law and law-to-quotient morphisms is the identity on the representable probability space. -/
theorem QuotientLaw.toLawHom_toQuotientHom (space : Space (Source.ofMeasurable borel)) :
    Hom.comp (QuotientLaw.toLawHom space) (Law.toQuotientHom space) =
      Hom.identity (Probability.object space) := by
  apply Hom.ext
  exact Law.toQuotient_toLaw

/-- The composite of the law-to-quotient and quotient-to-law morphisms is the identity on the presentation quotient space. -/
theorem QuotientLaw.toQuotientHom_toLawHom (space : Space (Source.ofMeasurable borel)) :
    Hom.comp (Law.toQuotientHom space) (QuotientLaw.toLawHom space) =
      Hom.identity (QuotientLaw.object space) := by
  apply Hom.ext
  exact QuotientLaw.toLaw_toQuotient

end Problib.QuasiBorel.Probability
