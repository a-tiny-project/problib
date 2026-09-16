module

public import Foundations.QuasiBorel.SFinite.Random

set_option autoImplicit false

/-!
# Quasi-Borel structure on presentation quotients

This module equips the presentation quotient with a quasi-Borel space structure.
It proves that the presentation quotient is isomorphic to the represented law
space as a quasi-Borel object through mutually inverse morphisms.
-/
namespace Foundations.QuasiBorel.SFinite

public section

open Foundations.Measure hiding Space
open Foundations.Measure.Real (Carrier borel)

/-- Random elements into the presentation quotient witnessed by a generator and an s-finite kernel. -/
@[expose] def QuotientLaw.Random (space : Space realSource)
    (laws : Carrier → QuotientLaw space) : Prop :=
  ∃ (random : Carrier → (withFailure space).Carrier)
    (accepted : (withFailure space).Random random)
    (kernel : Kernel borel borel) (sfinite : Kernel.IsSFinite kernel),
    ∀ seed, Quotient.mk (Presentation.setoid space)
      ⟨⟨random, accepted⟩, kernel seed, sfinite.measure seed⟩ = laws seed

/-- Proves that random elements into quotient classes match random elements into represented laws. -/
theorem QuotientLaw.random_iff {space : Space realSource}
    (laws : Carrier → QuotientLaw space) :
    QuotientLaw.Random space laws ↔ SFinite.Random space (fun seed => (laws seed).toLaw) := by
  constructor
  · rintro ⟨random, accepted, kernel, sfinite, equal⟩
    refine ⟨⟨⟨random, accepted⟩, kernel, sfinite, ?_⟩⟩
    intro seed
    exact congrArg (fun law => (QuotientLaw.toLaw law).val) (equal seed)
  · rintro ⟨family⟩
    refine ⟨family.random, family.accepted, family.kernel, family.sfinite, ?_⟩
    intro seed
    apply QuotientLaw.toLaw_injective
    exact Law.ext (family.law seed)

/-- Equips the presentation quotient with its canonical quasi-Borel space structure. -/
@[expose] noncomputable def QuotientLaw.object (space : Space realSource) : Space realSource where
  Carrier := QuotientLaw space
  Random := QuotientLaw.Random space
  constant := fun law => (random_iff _).mpr ((SFinite.object space).constant law.toLaw)
  reparam := by
    intro parameter random measurable accepted
    exact (random_iff _).mpr
      ((SFinite.object space).reparam measurable ((random_iff _).mp accepted))
  piecewise := by
    intro partition branches measurable accepted
    exact (random_iff _).mpr ((SFinite.object space).piecewise measurable
      (fun index => (random_iff _).mp (accepted index)))

/-- Canonical quasi-Borel morphism from the quotient space to the represented-law space. -/
@[expose] noncomputable def QuotientLaw.toLawHom (space : Space realSource) :
    Hom (QuotientLaw.object space) (SFinite.object space) where
  toFun := QuotientLaw.toLaw
  mapRandom := fun accepted => (random_iff _).mp accepted

/-- Canonical quasi-Borel morphism from the represented-law space to the quotient space. -/
@[expose] noncomputable def Law.toQuotientHom (space : Space realSource) :
    Hom (SFinite.object space) (QuotientLaw.object space) where
  toFun := Law.toQuotient
  mapRandom := by
    intro random accepted
    change SFinite.Random space random at accepted
    apply (QuotientLaw.random_iff _).mpr
    simpa only [Law.toQuotient_toLaw] using accepted

/-- Proves that composing the quotient-to-law and law-to-quotient morphisms yields the identity on laws. -/
theorem QuotientLaw.toLawHom_toQuotientHom (space : Space realSource) :
    Hom.comp (QuotientLaw.toLawHom space) (Law.toQuotientHom space) =
      Hom.identity (SFinite.object space) := by
  apply Hom.ext
  exact Law.toQuotient_toLaw

/-- Proves that composing the law-to-quotient and quotient-to-law morphisms yields the identity on quotients. -/
theorem QuotientLaw.toQuotientHom_toLawHom (space : Space realSource) :
    Hom.comp (Law.toQuotientHom space) (QuotientLaw.toLawHom space) =
      Hom.identity (QuotientLaw.object space) := by
  apply Hom.ext
  exact QuotientLaw.toLaw_toQuotient

end

end Foundations.QuasiBorel.SFinite
