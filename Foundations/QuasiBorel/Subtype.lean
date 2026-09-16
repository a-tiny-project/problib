module

public import Foundations.QuasiBorel.Space

/-!
# Quasi-Borel subtypes and universal property

This module formalizes the generic quasi-Borel subspace (subtype) construction
for an arbitrary predicate on the carrier, equipping it with the induced random
elements, the canonical subspace inclusion morphism, and the universal property
lifting morphisms with image in the subtype.
-/

set_option autoImplicit false

namespace Foundations.QuasiBorel

public section

universe u v w

variable {Ω : Type u} {source : Source Ω}

/-- Quasi-Borel space structure on a subtype carrier equipped with the induced random elements. -/
@[expose] def Space.subtype (space : Space.{u, v} source)
    (predicate : space.Carrier → Prop) : Space.{u, v} source where
  Carrier := {point : space.Carrier // predicate point}
  Random := fun random => space.Random (fun seed => (random seed).val)
  constant := fun point => space.constant point.val
  reparam := fun measurable accepted => space.reparam measurable accepted
  piecewise := fun measurable accepted => space.piecewise measurable accepted

theorem Space.subtype_random_iff (space : Space.{u, v} source)
    (predicate : space.Carrier → Prop) (random : Ω → (space.subtype predicate).Carrier) :
    (space.subtype predicate).Random random ↔ space.Random (fun seed => (random seed).val) :=
  Iff.rfl

/-- Canonical inclusion morphism from a quasi-Borel subtype into the ambient space. -/
@[expose] def Space.subtypeVal (space : Space.{u, v} source)
    (predicate : space.Carrier → Prop) : Hom (space.subtype predicate) space where
  toFun := Subtype.val
  mapRandom := fun accepted => accepted

@[simp] theorem Space.subtypeVal_apply (space : Space.{u, v} source)
    (predicate : space.Carrier → Prop) (point : (space.subtype predicate).Carrier) :
    space.subtypeVal predicate point = point.val := rfl

theorem Space.subtypeVal_injective (space : Space.{u, v} source)
    (predicate : space.Carrier → Prop) : Function.Injective (space.subtypeVal predicate) :=
  fun _ _ equal => Subtype.ext equal

variable {domain : Space.{u, v} source} {codomain : Space.{u, w} source}

/-- Universal lift of a quasi-Borel morphism whose image factors through the subtype predicate. -/
@[expose] def Hom.subtypeLift (function : Hom domain codomain)
    (predicate : codomain.Carrier → Prop) (accepted : ∀ point, predicate (function point)) :
    Hom domain (codomain.subtype predicate) where
  toFun := fun point => ⟨function point, accepted point⟩
  mapRandom := function.mapRandom

@[simp] theorem Hom.subtypeLift_apply (function : Hom domain codomain)
    (predicate : codomain.Carrier → Prop) (accepted : ∀ point, predicate (function point))
    (point : domain.Carrier) : (function.subtypeLift predicate accepted point).val = function point :=
  rfl

@[simp] theorem Hom.subtypeVal_subtypeLift (function : Hom domain codomain)
    (predicate : codomain.Carrier → Prop) (accepted : ∀ point, predicate (function point)) :
    Hom.comp (codomain.subtypeVal predicate) (function.subtypeLift predicate accepted) = function := by
  apply Hom.ext
  intro point
  rfl

theorem Hom.subtypeLift_unique (predicate : codomain.Carrier → Prop)
    (function : Hom domain codomain) (accepted : ∀ point, predicate (function point))
    (lifted : Hom domain (codomain.subtype predicate))
    (equal : Hom.comp (codomain.subtypeVal predicate) lifted = function) :
    lifted = function.subtypeLift predicate accepted := by
  apply Hom.ext
  intro point
  apply Subtype.ext
  exact congrArg (fun morphism : Hom domain codomain => morphism point) equal

end

end Foundations.QuasiBorel
