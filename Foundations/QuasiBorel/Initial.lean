module

public import Foundations.QuasiBorel.Space

set_option autoImplicit false

/-!
# Initial quasi-Borel space

This module defines the initial quasi-Borel space on the empty carrier `PEmpty`.
Source and carrier universes remain independent.
No random elements are accepted into this space.
-/
namespace Foundations.QuasiBorel.Space

public section

universe u v w

variable {Ω : Type u} {source : Source Ω}

/-- Initial quasi-Borel space on `PEmpty.{v + 1}`.
Accepts no random elements from the source.
Source universe `u` and carrier universe `v` are independent. -/
@[expose] def initial (source : Source Ω) : Space.{u, v} source where
  Carrier := PEmpty.{v + 1}
  Random := fun _ => False
  constant := fun point => point.elim
  reparam := fun _ accepted => accepted.elim
  piecewise := fun _ branches => (branches 0).elim

/-- Canonical quasi-Borel morphism from the initial space into any space. -/
@[expose] def initiate (space : Space.{u, w} source) :
    Hom (initial.{u, v} source) space where
  toFun := fun point => point.elim
  mapRandom := fun accepted => accepted.elim

/-- Uniqueness of the mediating morphism from the initial space. -/
theorem initiate_unique (space : Space.{u, w} source)
    (morphism : Hom (initial.{u, v} source) space) : morphism = initiate space := by
  apply Hom.ext
  intro point
  exact point.elim

/-- Proves that no random element into the initial space is accepted. -/
theorem initial_no_random (random : Ω → (initial.{u, v} source).Carrier) :
    ¬(initial source).Random random := fun accepted => accepted

end

end Foundations.QuasiBorel.Space
