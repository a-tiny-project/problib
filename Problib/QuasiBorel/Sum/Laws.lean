module

public import Problib.QuasiBorel.Initial
public import Problib.QuasiBorel.Sum

set_option autoImplicit false

/-!
# Category-theoretic coproduct laws for quasi-Borel spaces

This module proves symmetric, associative, and initial unit isomorphisms
for quasi-Borel coproducts.
It verifies two-sided inverse identities and involution as extensional equalities between morphisms.
-/
namespace Problib.QuasiBorel.Space

public section

universe u v w x

variable {Ω : Type u} {source : Source Ω}

/-- Symmetry isomorphism swapping the summands of a coproduct space. -/
@[expose] def sumSwap (left : Space.{u, v} source) (right : Space.{u, w} source) :
    Hom (sum left right) (sum right left) :=
  copair (inr right left) (inl right left)

/-- Proves that swapping summands is an involution. -/
theorem sumSwap_involutive (left : Space.{u, v} source) (right : Space.{u, w} source) :
    Hom.comp (sumSwap right left) (sumSwap left right) = Hom.identity (sum left right) := by
  apply Hom.ext
  intro point
  cases point <;> rfl

/-- Associator isomorphism from `(A + B) + C` to `A + (B + C)`. -/
@[expose] def sumAssociate (first : Space.{u, v} source) (second : Space.{u, w} source)
    (third : Space.{u, x} source) :
    Hom (sum (sum first second) third) (sum first (sum second third)) :=
  copair
    (copair (inl first (sum second third))
      (Hom.comp (inr first (sum second third)) (inl second third)))
    (Hom.comp (inr first (sum second third)) (inr second third))

/-- Inverse associator isomorphism from `A + (B + C)` to `(A + B) + C`. -/
@[expose] def sumUnassociate (first : Space.{u, v} source) (second : Space.{u, w} source)
    (third : Space.{u, x} source) :
    Hom (sum first (sum second third)) (sum (sum first second) third) :=
  copair (Hom.comp (inl (sum first second) third) (inl first second))
    (copair (Hom.comp (inl (sum first second) third) (inr first second))
      (inr (sum first second) third))

/-- Proves that `sumAssociate` is a left inverse to `sumUnassociate`. -/
theorem sumAssociate_sumUnassociate (first : Space.{u, v} source)
    (second : Space.{u, w} source) (third : Space.{u, x} source) :
    Hom.comp (sumAssociate first second third) (sumUnassociate first second third) =
      Hom.identity (sum first (sum second third)) := by
  apply Hom.ext
  intro point
  cases point with
  | inl value => rfl
  | inr value => cases value <;> rfl

/-- Proves that `sumUnassociate` is a left inverse to `sumAssociate`. -/
theorem sumUnassociate_sumAssociate (first : Space.{u, v} source)
    (second : Space.{u, w} source) (third : Space.{u, x} source) :
    Hom.comp (sumUnassociate first second third) (sumAssociate first second third) =
      Hom.identity (sum (sum first second) third) := by
  apply Hom.ext
  intro point
  cases point with
  | inl value => cases value <;> rfl
  | inr value => rfl

/-- Left unitor isomorphism eliminating an initial summand on the left. -/
@[expose] def sumInitialLeft (space : Space.{u, w} source) :
    Hom (sum (initial.{u, v} source) space) space :=
  copair (initiate space) (Hom.identity space)

/-- Right unitor isomorphism eliminating an initial summand on the right. -/
@[expose] def sumInitialRight (space : Space.{u, w} source) :
    Hom (sum space (initial.{u, v} source)) space :=
  copair (Hom.identity space) (initiate space)

/-- Computation law proving `sumInitialLeft` is a left inverse to `inr`. -/
theorem sumInitialLeft_inr (space : Space.{u, w} source) :
    Hom.comp (sumInitialLeft space) (inr (initial.{u, v} source) space) =
      Hom.identity space := copair_inr _ _

/-- Proves `sumInitialLeft` is a right inverse to `inr`. -/
theorem inr_sumInitialLeft (space : Space.{u, w} source) :
    Hom.comp (inr (initial.{u, v} source) space) (sumInitialLeft space) =
      Hom.identity (sum (initial source) space) := by
  apply Hom.ext
  intro point
  cases point with
  | inl value => exact value.elim
  | inr value => rfl

/-- Computation law proving `sumInitialRight` is a left inverse to `inl`. -/
theorem sumInitialRight_inl (space : Space.{u, w} source) :
    Hom.comp (sumInitialRight space) (inl space (initial.{u, v} source)) =
      Hom.identity space := copair_inl _ _

/-- Proves `sumInitialRight` is a right inverse to `inl`. -/
theorem inl_sumInitialRight (space : Space.{u, w} source) :
    Hom.comp (inl space (initial.{u, v} source)) (sumInitialRight space) =
      Hom.identity (sum space (initial source)) := by
  apply Hom.ext
  intro point
  cases point with
  | inl value => rfl
  | inr value => exact value.elim

end

end Problib.QuasiBorel.Space
