module

public import Foundations.QuasiBorel.Space

set_option autoImplicit false

/-!
# Binary coproducts of quasi-Borel spaces

This module constructs binary coproducts of quasi-Borel spaces.
Accepted random elements are generated inductively from summand injections,
measurable reparameterizations, and countable partition gluing.
No inhabitant is required in either summand or the source.
-/
namespace Foundations.QuasiBorel

public section

universe u v w x y z t

variable {Ω : Type u} {source : Source Ω}

/-- Inductive predicate characterizing accepted random elements into the sum space.
Closes accepted summand random elements under reparameterization and countable gluing. -/
inductive SumRandom (left : Space.{u, v} source) (right : Space.{u, w} source) :
    (Ω → _root_.Sum left.Carrier right.Carrier) → Prop where
  | inl {random} : left.Random random →
      SumRandom left right (fun seed => _root_.Sum.inl (random seed))
  | inr {random} : right.Random random →
      SumRandom left right (fun seed => _root_.Sum.inr (random seed))
  | reparam {parameter random} : source.Measurable parameter →
      SumRandom left right random →
        SumRandom left right (fun seed => random (parameter seed))
  | piecewise {partition : Ω → Nat}
      {branches : Nat → Ω → _root_.Sum left.Carrier right.Carrier} :
      source.Partition partition → (∀ index, SumRandom left right (branches index)) →
        SumRandom left right (fun seed => branches (partition seed) seed)

namespace Space

/-- Binary coproduct of two quasi-Borel spaces over an abstract random source.
Carrier universes `v` and `w` may vary independently. -/
@[expose] def sum (left : Space.{u, v} source) (right : Space.{u, w} source) :
    Space source where
  Carrier := _root_.Sum left.Carrier right.Carrier
  Random := SumRandom left right
  constant := by
    intro point
    cases point with
    | inl point => exact SumRandom.inl (left.constant point)
    | inr point => exact SumRandom.inr (right.constant point)
  reparam := SumRandom.reparam
  piecewise := SumRandom.piecewise

/-- Canonical left injection morphism into the coproduct space. -/
@[expose] def inl (left : Space.{u, v} source) (right : Space.{u, w} source) :
    Hom left (sum left right) where
  toFun := _root_.Sum.inl
  mapRandom := SumRandom.inl

/-- Canonical right injection morphism into the coproduct space. -/
@[expose] def inr (left : Space.{u, v} source) (right : Space.{u, w} source) :
    Hom right (sum left right) where
  toFun := _root_.Sum.inr
  mapRandom := SumRandom.inr

@[simp] theorem inl_apply (left : Space.{u, v} source) (right : Space.{u, w} source)
    (value : left.Carrier) : inl left right value = _root_.Sum.inl value := rfl

@[simp] theorem inr_apply (left : Space.{u, v} source) (right : Space.{u, w} source)
    (value : right.Carrier) : inr left right value = _root_.Sum.inr value := rfl

/-- Mediating morphism `[leftMap, rightMap]` out of a coproduct space. -/
@[expose] def copair {left : Space.{u, v} source} {right : Space.{u, w} source}
    {target : Space.{u, x} source} (leftMap : Hom left target) (rightMap : Hom right target) :
    Hom (sum left right) target where
  toFun := _root_.Sum.elim leftMap rightMap
  mapRandom := by
    intro random accepted
    induction accepted with
    | inl accepted => exact leftMap.mapRandom accepted
    | inr accepted => exact rightMap.mapRandom accepted
    | reparam measurable _ induction => exact target.reparam measurable induction
    | piecewise measurable _ induction => exact target.piecewise measurable induction

@[simp] theorem copair_inl {left : Space.{u, v} source} {right : Space.{u, w} source}
    {target : Space.{u, x} source} (leftMap : Hom left target) (rightMap : Hom right target) :
    Hom.comp (copair leftMap rightMap) (inl left right) = leftMap := by
  apply Hom.ext
  intro point
  rfl

@[simp] theorem copair_inr {left : Space.{u, v} source} {right : Space.{u, w} source}
    {target : Space.{u, x} source} (leftMap : Hom left target) (rightMap : Hom right target) :
    Hom.comp (copair leftMap rightMap) (inr left right) = rightMap := by
  apply Hom.ext
  intro point
  rfl

/-- Proves uniqueness of the mediating copair morphism. -/
theorem copair_unique {left : Space.{u, v} source} {right : Space.{u, w} source}
    {target : Space.{u, x} source} (morphism : Hom (sum left right) target) :
    copair (Hom.comp morphism (inl left right)) (Hom.comp morphism (inr left right)) =
      morphism := by
  apply Hom.ext
  intro point
  cases point <;> rfl

/-- Extensionality principle for morphisms from a coproduct space.
Two morphisms are equal when they agree on both summand injections. -/
theorem sum_hom_ext {left : Space.{u, v} source} {right : Space.{u, w} source}
    {target : Space.{u, x} source} {first second : Hom (sum left right) target}
    (leftEqual : Hom.comp first (inl left right) = Hom.comp second (inl left right))
    (rightEqual : Hom.comp first (inr left right) = Hom.comp second (inr left right)) :
    first = second := by
  rw [← copair_unique first, leftEqual, rightEqual, copair_unique]

/-- Functorial coproduct action mapping a pair of morphisms across summands. -/
@[expose] def sumMap {first : Space.{u, v} source} {second : Space.{u, w} source}
    {third : Space.{u, x} source} {fourth : Space.{u, y} source}
    (leftMap : Hom first third) (rightMap : Hom second fourth) :
    Hom (sum first second) (sum third fourth) :=
  copair (Hom.comp (inl third fourth) leftMap) (Hom.comp (inr third fourth) rightMap)

@[simp] theorem sumMap_inl {first : Space.{u, v} source} {second : Space.{u, w} source}
    {third : Space.{u, x} source} {fourth : Space.{u, y} source}
    (leftMap : Hom first third) (rightMap : Hom second fourth) (value : first.Carrier) :
    sumMap leftMap rightMap (_root_.Sum.inl value) = _root_.Sum.inl (leftMap value) := rfl

@[simp] theorem sumMap_inr {first : Space.{u, v} source} {second : Space.{u, w} source}
    {third : Space.{u, x} source} {fourth : Space.{u, y} source}
    (leftMap : Hom first third) (rightMap : Hom second fourth) (value : second.Carrier) :
    sumMap leftMap rightMap (_root_.Sum.inr value) = _root_.Sum.inr (rightMap value) := rfl

/-- Proves that the sum map of identity morphisms is the identity morphism. -/
theorem sumMap_identity (left : Space.{u, v} source) (right : Space.{u, w} source) :
    sumMap (Hom.identity left) (Hom.identity right) = Hom.identity (sum left right) := by
  apply Hom.ext
  intro point
  cases point <;> rfl

/-- Proves functorial composition for sum maps. -/
theorem sumMap_comp {first : Space.{u, v} source} {second : Space.{u, w} source}
    {third : Space.{u, x} source} {fourth : Space.{u, y} source}
    {fifth : Space.{u, z} source} {sixth : Space.{u, t} source}
    (afterLeft : Hom third fifth) (afterRight : Hom fourth sixth)
    (beforeLeft : Hom first third) (beforeRight : Hom second fourth) :
    sumMap (Hom.comp afterLeft beforeLeft) (Hom.comp afterRight beforeRight) =
      Hom.comp (sumMap afterLeft afterRight) (sumMap beforeLeft beforeRight) := by
  apply Hom.ext
  intro point
  cases point <;> rfl

end Space

end

end Foundations.QuasiBorel
