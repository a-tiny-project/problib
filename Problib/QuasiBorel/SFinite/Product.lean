module

public import Problib.QuasiBorel.SFinite.Commutative

set_option autoImplicit false

/-!
# Joint commutative products for s-finite quasi-Borel spaces

This module constructs the joint independent product morphism for s-finite
quasi-Borel spaces from higher-order monadic bind and strength.
It proves unit, zero, naturality, swapping, associativity, strength coherence,
and left, right, and pairwise bind compatibility.
-/

namespace Problib.QuasiBorel.SFinite

public section

open Problib.Measure hiding Space

universe u v w x y

/-- Joint independent product morphism for s-finite quasi-Borel laws. -/
@[expose] noncomputable def product (left : Space.{0, u} realSource) (right : Space.{0, v} realSource) :
    Hom (Space.product (object left) (object right)) (object (Space.product left right)) :=
  Hom.comp (bindValue left (Space.product left right))
    (Space.pair
      (Hom.comp (Space.curry (Hom.comp (strength left right) (Space.swap (object right) left)))
        (Space.second (object left) (object right)))
      (Space.first (object left) (object right)))

variable {left : Space.{0, u} realSource} {right : Space.{0, v} realSource}

/-- Evaluates the product morphism as monadic bind of the left law with the curried left strength after swapping inputs to fix the right law. -/
theorem product_apply (first : Law left) (second : Law right) :
    product left right (first, second) = bind first
      (Space.curry (Hom.comp (strength left right) (Space.swap (object right) left)) second) :=
  bindValue_apply _ first

/-- Proves that binding against the joint product equals contextual bind of the factors. -/
theorem product_bind {target : Space.{0, w} realSource}
    (first : Law left) (second : Law right) (kernel : Hom (Space.product left right) (object target)) :
    bind (product left right (first, second)) kernel =
      bind first (bindContext (Hom.constant left (object right) second) kernel) := by
  rw [product_apply, bind_assoc]
  apply congrArg (bind first)
  apply Hom.ext
  intro point
  change bind (strength left right (point, second)) kernel =
    bindContext (Hom.constant left (object right) second) kernel point
  rw [bindContext_apply]
  change bind (map (Space.pairLeft left right point) second) kernel =
    bind second (Space.curry kernel point)
  rw [bind_map]
  rfl

/-- Proves that pairing with a pure law on the left equals tensorial strength. -/
@[simp] theorem product_pure_left (point : left.Carrier) (law : Law right) :
    product left right (pure left point, law) = strength left right (point, law) := by
  rw [product_apply, pure_bind]
  rfl

/-- Proves that pairing with a pure law on the right equals pushforward along the right pairing section. -/
@[simp] theorem product_pure_right (law : Law left) (point : right.Carrier) :
    product left right (law, pure right point) =
      map (Space.pair (Hom.identity left) (Hom.constant left right point)) law := by
  rw [product_apply]
  apply congrArg (bind law)
  apply Hom.ext
  intro value
  exact strength_pure value point

/-- Proves that the product of pure Dirac laws is the pure Dirac law of the pair. -/
@[simp] theorem product_pure (first : left.Carrier) (second : right.Carrier) :
    product left right (pure left first, pure right second) =
      pure (Space.product left right) (first, second) := by
  rw [product_pure_left, strength_pure]

/-- Proves that the product with the zero law on the left is the zero law. -/
@[simp] theorem product_zero_left (law : Law right) :
    product left right (zero left, law) = zero (Space.product left right) := by
  rw [product_apply, zero_bind]

/-- Proves that the product with the zero law on the right is the zero law. -/
@[simp] theorem product_zero_right (law : Law left) :
    product left right (law, zero right) = zero (Space.product left right) := by
  rw [product_apply]
  have equal :
      Space.curry (Hom.comp (strength left right) (Space.swap (object right) left)) (zero right) =
        Hom.constant left (object (Space.product left right)) (zero (Space.product left right)) := by
    apply Hom.ext
    intro point
    exact strength_zero point
  rw [equal, bind_zero]

/-- Proves naturality of the joint product morphism with respect to morphism pairs. -/
theorem product_natural {first : Space.{0, w} realSource} {second : Space.{0, x} realSource}
    (firstMap : Hom left first) (secondMap : Hom right second)
    (firstLaw : Law left) (secondLaw : Law right) :
    map (Space.productMap firstMap secondMap) (product left right (firstLaw, secondLaw)) =
      product first second (map firstMap firstLaw, map secondMap secondLaw) := by
  rw [product_apply, map_bind, product_apply, bind_map]
  apply congrArg (bind firstLaw)
  apply Hom.ext
  intro point
  exact strength_natural firstMap secondMap point secondLaw

/-- Proves commutativity of the joint product morphism under coordinate swap. -/
theorem product_swap (first : Law left) (second : Law right) :
    map (Space.swap left right) (product left right (first, second)) =
      product right left (second, first) := by
  change bind (product left right (first, second))
    (Hom.comp (unit (Space.product right left)) (Space.swap left right)) = _
  rw [product_bind]
  have exchange := bind_comm second first (unit (Space.product right left))
  rw [← exchange, ← product_bind, bind_unit]

/-- Distributes monadic bind occurring inside the left input factor across the joint product. -/
theorem product_bind_left {source : Space.{0, w} realSource}
    (law : Law source) (kernel : Hom source (object left)) (second : Law right) :
    product left right (bind law kernel, second) =
      bind law (Hom.comp (product left right)
        (Space.pair kernel (Hom.constant source (object right) second))) := by
  rw [product_apply, bind_assoc]
  apply congrArg (bind law)
  apply Hom.ext
  intro point
  exact (product_apply (kernel point) second).symm

/-- Proves coherence between tensorial strength and the joint product under associativity. -/
theorem strength_product {third : Space.{0, w} realSource}
    (point : left.Carrier) (first : Law right) (second : Law third) :
    map (Space.associate left right third)
      (product (Space.product left right) third (strength left right (point, first), second)) =
      strength left (Space.product right third) (point, product right third (first, second)) := by
  have natural := product_natural (Space.pairLeft left right point) (Hom.identity third) first second
  simp only [map_id, Hom.identity_apply] at natural
  change map (Space.associate left right third)
    (product (Space.product left right) third (map (Space.pairLeft left right point) first, second)) =
      map (Space.pairLeft left (Space.product right third) point) (product right third (first, second))
  rw [← natural]
  apply Law.ext
  rw [map_val, map_val, Measure.map_comp, map_val]
  rfl

/-- Proves associativity of the joint product morphism on triples of laws. -/
theorem product_associate {third : Space.{0, w} realSource}
    (first : Law left) (second : Law right) (thirdLaw : Law third) :
    map (Space.associate left right third)
      (product (Space.product left right) third (product left right (first, second), thirdLaw)) =
      product left (Space.product right third) (first, product right third (second, thirdLaw)) := by
  rw [product_apply first second, product_bind_left, map_bind,
    product_apply first (product right third (second, thirdLaw))]
  apply congrArg (bind first)
  apply Hom.ext
  intro point
  exact strength_product point second thirdLaw

/-- Proves that projecting the left unit product recovers the original law. -/
theorem product_unit_left (law : Law right) :
    map (Space.second (Space.terminal realSource) right)
      (product (Space.terminal realSource) right (pure (Space.terminal realSource) (), law)) = law := by
  rw [product_pure_left]
  exact strength_unit law

/-- Proves that projecting the right unit product recovers the original law. -/
theorem product_unit_right (law : Law left) :
    map (Space.first left (Space.terminal realSource))
      (product left (Space.terminal realSource) (law, pure (Space.terminal realSource) ())) = law := by
  rw [product_pure_right]
  apply Law.ext
  rw [map_val, map_val, Measure.map_comp]
  exact Measure.map_id law.val

/-- Proves that the joint product morphism equals the canonical left-strength sequencing composite. -/
theorem product_strength : product left right =
    Hom.comp (extend (strength left right)) (costrength left (object right)) := by
  apply Hom.ext
  rintro ⟨first, second⟩
  rw [product_apply]
  apply Law.ext
  change (bind first
    (Space.curry (Hom.comp (strength left right) (Space.swap (object right) left)) second)).val =
      (bind (costrength left (object right) (first, second)) (strength left right)).val
  rw [bind_val, bind_val, costrength_val, Measure.bind_map]
  rfl

/-- Proves that the joint product morphism equals the canonical right-costrength sequencing composite. -/
theorem product_costrength : product left right =
    Hom.comp (extend (costrength left right)) (strength (object left) right) := by
  apply Hom.ext
  rintro ⟨first, second⟩
  rw [← product_swap second first, product_apply, map_bind]
  apply Law.ext
  change (bind second (Hom.comp (map (Space.swap right left))
    (Space.curry (Hom.comp (strength right left) (Space.swap (object left) right)) first))).val =
      (bind (strength (object left) right (first, second)) (costrength left right)).val
  rw [bind_val, bind_val, strength_val, Measure.bind_map]
  rfl

/-- Distributes monadic bind occurring inside the right input factor across the joint product. -/
theorem product_bind_right {source : Space.{0, w} realSource}
    (first : Law left) (law : Law source) (kernel : Hom source (object right)) :
    product left right (first, bind law kernel) =
      bind law (Hom.comp (product left right)
        (Space.pair (Hom.constant source (object left) first) kernel)) := by
  rw [← product_swap (bind law kernel) first, product_bind_left, map_bind]
  apply congrArg (bind law)
  apply Hom.ext
  intro point
  exact product_swap (kernel point) first

/-- Distributes simultaneous monadic binds across both input factors into a single bind against the joint product. -/
theorem product_bind_pair {first : Space.{0, w} realSource} {second : Space.{0, x} realSource}
    (leftLaw : Law left) (rightLaw : Law right)
    (leftKernel : Hom left (object first)) (rightKernel : Hom right (object second)) :
    product first second (bind leftLaw leftKernel, bind rightLaw rightKernel) =
      bind (product left right (leftLaw, rightLaw))
        (Hom.comp (product first second) (Space.productMap leftKernel rightKernel)) := by
  rw [product_bind_left, product_bind]
  apply congrArg (bind leftLaw)
  apply Hom.ext
  intro point
  change product first second (leftKernel point, bind rightLaw rightKernel) =
    bindContext (Hom.constant left (object right) rightLaw)
      (Hom.comp (product first second) (Space.productMap leftKernel rightKernel)) point
  rw [product_bind_right, bindContext_apply]
  apply congrArg (bind rightLaw)
  apply Hom.ext
  intro value
  rfl

end

end Problib.QuasiBorel.SFinite
