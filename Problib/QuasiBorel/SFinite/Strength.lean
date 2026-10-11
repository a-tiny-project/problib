module

public import Problib.QuasiBorel.SFinite.Monad
public import Problib.QuasiBorel.SFinite.Standard.Joint

set_option autoImplicit false

/-!
# Tensorial strength and costrength for the s-finite quasi-Borel monad

This module constructs the canonical tensorial left strength and right costrength
morphisms for the s-finite quasi-Borel space monad.
It proves standard strong monad coherence laws (pure, naturality, associator
coherence, and bind compatibility), as well as additional verified laws for zero
absorption and projection recovery.
-/

namespace Problib.QuasiBorel.SFinite

public section

open Problib.Measure hiding Space
open Problib.Measure.Real (Carrier borel)

universe u v w x

/-- Canonical left tensorial strength morphism for the s-finite quasi-Borel monad. -/
@[expose] noncomputable def strength (left : Space.{0, u} realSource) (right : Space.{0, v} realSource) :
    Hom (Space.product left (object right)) (object (Space.product left right)) where
  toFun := fun point => map (Space.pairLeft left right point.1) point.2
  map_random := by
    intro random accepted
    let family := Standard.Family.ofPartial (Classical.choice accepted.2)
    let joint : Standard.JointFamily (Space.product left right)
        (fun seed => map (Space.pairLeft left right (random seed).1) (random seed).2) := {
      Seed := family.Seed
      source := family.source
      standard := family.standard
      random := {
        toFun := fun point => ((random point.1).1, family.random point.2)
        map_random := by
          intro input measurable
          exact ⟨left.reparam
            (MeasurableMap.comp
              (Problib.Measure.Space.first_measurable borel family.source) measurable) accepted.1,
            family.random.map_random (MeasurableMap.comp
              (Problib.Measure.Space.second_measurable borel family.source) measurable)⟩
      }
      kernel := family.kernel
      sfinite := family.sfinite
      law := by
        intro seed
        rw [map_val, ← family.law seed, Measure.map_comp]
        rfl
    }
    exact ⟨joint.toPartial⟩

variable {left : Space.{0, u} realSource} {right : Space.{0, v} realSource}

/-- Proves that left strength evaluates to pushforward along the left pair section. -/
theorem strength_val (point : left.Carrier) (law : Law right) :
    (strength left right (point, law)).val =
      law.val.map (Space.pairLeft left right point) (Space.pairLeft left right point).toMeasurable :=
  map_val _ law

/-- Proves that left strength preserves pure Dirac laws. -/
@[simp] theorem strength_pure (point : left.Carrier) (value : right.Carrier) :
    strength left right (point, pure right value) = pure (Space.product left right) (point, value) :=
  map_pure (Space.pairLeft left right point) value

/-- Proves that left strength preserves the zero law on the right factor. -/
@[simp] theorem strength_zero (point : left.Carrier) :
    strength left right (point, zero right) = zero (Space.product left right) :=
  map_zero (Space.pairLeft left right point)

/-- Proves naturality of left strength with respect to morphism pairs. -/
theorem strength_natural {first : Space.{0, w} realSource} {second : Space.{0, x} realSource}
    (firstMap : Hom left first) (secondMap : Hom right second)
    (point : left.Carrier) (law : Law right) :
    map (Space.productMap firstMap secondMap) (strength left right (point, law)) =
      strength first second (firstMap point, map secondMap law) := by
  apply Law.ext
  rw [map_val, strength_val, strength_val, map_val, Measure.map_comp, Measure.map_comp]
  rfl

/-- Proves that left strength followed by projection to the second coordinate recovers the law. -/
theorem strength_second (point : left.Carrier) (law : Law right) :
    map (Space.second left right) (strength left right (point, law)) = law := by
  apply Law.ext
  rw [map_val, strength_val, Measure.map_comp]
  exact Measure.map_id law.val

/-- Proves that left strength with the terminal unit space recovers the law under projection. -/
theorem strength_unit (law : Law right) :
    map (Space.second (Space.terminal realSource) right)
      (strength (Space.terminal realSource) right ((), law)) = law :=
  strength_second (left := Space.terminal realSource) () law

/-- Proves associativity coherence for left strength with respect to nested Cartesian products. -/
theorem strength_associate {third : Space.{0, w} realSource}
    (first : left.Carrier) (second : right.Carrier) (law : Law third) :
    map (Space.associate left right third)
      (strength (Space.product left right) third ((first, second), law)) =
      strength left (Space.product right third) (first, strength right third (second, law)) := by
  apply Law.ext
  rw [map_val, strength_val, strength_val, strength_val, Measure.map_comp, Measure.map_comp]
  rfl

/-- Proves that left strength commutes with monadic bind. -/
theorem strength_bind {third : Space.{0, w} realSource}
    (point : left.Carrier) (law : Law right) (kernel : Hom right (object third)) :
    strength left third (point, bind law kernel) =
      bind (strength left right (point, law))
        (Hom.comp (strength left third) (Space.productMap (Hom.identity left) kernel)) := by
  apply Law.ext
  rw [strength_val, bind_val, Measure.map_bind, bind_val, strength_val, Measure.bind_map]
  apply congrArg (fun next => law.val.bind next)
  apply Kernel.ext
  intro value
  exact (strength_val point (kernel value)).symm

/-- Canonical right tensorial costrength morphism obtained by symmetry from left strength. -/
@[expose] noncomputable def costrength (left : Space.{0, u} realSource) (right : Space.{0, v} realSource) :
    Hom (Space.product (object left) right) (object (Space.product left right)) :=
  Hom.comp (map (Space.swap right left))
    (Hom.comp (strength right left) (Space.swap (object left) right))

/-- Proves that costrength applies as pushforward along the right pair section. -/
theorem costrength_apply (law : Law left) (point : right.Carrier) :
    costrength left right (law, point) =
      map (Space.pair (Hom.identity left) (Hom.constant left right point)) law := by
  apply Law.ext
  change (map (Space.swap right left) (strength right left (point, law))).val = _
  rw [map_val, strength_val, Measure.map_comp, map_val]
  rfl

/-- Proves the measure formula for costrength as pushforward along the right pair section. -/
theorem costrength_val (law : Law left) (point : right.Carrier) :
    (costrength left right (law, point)).val =
      law.val.map (Space.pair (Hom.identity left) (Hom.constant left right point))
        (Space.pair (Hom.identity left) (Hom.constant left right point)).toMeasurable := by
  rw [costrength_apply, map_val]

/-- Proves that costrength preserves pure Dirac laws. -/
@[simp] theorem costrength_pure (point : left.Carrier) (value : right.Carrier) :
    costrength left right (pure left point, value) = pure (Space.product left right) (point, value) := by
  rw [costrength_apply, map_pure]
  rfl

/-- Proves that costrength preserves the zero law on the left factor. -/
@[simp] theorem costrength_zero (point : right.Carrier) :
    costrength left right (zero left, point) = zero (Space.product left right) := by
  rw [costrength_apply, map_zero]

/-- Proves naturality of costrength with respect to morphism pairs. -/
theorem costrength_natural {first : Space.{0, w} realSource} {second : Space.{0, x} realSource}
    (firstMap : Hom left first) (secondMap : Hom right second)
    (law : Law left) (point : right.Carrier) :
    map (Space.productMap firstMap secondMap) (costrength left right (law, point)) =
      costrength first second (map firstMap law, secondMap point) := by
  apply Law.ext
  rw [map_val, costrength_val, costrength_val, map_val, Measure.map_comp, Measure.map_comp]
  rfl

/-- Proves that costrength followed by projection to the first coordinate recovers the law. -/
theorem costrength_first (law : Law left) (point : right.Carrier) :
    map (Space.first left right) (costrength left right (law, point)) = law := by
  apply Law.ext
  rw [map_val, costrength_val, Measure.map_comp]
  exact Measure.map_id law.val

/-- Proves that costrength commutes with monadic bind on the left factor. -/
theorem costrength_bind {source : Space.{0, w} realSource}
    (law : Law source) (kernel : Hom source (object left)) (point : right.Carrier) :
    costrength left right (bind law kernel, point) =
      bind (costrength source right (law, point))
        (Hom.comp (costrength left right) (Space.productMap kernel (Hom.identity right))) := by
  apply Law.ext
  rw [costrength_val, bind_val, Measure.map_bind, bind_val, costrength_val, Measure.bind_map]
  apply congrArg (fun next => law.val.bind next)
  apply Kernel.ext
  intro value
  exact (costrength_val (kernel value) point).symm

end

end Problib.QuasiBorel.SFinite
