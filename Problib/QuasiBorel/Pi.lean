module

public import Problib.QuasiBorel.Space

set_option autoImplicit false

namespace Problib.QuasiBorel.Space

universe u v w

variable {Ω : Type u} {source : Source Ω} {ι : Type v}

public section

/-- Arbitrary product quasi-Borel space over an abstract random source.
A map into the product is an accepted random element if and only if each
coordinate projection is accepted. -/
@[expose] def pi (spaces : ι → Space source) : Space source where
  Carrier := ∀ index, (spaces index).Carrier
  Random := fun random => ∀ index, (spaces index).Random (fun seed => random seed index)
  constant := fun point index => (spaces index).constant (point index)
  reparam := by
    intro parameter random measurable accepted index
    exact (spaces index).reparam measurable (accepted index)
  piecewise := by
    intro partition branches measurable accepted index
    exact (spaces index).piecewise measurable (fun branch => accepted branch index)

/-- Coordinate projection morphism from the product quasi-Borel space. -/
@[expose] def project (spaces : ι → Space source) (index : ι) :
    Hom (pi spaces) (spaces index) where
  toFun := fun point => point index
  map_random := fun accepted => accepted index

/-- Universal mediating morphism into the product quasi-Borel space from a
family of coordinate morphisms. -/
@[expose] def tuple {domain : Space source} {spaces : ι → Space source}
    (functions : ∀ index, Hom domain (spaces index)) : Hom domain (pi spaces) where
  toFun := fun point index => functions index point
  map_random := fun accepted index => (functions index).map_random accepted

/-- Projecting the mediating tuple recovers the coordinate morphism. -/
theorem project_tuple {domain : Space source} {spaces : ι → Space source}
    (functions : ∀ index, Hom domain (spaces index)) (index : ι) :
    Hom.comp (project spaces index) (tuple functions) = functions index := by
  apply Hom.ext
  intro point
  rfl

/-- The mediating tuple of all coordinate projections is the identity morphism
on the product. -/
theorem tuple_project (spaces : ι → Space source) :
    tuple (fun index => project spaces index) = Hom.identity (pi spaces) := by
  apply Hom.ext
  intro point
  rfl

/-- Uniqueness of the mediating morphism into the product quasi-Borel space. -/
theorem tuple_unique {domain : Space source} {spaces : ι → Space source}
    (functions : ∀ index, Hom domain (spaces index)) (candidate : Hom domain (pi spaces))
    (coordinates : ∀ index, Hom.comp (project spaces index) candidate = functions index) :
    candidate = tuple functions := by
  apply Hom.ext
  intro point
  funext index
  exact congrArg (fun function => function point) (coordinates index)

end

end Problib.QuasiBorel.Space
