import Problib.QuasiBorel.Probability.StandardBorel
import Problib.Measure.Kernel.Pi.Basic
import Problib.Measure.StandardBorel.Pi
import Problib.Measure.Giry.Kernel

/-!
# Countable products of standard-Borel probability laws

A law-valued morphism out of a countable key space and a parameter space gives,
at each parameter, one probability law per key. This module takes the product of
those laws over all keys, as a morphism from the parameter space into laws on
the measurable product of the target. Each value is the product law of the
body's laws at the keys, and product laws are unique, so the product at a
parameter depends only on the body's laws there.

The target must be standard Borel. The construction reads the body as a
measurable kernel on the measurable product of the key space and the
parameter's induced space, takes Problib's countable product kernel, and
carries the result back through the standard-Borel comparison of Giry laws
with quasi-Borel laws.
-/

set_option autoImplicit false

namespace Problib.QuasiBorel.Probability

open Problib.Measure hiding Space
open Problib.Measure.Real (Carrier borel)

variable {κ β : Type} {keySpace : Problib.Measure.Space κ}
  {target : Problib.Measure.Space β} {domain : Space (Source.ofMeasurable borel)}

/-- A morphism into a generated space is measurable on the induced space. -/
private theorem measurable_of_hom {source : Space (Source.ofMeasurable borel)} {γ : Type}
    {codomain : Problib.Measure.Space γ}
    (morphism : Hom source (Space.ofMeasurable borel codomain)) :
    MeasurableMap source.toMeasurable codomain morphism :=
  Space.measurableMap_iff_random.mpr fun accepted => morphism.map_random accepted

/-- A set measurable for the quasi-Borel product of a countable key space with
any space is measurable for the measurable product of the key space and that
space's induced space: it is the union over the keys of each key times its
section. -/
theorem product_measurable_of_countable (code : κ → Nat) (injective : Function.Injective code)
    (singleton : ∀ key, keySpace.Measurable (Set.singleton key))
    {set : Set (κ × domain.Carrier)}
    (measurable :
      (Space.product (Space.ofMeasurable borel keySpace) domain).toMeasurable.Measurable set) :
    (Problib.Measure.Space.product keySpace domain.toMeasurable).Measurable set := by
  have section_measurable : ∀ key, domain.toMeasurable.Measurable
      (Set.preimage (fun point => (key, point)) set) := fun key =>
    Hom.toMeasurable (Space.pair (Hom.constant domain (Space.ofMeasurable borel keySpace) key)
      (Hom.identity domain)) measurable
  have union : set = Set.iUnion (fun index => fun pair => code pair.1 = index ∧ set pair) := by
    apply Set.ext
    intro pair
    exact ⟨fun member => ⟨code pair.1, rfl, member⟩, fun ⟨_, _, member⟩ => member⟩
  rw [union]
  refine (Problib.Measure.Space.product keySpace domain.toMeasurable).iUnion fun index => ?_
  by_cases named : ∃ key, code key = index
  · obtain ⟨key, rfl⟩ := named
    have piece : (fun pair : κ × domain.Carrier => code pair.1 = code key ∧ set pair) =
        Set.product (Set.singleton key) (Set.preimage (fun point => (key, point)) set) := by
      apply Set.ext
      intro pair
      constructor
      · intro ⟨same, member⟩
        have equal : pair.1 = key := injective same
        refine ⟨equal, ?_⟩
        change set (key, pair.2)
        rw [← equal]
        exact member
      · intro ⟨equal, member⟩
        refine ⟨congrArg code equal, ?_⟩
        have pairEqual : pair = (key, pair.2) := by
          cases pair
          cases equal
          rfl
        rw [pairEqual]
        exact member
    rw [piece]
    exact Problib.Measure.Space.product_set_measurable keySpace domain.toMeasurable
      (singleton key) (section_measurable key)
  · have piece : (fun pair : κ × domain.Carrier => code pair.1 = index ∧ set pair) =
        Set.empty := by
      apply Set.ext
      intro pair
      exact ⟨fun ⟨same, _⟩ => named ⟨pair.1, same⟩, False.elim⟩
    rw [piece]
    exact (Problib.Measure.Space.product keySpace domain.toMeasurable).empty

/-- The body read as a measurable kernel on the measurable product of the key
space and the parameter's induced space. -/
noncomputable def keyedKernel (code : κ → Nat) (injective : Function.Injective code)
    (singleton : ∀ key, keySpace.Measurable (Set.singleton key))
    (presentation : Problib.Measure.StandardBorel target)
    (body : Hom (Space.product (Space.ofMeasurable borel keySpace) domain)
      (object (Space.ofMeasurable borel target))) :
    Kernel (Problib.Measure.Space.product keySpace domain.toMeasurable) target :=
  Giry.toKernel (fun pair => StandardBorel.toGiry presentation (body pair))
    fun {_} regionMeasurable => product_measurable_of_countable code injective singleton
      (measurable_of_hom (Hom.comp (StandardBorel.toGiryHom presentation) body) regionMeasurable)

/-- The countable product of the body's laws as a kernel on the parameter's
induced space. -/
noncomputable def countableProductKernel (code : κ → Nat) (injective : Function.Injective code)
    (singleton : ∀ key, keySpace.Measurable (Set.singleton key))
    (presentation : Problib.Measure.StandardBorel target)
    (body : Hom (Space.product (Space.ofMeasurable borel keySpace) domain)
      (object (Space.ofMeasurable borel target))) :
    Kernel domain.toMeasurable (Problib.Measure.Space.pi fun _ : κ => target) :=
  Kernel.pi code (Kernel.Randomizer.ofStandardBorel
    (keyedKernel code injective singleton presentation body) presentation
    fun pair => (StandardBorel.toGiry presentation (body pair)).property)

/-- At each parameter, the product kernel's law is the product of the body's
laws at the keys. -/
theorem countableProductKernel_isProduct (code : κ → Nat) (injective : Function.Injective code)
    (singleton : ∀ key, keySpace.Measurable (Set.singleton key))
    (presentation : Problib.Measure.StandardBorel target)
    (body : Hom (Space.product (Space.ofMeasurable borel keySpace) domain)
      (object (Space.ofMeasurable borel target)))
    (point : domain.Carrier) :
    Pi.IsProduct (countableProductKernel code injective singleton presentation body point)
      fun key => (StandardBorel.toGiry presentation (body (key, point))).val :=
  Kernel.pi_isProduct code injective _ point

/-- The countable product of a law-valued morphism over a countable key space,
as a morphism into laws on the measurable product of a standard-Borel target. -/
noncomputable def countableProduct (code : κ → Nat) (injective : Function.Injective code)
    (singleton : ∀ key, keySpace.Measurable (Set.singleton key))
    (presentation : Problib.Measure.StandardBorel target)
    (body : Hom (Space.product (Space.ofMeasurable borel keySpace) domain)
      (object (Space.ofMeasurable borel target))) :
    Hom domain
      (object (Space.ofMeasurable borel (Problib.Measure.Space.pi fun _ : κ => target))) :=
  Hom.comp
    (StandardBorel.ofGiryHom
      (Problib.Measure.StandardBorel.piOfNatInjection code injective fun _ => presentation))
    { toFun := Giry.ofKernel (countableProductKernel code injective singleton presentation body)
        fun point => Kernel.pi_probability code _ point
      map_random := fun accepted =>
        Space.measurableMap_iff_random.mp
          (Giry.ofKernel_measurable (countableProductKernel code injective singleton
            presentation body) fun point => Kernel.pi_probability code _ point) accepted }

/-- Read back as a Giry law, the product at a parameter is the product kernel
there. -/
theorem toGiry_countableProduct (code : κ → Nat) (injective : Function.Injective code)
    (singleton : ∀ key, keySpace.Measurable (Set.singleton key))
    (presentation : Problib.Measure.StandardBorel target)
    (body : Hom (Space.product (Space.ofMeasurable borel keySpace) domain)
      (object (Space.ofMeasurable borel target)))
    (point : domain.Carrier) :
    (StandardBorel.toGiry
        (Problib.Measure.StandardBorel.piOfNatInjection code injective fun _ => presentation)
        (countableProduct code injective singleton presentation body point)).val =
      countableProductKernel code injective singleton presentation body point := by
  change (StandardBorel.toGiry _ (StandardBorel.ofGiry _ _)).val = _
  rw [StandardBorel.toGiry_ofGiry]
  rfl

/-- Reading a law as a Giry law does not depend on the standard-Borel
presentation: the comparison is the identity on points for every presentation. -/
theorem toGiry_presentation {γ : Type} {space : Problib.Measure.Space γ}
    (first second : Problib.Measure.StandardBorel space)
    (law : Law (Space.ofMeasurable borel space)) :
    StandardBorel.toGiry first law = StandardBorel.toGiry second law :=
  rfl

/-- Each value of the countable product, read as a Giry law through any
presentation of the product, is the product of the body's laws at the keys. -/
theorem countableProduct_isProduct (code : κ → Nat) (injective : Function.Injective code)
    (singleton : ∀ key, keySpace.Measurable (Set.singleton key))
    (presentation : Problib.Measure.StandardBorel target)
    (body : Hom (Space.product (Space.ofMeasurable borel keySpace) domain)
      (object (Space.ofMeasurable borel target)))
    (product : Problib.Measure.StandardBorel (Problib.Measure.Space.pi fun _ : κ => target))
    (point : domain.Carrier) :
    Pi.IsProduct
      (StandardBorel.toGiry product
        (countableProduct code injective singleton presentation body point)).val
      fun key => (StandardBorel.toGiry presentation (body (key, point))).val := by
  rw [toGiry_presentation product
    (Problib.Measure.StandardBorel.piOfNatInjection code injective fun _ => presentation),
    toGiry_countableProduct]
  exact countableProductKernel_isProduct code injective singleton presentation body point

/-- The product at a parameter reads only the body's laws there: bodies with
equal laws at every key give equal products. -/
theorem countableProduct_congr_at {other : Space (Source.ofMeasurable borel)}
    (code : κ → Nat) (injective : Function.Injective code)
    (singleton : ∀ key, keySpace.Measurable (Set.singleton key))
    (presentation : Problib.Measure.StandardBorel target)
    (left : Hom (Space.product (Space.ofMeasurable borel keySpace) domain)
      (object (Space.ofMeasurable borel target)))
    (right : Hom (Space.product (Space.ofMeasurable borel keySpace) other)
      (object (Space.ofMeasurable borel target)))
    {leftPoint : domain.Carrier} {rightPoint : other.Carrier}
    (equal : ∀ key, left (key, leftPoint) = right (key, rightPoint)) :
    countableProduct code injective singleton presentation left leftPoint =
      countableProduct code injective singleton presentation right rightPoint := by
  change StandardBorel.ofGiry _ _ = StandardBorel.ofGiry _ _
  apply congrArg
  apply Subtype.ext
  exact Pi.IsProduct.ext
    (countableProductKernel_isProduct code injective singleton presentation left leftPoint)
    ((countableProductKernel_isProduct code injective singleton presentation right
      rightPoint).congr_laws fun key => by rw [equal key])

end Problib.QuasiBorel.Probability
