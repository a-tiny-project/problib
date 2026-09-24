import Problib.QuasiBorel.Probability.Random

set_option autoImplicit false

namespace Problib.QuasiBorel.Probability

open Problib.Measure hiding Space
open Problib.Measure.Real (Carrier borel)

universe u v w

/-- Point-mass Dirac probability law on a quasi-Borel space at a given point. -/
noncomputable def pure (space : Space (Source.ofMeasurable borel)) (point : space.Carrier) :
    Law space := by
  refine ⟨Giry.pure space.toMeasurable point, ?_⟩
  refine ⟨⟨fun _ => point, space.constant point,
    Giry.pure borel Problib.Real.Construction.Dedekind.zero⟩, ?_⟩
  exact Giry.map_pure (fun _ => point) (Space.random_measurable (space.constant point)) _

/-- Unit of the probability monad, embedding each quasi-Borel point into its Dirac law as a morphism. -/
noncomputable def unit (space : Space (Source.ofMeasurable borel)) :
    Hom space (object space) where
  toFun := pure space
  map_random := by
    intro random accepted
    exact ⟨{
      random := random
      accepted := accepted
      kernel := Giry.pure borel
      measurable := Giry.pure_measurable borel
      law := fun seed => Giry.map_pure random (Space.random_measurable accepted) seed
    }⟩

/-- The space of representable probability laws is nonempty if and only if the underlying carrier is nonempty. -/
theorem nonempty_iff (space : Space (Source.ofMeasurable borel)) :
    Nonempty (Law space) ↔ Nonempty space.Carrier := by
  constructor
  · rintro ⟨law⟩
    exact law.val.property.nonempty
  · rintro ⟨point⟩
    exact ⟨pure space point⟩

variable {domain codomain : Space (Source.ofMeasurable borel)}

/-- A quasi-Borel morphism into the probability space induces a measurable kernel between the induced measurable spaces. -/
theorem kernel_measurable (kernel : Hom domain (object codomain)) :
    MeasurableMap domain.toMeasurable (Giry.space codomain.toMeasurable)
      (fun point => (kernel point).val) := by
  intro region measurable
  exact kernel.toMeasurable (toGiry_measurable codomain measurable)

/-- Representation formula for monadic bind, expressing the pushed-forward bound law through the underlying measurable kernel bind. -/
theorem bind_representation (kernel : Hom domain (object codomain))
    {random : Carrier → domain.Carrier} (accepted : domain.Random random)
    (family : Family codomain (fun seed => kernel (random seed))) (law : Giry.Law borel) :
    Giry.map family.random (Space.random_measurable family.accepted)
        (Giry.bind law family.kernel family.measurable) =
      Giry.bind (Giry.map random (Space.random_measurable accepted) law)
        (fun point => (kernel point).val) (kernel_measurable kernel) := by
  rw [Giry.map_bind, Giry.bind_map]
  have equal : (fun seed => Giry.map family.random (Space.random_measurable family.accepted)
      (family.kernel seed)) = (fun seed => (kernel (random seed)).val) := funext family.law
  simp only [equal]

/-- Monadic bind for quasi-Borel probability laws, integrating a measurable continuation family. -/
noncomputable def bind (law : Law domain) (kernel : Hom domain (object codomain)) : Law codomain := by
  refine ⟨Giry.bind law.val (fun point => (kernel point).val) (kernel_measurable kernel), ?_⟩
  let family := Classical.choice (kernel.map_random law.presentation.accepted)
  refine ⟨⟨family.random, family.accepted,
    Giry.bind law.presentation.sourceLaw family.kernel family.measurable⟩, ?_⟩
  change Giry.map family.random (Space.random_measurable family.accepted)
    (Giry.bind law.presentation.sourceLaw family.kernel family.measurable) = _
  rw [bind_representation kernel law.presentation.accepted family]
  change Giry.bind law.presentation.toGiry _ _ = _
  rw [law.presentation_toGiry]

/-- The underlying Giry law of a quasi-Borel bind is the Giry bind of the factor laws. -/
theorem bind_val (law : Law domain) (kernel : Hom domain (object codomain)) :
    (bind law kernel).val = Giry.bind law.val
      (fun point => (kernel point).val) (kernel_measurable kernel) := rfl

/-- Unfolds monadic bind into an integral over the real Borel random source. -/
theorem bind_source (law : Law domain) (kernel : Hom domain (object codomain)) :
    (bind law kernel).val =
      Giry.bind law.presentation.sourceLaw (fun seed => (kernel (law.presentation.random seed)).val)
        (MeasurableMap.comp (kernel_measurable kernel) (Space.random_measurable law.presentation.accepted)) := by
  rw [bind_val, ← law.presentation_toGiry]
  exact Giry.bind_map law.presentation.sourceLaw law.presentation.random
    (Space.random_measurable law.presentation.accepted) (fun point => (kernel point).val)
    (kernel_measurable kernel)

/-- Pushing a representing family through a quasi-Borel kernel yields a valid representing family for the bound laws. -/
noncomputable def Family.bind {laws : Carrier → Law domain} (family : Family domain laws)
    (kernel : Hom domain (object codomain)) : Family codomain (fun seed => bind (laws seed) kernel) := by
  let continuation := Classical.choice (kernel.map_random family.accepted)
  refine {
    random := continuation.random
    accepted := continuation.accepted
    kernel := fun seed => Giry.bind (family.kernel seed) continuation.kernel continuation.measurable
    measurable := MeasurableMap.comp (Giry.bind_measurable continuation.kernel continuation.measurable)
      family.measurable
    law := ?_
  }
  intro seed
  rw [bind_representation kernel family.accepted continuation, family.law seed]
  rfl

/-- Kleisli extension lifting a quasi-Borel kernel to a morphism between probability spaces. -/
noncomputable def extend (kernel : Hom domain (object codomain)) :
    Hom (object domain) (object codomain) where
  toFun := fun law => bind law kernel
  map_random := by
    intro random accepted
    exact ⟨(Classical.choice accepted).bind kernel⟩

/-- Right unit law for Kleisli extension: extending the monad unit is the identity morphism. -/
theorem extend_unit_right (space : Space (Source.ofMeasurable borel)) :
    extend (unit space) = Hom.identity (object space) := by
  apply Hom.ext
  intro law
  apply Law.ext
  exact Giry.bind_pure law.val

/-- Left unit law for Kleisli extension: precomposing an extension with the monad unit recovers the kernel. -/
theorem extend_unit_left (kernel : Hom domain (object codomain)) :
    Hom.comp (extend kernel) (unit domain) = kernel := by
  apply Hom.ext
  intro point
  apply Law.ext
  exact Giry.pure_bind point (fun value => (kernel value).val) (kernel_measurable kernel)

/-- Associativity of Kleisli composition for quasi-Borel probability kernels. -/
theorem extend_assoc {result : Space (Source.ofMeasurable borel)}
    (first : Hom domain (object codomain)) (second : Hom codomain (object result)) :
    Hom.comp (extend second) (extend first) =
      extend (Hom.comp (extend second) first) := by
  apply Hom.ext
  intro law
  apply Law.ext
  exact Giry.bind_assoc law.val (fun value => (first value).val) (kernel_measurable first)
    (fun value => (second value).val) (kernel_measurable second)

/-- Functorial pushforward of probability laws along a quasi-Borel morphism. -/
noncomputable def map (function : Hom domain codomain) : Hom (object domain) (object codomain) :=
  extend (Hom.comp (unit codomain) function)

/-- Functorial pushforward agrees with the Giry measure pushforward. -/
theorem map_val (function : Hom domain codomain) (law : Law domain) :
    (map function law).val = Giry.map function function.toMeasurable law.val :=
  Giry.bind_pure_comp law.val function function.toMeasurable

/-- Functorial pushforward along the identity morphism is the identity. -/
theorem map_id (space : Space (Source.ofMeasurable borel)) :
    map (Hom.identity space) = Hom.identity (object space) := by
  apply Hom.ext
  intro law
  apply Law.ext
  rw [map_val]
  exact Giry.map_id law.val

/-- Functorial pushforward distributes over morphism composition. -/
theorem map_comp {result : Space (Source.ofMeasurable borel)}
    (after : Hom codomain result) (before : Hom domain codomain) :
    map (Hom.comp after before) = Hom.comp (map after) (map before) := by
  apply Hom.ext
  intro law
  apply Law.ext
  change (map (Hom.comp after before) law).val = (map after (map before law)).val
  rw [map_val, map_val, map_val]
  exact (Giry.map_comp law.val before after before.toMeasurable after.toMeasurable).symm

/-- Functorial pushforward maps a Dirac law at a point to the Dirac law at the image point. -/
theorem map_pure (function : Hom domain codomain) (point : domain.Carrier) :
    map function (pure domain point) = pure codomain (function point) := by
  apply Law.ext
  rw [map_val]
  exact Giry.map_pure function function.toMeasurable point

end Problib.QuasiBorel.Probability
