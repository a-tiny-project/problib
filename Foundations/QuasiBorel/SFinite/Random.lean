module

public import Foundations.QuasiBorel.SFinite.Representation
public import Foundations.QuasiBorel.Measurable.Family
public import Foundations.Measure.Kernel.Comap
public import Foundations.Measure.Kernel.Precomp
public import Foundations.Measure.Kernel.Piecewise.Countable

set_option autoImplicit false

/-!
# Parameterized random families and quasi-Borel structure on laws

This module defines parameterized random families of s-finite laws.
Families carry a shared generator and a global s-finite real kernel.
Countable gluing, reparameterization, and constants equip the law space with a
canonical quasi-Borel space structure.
Evaluation against measurable sets is measurable, and morphisms into the law
object induce measurable kernels.
Precomposition with any accepted real random element yields a global s-finite
kernel certificate.
-/
namespace Foundations.QuasiBorel.SFinite

public section

open Foundations.Measure hiding Space
open Foundations.Measure.Real (Carrier borel)

universe u v w

/-- Parameterized family of s-finite laws sharing a generator and global kernel. -/
structure Family (space : Space realSource) (laws : Carrier → Law space) extends Generator space where
  /-- Transition kernel on the real random source. -/
  kernel : Kernel borel borel
  /-- Certificate that the transition kernel is globally s-finite. -/
  sfinite : Kernel.IsSFinite kernel
  /-- Law equation identifying the pushforward-pullback measure at each parameter. -/
  law : ∀ seed, ((kernel seed).map random (Space.random_measurable accepted)).comap
    (Space.inrEmbedding (Space.terminal realSource) space) = (laws seed).val

/-- Predicate asserting that a family of laws is witnessed by an accepted family. -/
@[expose] def Random (space : Space realSource) (laws : Carrier → Law space) : Prop :=
  Nonempty (Family space laws)

namespace Family

variable {space : Space realSource} {laws : Carrier → Law space}

/-- Converts a family of laws into a transition kernel on the induced measurable space. -/
@[expose] noncomputable def toKernel (family : Family space laws) :
    Kernel borel space.toMeasurable :=
  (family.kernel.map family.random (Space.random_measurable family.accepted)).comap
    (Space.inrEmbedding (Space.terminal realSource) space)

/-- Proves that the converted kernel evaluates to the family law at each parameter. -/
@[simp] theorem toKernel_apply (family : Family space laws) (seed : Carrier) :
    family.toKernel seed = (laws seed).val :=
  family.law seed

/-- Derives a global s-finite certificate for the converted transition kernel. -/
@[expose] noncomputable def toKernel_sfinite (family : Family space laws) :
    Kernel.IsSFinite family.toKernel :=
  (family.sfinite.map family.random (Space.random_measurable family.accepted)).comap
    (Space.inrEmbedding (Space.terminal realSource) space)

/-- Constructs a constant family of laws from any single represented law. -/
@[expose] noncomputable def constant (law : Law space) : Family space (fun _ => law) where
  random := law.presentation.random
  accepted := law.presentation.accepted
  kernel := Kernel.const borel law.presentation.sourceMeasure
  sfinite := Kernel.IsSFinite.const borel law.presentation.sfinite
  law := fun _ => law.presentation_toMeasure

/-- Reparameterizes a family of laws along a measurable real map. -/
@[expose] noncomputable def reparam (family : Family space laws)
    {parameter : Carrier → Carrier} (measurable : MeasurableMap borel borel parameter) :
    Family space (fun seed => laws (parameter seed)) where
  random := family.random
  accepted := family.accepted
  kernel := family.kernel.precomp parameter measurable
  sfinite := family.sfinite.precomp parameter measurable
  law := fun seed => family.law (parameter seed)

/-- Glues a countable sequence of families along a measurable partition. -/
@[expose] noncomputable def piecewise {partition : Carrier → Nat}
    (measurable : realSource.Partition partition)
    {branches : Nat → Carrier → Law space} (families : ∀ index, Family space (branches index)) :
    Family space (fun seed => branches (partition seed) seed) where
  random := RandomFamily.join (fun index => (families index).random)
  accepted := RandomFamily.join_random (fun index => (families index).accepted)
  kernel := Kernel.countablePiecewise partition measurable (fun index =>
    (families index).kernel.map (RandomFamily.select index) (RandomFamily.select_measurable index))
  sfinite := Kernel.IsSFinite.countablePiecewise partition measurable _ (fun index =>
    (families index).sfinite.map (RandomFamily.select index) (RandomFamily.select_measurable index))
  law := by
    intro seed
    rw [Kernel.countablePiecewise_apply, Kernel.map_apply, Measure.map_comp]
    have equal :
        (fun point => RandomFamily.join (fun index => (families index).random)
          (RandomFamily.select (partition seed) point)) = (families (partition seed)).random :=
      funext (RandomFamily.join_select _ (partition seed))
    simpa only [equal] using (families (partition seed)).law seed

end Family

/-- Equips the space of represented laws with its canonical quasi-Borel structure. -/
@[expose] noncomputable def object (space : Space realSource) : Space realSource where
  Carrier := Law space
  Random := Random space
  constant := fun law => ⟨Family.constant law⟩
  reparam := by
    intro parameter random measurable accepted
    exact ⟨(Classical.choice accepted).reparam measurable⟩
  piecewise := by
    intro partition branches measurable accepted
    exact ⟨Family.piecewise measurable (fun index => Classical.choice (accepted index))⟩

/-- Proves that evaluation of laws against any measurable set is measurable. -/
theorem evaluation_measurable (space : Space realSource)
    {region : Set space.Carrier} (measurable : space.toMeasurable.Measurable region) :
    ENNRealMeasurable (object space).toMeasurable (fun law : Law space => law.val region) := by
  intro threshold random accepted
  rcases accepted with ⟨family⟩
  have measured := family.toKernel.measurable @measurable threshold
  have equal : (fun seed => family.toKernel seed region) =
      (fun seed => (random seed).val region) :=
    funext (fun seed => congrArg (fun measure : Measure space.toMeasurable => measure region)
      (family.toKernel_apply seed))
  rw [equal] at measured
  exact measured

/-- Constructs a measurable transition kernel from a morphism into the law object. -/
@[expose] noncomputable def toKernel {domain codomain : Space realSource}
    (morphism : Hom domain (object codomain)) : Kernel domain.toMeasurable codomain.toMeasurable where
  toFun := fun point => (morphism point).val
  measurable := by
    intro region measurable
    exact ENNRealMeasurable.comp (evaluation_measurable codomain @measurable) morphism.toMeasurable

/-- Proves that the induced kernel evaluates to the morphism result at each point. -/
@[simp] theorem toKernel_apply {domain codomain : Space realSource}
    (morphism : Hom domain (object codomain)) (point : domain.Carrier) :
    toKernel morphism point = (morphism point).val := rfl

/-- Proves that precomposition with any accepted real random element yields an s-finite kernel. -/
@[expose] noncomputable def toKernel_precomp_sfinite {domain codomain : Space realSource}
    (morphism : Hom domain (object codomain))
    {random : Carrier → domain.Carrier} (accepted : domain.Random random) :
    Kernel.IsSFinite ((toKernel morphism).precomp random (Space.random_measurable accepted)) := by
  let family := Classical.choice (morphism.mapRandom accepted)
  have equal : family.toKernel =
      (toKernel morphism).precomp random (Space.random_measurable accepted) := by
    apply Kernel.ext
    intro seed
    exact family.toKernel_apply seed
  exact equal ▸ family.toKernel_sfinite

end

end Foundations.QuasiBorel.SFinite
