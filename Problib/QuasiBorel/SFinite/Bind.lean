module

public import Problib.QuasiBorel.SFinite.Unit
public import Problib.Measure.Kernel.Composition
public import Problib.Measure.Kernel.Composition.Bind.Transport

set_option autoImplicit false

/-!
# Monadic bind for s-finite quasi-Borel spaces

This module defines the monadic bind operation on s-finite quasi-Borel spaces.
The continuation is extended by the zero law on failure, inducing an accepted
real random continuation family.
Kernel composition and s-finite source transport yield a concrete presentation
of the bound law without requiring global s-finite certificates on arbitrary
QBS spaces.
-/
namespace Problib.QuasiBorel.SFinite

public section

open Problib.Measure hiding Space
open Problib.Measure.Real (Carrier borel)

universe u v w

variable {domain codomain : Space realSource}

/-- Extends a morphism from a domain into laws to the failure sum by assigning the zero law on failure. -/
@[expose] noncomputable def zeroExtend (kernel : Hom domain (object codomain)) :
    Hom (withFailure domain) (object codomain) :=
  Space.copair (Hom.constant (Space.terminal realSource) (object codomain) (zero codomain)) kernel

/-- Proves that the zero extension evaluates to the zero law on the failure summand. -/
@[simp] theorem zeroExtend_failure (kernel : Hom domain (object codomain)) (failure : Unit) :
    zeroExtend kernel (Sum.inl failure) = zero codomain := rfl

/-- Proves that the zero extension agrees with the original morphism on the success summand. -/
@[simp] theorem zeroExtend_success (kernel : Hom domain (object codomain)) (point : domain.Carrier) :
    zeroExtend kernel (Sum.inr point) = kernel point := rfl

/-- Proves that precomposing the zero extension kernel with the right injection recovers the domain kernel. -/
theorem toKernel_zeroExtend_precomp (kernel : Hom domain (object codomain)) :
    (toKernel (zeroExtend kernel)).precomp
      (Space.inrEmbedding (Space.terminal realSource) domain).function
      (Space.inrEmbedding (Space.terminal realSource) domain).measurable = toKernel kernel := by
  apply Kernel.ext
  intro point
  rfl

/-- Relates pullback bind against the domain kernel to ambient bind against the zero extension kernel. -/
theorem bind_comap_zeroExtend (measure : Measure (withFailure domain).toMeasurable)
    (kernel : Hom domain (object codomain)) :
    (measure.comap (Space.inrEmbedding (Space.terminal realSource) domain)).bind (toKernel kernel) =
      measure.bind (toKernel (zeroExtend kernel)) := by
  have law := Measure.bind_comap_of_zero_outside measure
    (Space.inrEmbedding (Space.terminal realSource) domain) (toKernel (zeroExtend kernel)) (by
      intro input outside
      cases input with
      | inl _ => rfl
      | inr point => exact False.elim (outside ⟨point, rfl⟩))
  rw [toKernel_zeroExtend_precomp] at law
  exact law

/-- Proves presentation transport for bind along an accepted random family. -/
theorem bind_representation (kernel : Hom domain (object codomain))
    {random : Carrier → (withFailure domain).Carrier} (accepted : (withFailure domain).Random random)
    (family : Family codomain (fun seed => zeroExtend kernel (random seed))) (measure : Measure borel) :
    ((measure.bind family.kernel).map family.random
      (Space.random_measurable family.accepted)).comap
        (Space.inrEmbedding (Space.terminal realSource) codomain) =
      ((measure.map random (Space.random_measurable accepted)).comap
        (Space.inrEmbedding (Space.terminal realSource) domain)).bind (toKernel kernel) := by
  have equal : family.toKernel =
      (toKernel (zeroExtend kernel)).precomp random (Space.random_measurable accepted) := by
    apply Kernel.ext
    intro seed
    exact family.toKernel_apply seed
  calc
    ((measure.bind family.kernel).map family.random
        (Space.random_measurable family.accepted)).comap
          (Space.inrEmbedding (Space.terminal realSource) codomain) =
        measure.bind family.toKernel := by
      rw [Measure.map_bind, Measure.comap_bind]
      rfl
    _ = measure.bind
        ((toKernel (zeroExtend kernel)).precomp random (Space.random_measurable accepted)) :=
      congrArg (fun current => measure.bind current) equal
    _ = (measure.map random (Space.random_measurable accepted)).bind
        (toKernel (zeroExtend kernel)) :=
      (Measure.bind_map measure random (Space.random_measurable accepted) _).symm
    _ = _ := (bind_comap_zeroExtend _ kernel).symm

/-- Monadic bind producing a represented law from an input law and a law-valued morphism. -/
@[expose] noncomputable def bind (law : Law domain)
    (kernel : Hom domain (object codomain)) : Law codomain := by
  let family := Classical.choice ((zeroExtend kernel).map_random law.presentation.accepted)
  refine ⟨law.val.bind (toKernel kernel), ?_⟩
  refine ⟨{
    random := family.random
    accepted := family.accepted
    sourceMeasure := law.presentation.sourceMeasure.bind family.kernel
    sfinite := law.presentation.sfinite.bind family.sfinite
  }, ?_⟩
  change ((law.presentation.sourceMeasure.bind family.kernel).map family.random
    (Space.random_measurable family.accepted)).comap
      (Space.inrEmbedding (Space.terminal realSource) codomain) = _
  rw [bind_representation kernel law.presentation.accepted family]
  change law.presentation.toMeasure.bind (toKernel kernel) = _
  rw [law.presentation_toMeasure]

/-- Proves that the bound law evaluates to the measure bind against the induced kernel. -/
@[simp] theorem bind_val (law : Law domain) (kernel : Hom domain (object codomain)) :
    (bind law kernel).val = law.val.bind (toKernel kernel) := rfl

/-- Expresses the bound law directly through the source measure and precomposed continuation kernel. -/
theorem bind_source (law : Law domain) (kernel : Hom domain (object codomain)) :
    (bind law kernel).val = law.presentation.sourceMeasure.bind
      ((toKernel (zeroExtend kernel)).precomp law.presentation.random
        (Space.random_measurable law.presentation.accepted)) := by
  rw [bind_val, ← law.presentation_toMeasure]
  change ((law.presentation.sourceMeasure.map law.presentation.random
    (Space.random_measurable law.presentation.accepted)).comap
      (Space.inrEmbedding (Space.terminal realSource) domain)).bind (toKernel kernel) = _
  rw [bind_comap_zeroExtend, Measure.bind_map]

/-- Binds an accepted parameterized family of laws against a law-valued morphism. -/
@[expose] noncomputable def Family.bind {laws : Carrier → Law domain}
    (family : Family domain laws) (kernel : Hom domain (object codomain)) :
    Family codomain (fun seed => bind (laws seed) kernel) := by
  let continuation := Classical.choice ((zeroExtend kernel).map_random family.accepted)
  refine {
    random := continuation.random
    accepted := continuation.accepted
    kernel := family.kernel.comp continuation.kernel
    sfinite := family.sfinite.comp continuation.sfinite
    law := ?_
  }
  intro seed
  change (((family.kernel seed).bind continuation.kernel).map continuation.random
    (Space.random_measurable continuation.accepted)).comap
      (Space.inrEmbedding (Space.terminal realSource) codomain) = _
  rw [bind_representation kernel family.accepted continuation, family.law seed]
  rfl

/-- Kleisli extension lifting a law-valued morphism to a morphism between law objects. -/
@[expose] noncomputable def extend (kernel : Hom domain (object codomain)) :
    Hom (object domain) (object codomain) where
  toFun := fun law => bind law kernel
  map_random := by
    intro random accepted
    exact ⟨(Classical.choice accepted).bind kernel⟩

/-- Proves that the kernel induced by composed Kleisli extensions is the composition of induced kernels. -/
theorem toKernel_extend_comp {result : Space realSource}
    (first : Hom domain (object codomain)) (second : Hom codomain (object result)) :
    toKernel (Hom.comp (extend second) first) = (toKernel first).comp (toKernel second) := by
  apply Kernel.ext
  intro point
  rfl

end

end Problib.QuasiBorel.SFinite
