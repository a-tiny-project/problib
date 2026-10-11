module

public import Problib.Measure.Kernel.RadonNikodym.Basic
public import Problib.Measure.Kernel.Product.Finite
import Problib.Measure.Kernel.Product.Density
import Problib.Measure.Kernel.Product.Transport
import Problib.Measure.Extended.Algebra.Binary

set_option autoImplicit false

/-!
# Densities of independent products

When each lane of a finite product has a density against its own reference,
the product has a density against the product of the references: the lanes'
densities multiplied together, each read at its own coordinate. This is the
density of a vector of independent draws, such as a vectorized program's.

`Measure.prod_withDensity` is the two-lane fact, read off
`semiproduct_withDensity_prod` with a constant kernel.
`finProductDensity` multiplies lane densities in lane order, lane `0` first,
and `finProduct_withDensity` folds the two-lane fact over `Kernel.finProduct`.
`RadonNikodymDerivative.finProduct` packages it as a kernel certificate.
-/

namespace Problib.Measure

open Problib.Real

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

public section

namespace Measure

/-- Densities on both factors multiply on the product: the right density is
read at the second coordinate and the left at the first. -/
theorem prod_withDensity {first : Space α} {second : Space β} (left : Measure first)
    (right : Measure second) (rightFinite : SFinite right) {leftDensity : α → ENNReal}
    {rightDensity : β → ENNReal} (leftMeasurable : ENNRealMeasurable first leftDensity)
    (rightMeasurable : ENNRealMeasurable second rightDensity)
    (weightedFinite : SFinite (right.withDensity rightDensity)) :
    Measure.prod (left.withDensity leftDensity) (right.withDensity rightDensity) weightedFinite =
      (Measure.prod left right rightFinite).withDensity
        (fun pair => ENNReal.mul (rightDensity pair.2) (leftDensity pair.1)) :=
  semiproduct_withDensity_prod left leftMeasurable right rightFinite
    (Kernel.const first (right.withDensity rightDensity))
    (Kernel.IsSFinite.const first weightedFinite)
    (kernelDensity := fun pair => rightDensity pair.2)
    (rightMeasurable.comp (Space.second_measurable first second)) (fun _ => rfl)

end Measure

namespace Kernel

variable {source : Space α} {target : Space β}

/-- The product of one density per lane at a tuple: lane `0`'s density at its
coordinate, times the product over the remaining lanes. -/
@[expose] noncomputable def finProductDensity : (extent : Nat) → (Fin extent → α → β → ENNReal) → α →
    (Fin extent → β) → ENNReal
  | 0, _, _, _ => ENNReal.one
  | extent + 1, density, input, point =>
      ENNReal.mul (density 0 input (point 0))
        (finProductDensity extent (fun lane => density lane.succ) input fun lane => point lane.succ)

/-- A product of jointly measurable lane densities is jointly measurable. -/
theorem finProductDensity_measurable : (extent : Nat) → {density : Fin extent → α → β → ENNReal} →
    (∀ lane, ENNRealMeasurable (Space.product source target)
      (fun pair => density lane pair.1 pair.2)) →
    ENNRealMeasurable (Space.product source (Space.pi fun _ : Fin extent => target))
      (fun pair => finProductDensity extent density pair.1 pair.2)
  | 0, _, _ => ENNRealMeasurable.constant _ _
  | extent + 1, density, measurable => by
      have head : MeasurableMap (Space.product source (Space.pi fun _ : Fin (extent + 1) => target))
          (Space.product source target) (fun pair => (pair.1, pair.2 0)) :=
        Space.pair_measurable (Space.first_measurable _ _)
          (MeasurableMap.comp (Space.coordinate_measurable (fun _ : Fin (extent + 1) => target) 0)
            (Space.second_measurable _ _))
      have tail : MeasurableMap (Space.product source (Space.pi fun _ : Fin (extent + 1) => target))
          (Space.product source (Space.pi fun _ : Fin extent => target))
          (fun pair => (pair.1, fun lane => pair.2 lane.succ)) :=
        Space.pair_measurable (Space.first_measurable _ _)
          (Space.pi_measurable fun lane : Fin extent =>
            MeasurableMap.comp
              (Space.coordinate_measurable (fun _ : Fin (extent + 1) => target) lane.succ)
              (Space.second_measurable _ _))
      exact ENNRealMeasurable.mul ((measurable 0).comp head)
        ((finProductDensity_measurable extent fun lane => measurable lane.succ).comp tail)

/-- A finite product of kernels with densities has the product density against
the product of the references. -/
theorem finProduct_withDensity : (extent : Nat) → (family reference : Fin extent → Kernel source target) →
    (familyFinite : ∀ lane, IsSFinite (family lane)) →
    (referenceFinite : ∀ lane, IsSFinite (reference lane)) →
    (derivative : ∀ lane, RadonNikodymDerivative (family lane) (reference lane)) → (input : α) →
    finProduct extent family familyFinite input =
      (finProduct extent reference referenceFinite input).withDensity
        (finProductDensity extent (fun lane => (derivative lane).density) input)
  | 0, family, reference, familyFinite, referenceFinite, _, input => by
      rw [finProduct_dirac 0 family familyFinite (values := fun lane => lane.elim0)
          fun lane => lane.elim0,
        finProduct_dirac 0 reference referenceFinite (values := fun lane => lane.elim0)
          fun lane => lane.elim0]
      exact (Measure.withDensity_one _).symm
  | extent + 1, family, reference, familyFinite, referenceFinite, derivative, input => by
      rw [finProduct_succ_apply, finProduct_succ_apply]
      have rest := finProduct_withDensity extent (fun lane => family lane.succ)
        (fun lane => reference lane.succ) (fun lane => familyFinite lane.succ)
        (fun lane => referenceFinite lane.succ) (fun lane => derivative lane.succ) input
      have restFinite := rest ▸
        (IsSFinite.finProduct extent _ fun lane => familyFinite lane.succ).measure input
      have headDensity : family 0 input = (reference 0 input).withDensity
          ((derivative 0).density input) := (derivative 0).reconstruct input
      rw [Measure.prod_congr_right _ _ restFinite rest, headDensity,
        Measure.prod_withDensity _ _
          ((IsSFinite.finProduct extent _ fun lane => referenceFinite lane.succ).measure input)
          (leftDensity := (derivative 0).density input)
          (jointly_measurable_slice (derivative 0).density_measurable input)
          (jointly_measurable_slice (finProductDensity_measurable extent
            fun lane => (derivative lane.succ).density_measurable) input) restFinite,
        ← Measure.map_withDensity _ _ _ (jointly_measurable_slice (finProductDensity_measurable
          (extent + 1) fun lane => (derivative lane).density_measurable) input)]
      congr 2
      funext pair
      exact ENNReal.mul_comm _ _

/-- The product of lane certificates is a certificate for the product, with
the lanes' densities multiplied. -/
@[expose] noncomputable def RadonNikodymDerivative.finProduct (extent : Nat)
    {family reference : Fin extent → Kernel source target}
    (familyFinite : ∀ lane, IsSFinite (family lane))
    (referenceFinite : ∀ lane, IsSFinite (reference lane))
    (derivative : ∀ lane, RadonNikodymDerivative (family lane) (reference lane)) :
    RadonNikodymDerivative (Kernel.finProduct extent family familyFinite)
      (Kernel.finProduct extent reference referenceFinite) where
  density := finProductDensity extent fun lane => (derivative lane).density
  density_measurable := finProductDensity_measurable extent fun lane =>
    (derivative lane).density_measurable
  reconstruct := finProduct_withDensity extent family reference familyFinite referenceFinite
    derivative

/-- A derivative pushed forward along a map with a measurable left inverse:
the density at an image point is the density at the point it came from. -/
@[expose] noncomputable def RadonNikodymDerivative.map {image : Space γ}
    {kernel reference : Kernel source target}
    (derivative : RadonNikodymDerivative kernel reference) (function : β → γ)
    (measurable : MeasurableMap target image function) (inverse : γ → β)
    (inverseMeasurable : MeasurableMap image target inverse)
    (left : ∀ value, inverse (function value) = value) :
    RadonNikodymDerivative (kernel.map function measurable) (reference.map function measurable) :=
  have pulledMeasurable : ENNRealMeasurable (Space.product source image)
      (fun pair => derivative.density pair.1 (inverse pair.2)) :=
    ENNRealMeasurable.comp (map := fun pair => derivative.density pair.1 pair.2)
      derivative.density_measurable
      (Space.product_map (MeasurableMap.identity source) inverseMeasurable)
  { density := fun input point => derivative.density input (inverse point)
    density_measurable := pulledMeasurable
    reconstruct := fun input => by
      change (kernel input).map function measurable =
        ((reference input).map function measurable).withDensity _
      have pulled : (fun value => derivative.density input (inverse (function value))) =
          derivative.density input := funext fun value => by rw [left]
      rw [← Measure.map_withDensity _ _ measurable
          (density := fun point => derivative.density input (inverse point))
          (jointly_measurable_slice
            (density := fun input point => derivative.density input (inverse point))
            pulledMeasurable input), pulled]
      exact congrArg (fun measure : Measure target => measure.map function measurable)
        (derivative.reconstruct input) }

end Kernel

end

end Problib.Measure
