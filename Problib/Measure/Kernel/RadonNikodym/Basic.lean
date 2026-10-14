module

public import Problib.Measure.Decomposition.RadonNikodym.Basic
public import Problib.Measure.Kernel.Density.Basic
public import Problib.Measure.Integral.Density.Change
public import Problib.Measure.Integral.Density.Algebra
import Problib.Measure.Extended.Algebra.Binary

set_option autoImplicit false

/-!
# Kernel Radon-Nikodym derivatives: core interface

Packages jointly measurable Radon-Nikodym densities between transition kernels
alongside exact whole-measure reconstruction at every source input.
Supplies fiber certificates, kernel equality through `withDensity`, exact
integral reconstruction, ordinary almost-everywhere uniqueness under sigma-finite
reference fibers, constant certificates, identity, and transitive reweighting.
-/

namespace Problib.Measure.Kernel

open Problib.Real

universe u v

variable {α : Type u} {β : Type v} {source : Space α} {target : Space β}

/-- Radon-Nikodym derivative certificate between two transition kernels.
Packages a jointly measurable density and exact whole-measure reconstruction
at every source input point. -/
public structure RadonNikodymDerivative (kernel reference : Kernel source target) where
  density : α → β → ENNReal
  density_measurable : ENNRealMeasurable (Space.product source target)
    (fun pair => density pair.1 pair.2)
  reconstruct : ∀ input, Measure.IsDensity (kernel input) (reference input) (density input)

namespace RadonNikodymDerivative

variable {kernel middle reference : Kernel source target}

/-- Pointwise single-measure Radon-Nikodym derivative certificate at a source input. -/
@[expose] public def fiber (derivative : RadonNikodymDerivative kernel reference) (input : α) :
    Measure.RadonNikodymDerivative (kernel input) (reference input) where
  density := derivative.density input
  density_measurable := jointly_measurable_slice derivative.density_measurable input
  reconstruct := derivative.reconstruct input

/-- Whole-kernel reconstruction via density weighting for an s-finite reference kernel. -/
public theorem reconstruct_eq (derivative : RadonNikodymDerivative kernel reference)
    (referenceFinite : IsSFinite reference) :
    kernel = reference.withDensity referenceFinite derivative.density
      derivative.density_measurable := by
  apply Kernel.ext
  exact derivative.reconstruct

/-- Fiberwise absolute continuity implied by the kernel derivative certificate. -/
public theorem absolutelyContinuous (derivative : RadonNikodymDerivative kernel reference)
    (input : α) : Measure.AbsolutelyContinuous (kernel input) (reference input) :=
  (derivative.fiber input).absolutelyContinuous

/-- Exact integral reconstruction for measurable integrands along each source fiber. -/
public theorem lintegral_eq (derivative : RadonNikodymDerivative kernel reference)
    (input : α) {integrand : β → ENNReal}
    (measurable : ENNRealMeasurable target integrand) :
    lintegral (kernel input) integrand = lintegral (reference input)
      (fun output => ENNReal.mul (derivative.density input output) (integrand output)) := by
  rw [(derivative.fiber input).reconstruct_eq]
  exact lintegral_withDensity _ (derivative.fiber input).density_measurable measurable

/-- Uniqueness of kernel densities almost everywhere under sigma-finite reference fibers. -/
public theorem density_aeEq (left right : RadonNikodymDerivative kernel reference)
    (finite : ∀ input, Measure.SigmaFinite (reference input)) (input : α) :
    (reference input).AEEq (left.density input) (right.density input) :=
  (left.fiber input).density_aeEq (right.fiber input) (finite input)

/-- Constant kernel derivative induced by a single-measure Radon-Nikodym certificate. -/
@[expose] public noncomputable def const {measure base : Measure target}
    (derivative : Measure.RadonNikodymDerivative measure base) (source : Space α) :
    RadonNikodymDerivative (Kernel.const source measure) (Kernel.const source base) where
  density := fun _ => derivative.density
  density_measurable := derivative.density_measurable.comp (Space.second_measurable source target)
  reconstruct := fun _ => derivative.reconstruct

/-- Identity kernel Radon-Nikodym certificate with constant unit density. -/
@[expose] public noncomputable def identity (kernel : Kernel source target) :
    RadonNikodymDerivative kernel kernel where
  density := fun _ _ => ENNReal.one
  density_measurable := ENNRealMeasurable.constant _ _
  reconstruct := fun input => (kernel input).withDensity_one.symm

/-- Transitive composition of kernel Radon-Nikodym certificates multiplying
the second density by the first with no finiteness premises. -/
@[expose] public noncomputable def trans (first : RadonNikodymDerivative kernel middle)
    (second : RadonNikodymDerivative middle reference) :
    RadonNikodymDerivative kernel reference where
  density := fun input output => ENNReal.mul (second.density input output)
    (first.density input output)
  density_measurable := second.density_measurable.mul first.density_measurable
  reconstruct := by
    intro input
    change kernel input = (reference input).withDensity _
    calc
      kernel input = (middle input).withDensity (first.density input) := first.reconstruct input
      _ = ((reference input).withDensity (second.density input)).withDensity
          (first.density input) :=
        congrArg (fun measure : Measure target => measure.withDensity (first.density input))
          (second.reconstruct input)
      _ = (reference input).withDensity _ :=
        Measure.withDensity_withDensity _ (second.fiber input).density_measurable
          (first.fiber input).density_measurable

end RadonNikodymDerivative

end Problib.Measure.Kernel
