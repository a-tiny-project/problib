module

public import Foundations.Measure.Kernel.RadonNikodym.Basic
public import Foundations.Measure.Kernel.Hahn.Countable
public import Foundations.Measure.Kernel.Scale
public import Foundations.Measure.Decomposition.RadonNikodym.Finite
import Foundations.Measure.Decomposition.Hahn.Density
import Foundations.Measure.Decomposition.Hahn.Levels

set_option autoImplicit false

/-!
# Finite-fiber kernel Radon-Nikodym derivatives

Constructs a jointly measurable Radon-Nikodym derivative for kernels with finite
fibers targeting a countably generated space, using rational Hahn level sets.
-/

namespace Foundations.Measure.Kernel.RadonNikodymDerivative

open Foundations.Real

universe u v

variable {α : Type u} {β : Type v} {source : Space α} {target : Space β}
  {kernel reference : Kernel source target}

/-- Constructs a jointly measurable Radon-Nikodym derivative for kernels with
finite fibers targeting a countably generated space under ordinary absolute continuity.
Rational Hahn level sets assemble into a joint density without uniform mass bounds. -/
public noncomputable def ofFiniteFibers (generator : Space.CountableGenerator target)
    (kernelFinite : ∀ input, Measure.IsFinite (kernel input))
    (referenceFinite : ∀ input, Measure.IsFinite (reference input))
    (continuous : ∀ input, Measure.AbsolutelyContinuous (kernel input) (reference input)) :
    RadonNikodymDerivative kernel reference := by
  let decompositions : ∀ index, HahnDecomposition kernel (Kernel.smul (ENNReal.rationalBasis index) reference) :=
    fun index => HahnDecomposition.ofCountableGenerator generator kernelFinite
      (fun input => (referenceFinite input).smul (ENNReal.rationalBasis index) (ENNReal.rationalBasisFinite index))
  let density : α → β → ENNReal := fun input =>
    Measure.Hahn.levelDensity (fun index => (decompositions index).region input)
  have measurable : ENNRealMeasurable (Space.product source target)
      (fun pair => density pair.1 pair.2) :=
    Measure.Hahn.levelDensity_measurable
      (fun index (pair : α × β) => (decompositions index).region pair.1 pair.2)
      (fun index => (decompositions index).measurable)
  refine { density := density, densityMeasurable := measurable, reconstruct := ?_ }
  intro input
  let derivative := Measure.RadonNikodymDerivative.ofFinite (kernelFinite input)
    (referenceFinite input) (continuous input)
  have bounds (index : Nat) : (reference input).AE (fun value =>
      ((decompositions index).region input value →
        ENNReal.le (ENNReal.rationalBasis index) (derivative.density value)) ∧
      (¬(decompositions index).region input value →
        ENNReal.le (derivative.density value) (ENNReal.rationalBasis index))) := by
    let constant : Measure.RadonNikodymDerivative
        (Measure.smul (ENNReal.rationalBasis index) (reference input)) (reference input) := {
      density := fun _ => ENNReal.rationalBasis index
      densityMeasurable := ENNRealMeasurable.constant target _
      reconstruct := (reference input).withDensity_const (ENNReal.rationalBasis index) |>.symm }
    exact ((decompositions index).fiber input).ae_density_bounds derivative constant (referenceFinite input)
  have equal : (reference input).AEEq (density input) derivative.density :=
    Measure.Hahn.ae_levelDensity_eq (reference input)
      (fun index => (decompositions index).region input) derivative.density bounds
  exact derivative.reconstruct_eq.trans (Measure.withDensity_congr_ae equal.symm)

end Foundations.Measure.Kernel.RadonNikodymDerivative
