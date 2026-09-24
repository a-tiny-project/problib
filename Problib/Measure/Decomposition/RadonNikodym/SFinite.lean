module

public import Problib.Measure.Decomposition.RadonNikodym.Finite
public import Problib.Measure.Extended.Limit

set_option autoImplicit false

/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying

Adapted from Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Decomposition along a disjoint finite reference cover and summation across
finite target components guide the construction.
-/

namespace Problib.Measure.Measure.RadonNikodymDerivative

open Problib.Real

universe u

variable {alpha : Type u} {space : Space alpha}

/-- Constructs a Radon-Nikodym derivative for a finite target and a
sigma-finite reference.

The construction requires ordinary absolute continuity of the target with
respect to the reference.

The proof glues finite derivatives along a disjoint finite cover of the
reference measure. -/
private noncomputable def ofFiniteCover {target reference : Measure space}
    (targetFinite : IsFinite target) (referenceFinite : SigmaFinite reference)
    (continuous : AbsolutelyContinuous target reference) :
    RadonNikodymDerivative target reference := by
  let cover := referenceFinite.disjointCover
  let derivatives := fun index => RadonNikodymDerivative.ofFinite
    (targetFinite.restrict (cover.sets index)) (cover.toFiniteCover.restrict_finite index)
    (continuous.restrict (cover.sets index))
  let densities := fun index => ennrealIndicator (cover.sets index) (derivatives index).density
  have measurable : ∀ index, ENNRealMeasurable space (densities index) :=
    fun index => ENNRealMeasurable.indicator (cover.measurable index)
      (derivatives index).density_measurable
  refine {
    density := fun value => ENNReal.tsum (fun index => densities index value)
    density_measurable := ENNRealMeasurable.tsum measurable
    reconstruct := ?_
  }
  change target = reference.withDensity (fun value => ENNReal.tsum (fun index => densities index value))
  rw [reference.withDensity_tsum densities measurable]
  have pieces : ∀ index, reference.withDensity (densities index) =
      target.restrict (cover.sets index) := by
    intro index
    change reference.withDensity
      (ennrealIndicator (cover.sets index) (derivatives index).density) = _
    rw [reference.withDensity_indicator _ (cover.measurable index)]
    exact (derivatives index).reconstruct_eq.symm
  calc
    target = target.restrict Set.univ := target.restrict_univ.symm
    _ = target.restrict (Set.iUnion cover.sets) := by rw [cover.cover]
    _ = Measure.sum (fun index => target.restrict (cover.sets index)) :=
      target.restrict_iUnion cover.sets cover.measurable cover.pairwise
    _ = Measure.sum (fun index => reference.withDensity (densities index)) :=
      congrArg Measure.sum (funext (fun index => (pieces index).symm))

/-- Constructs a Radon-Nikodym derivative for an s-finite target and a
sigma-finite reference.

The construction requires ordinary absolute continuity of the target with
respect to the reference.

The proof sums derivatives across finite target components. The space
needs no standard-Borel or countability structure. The density can take the
value infinity. -/
public noncomputable def ofSFinite {target reference : Measure space}
    (targetFinite : SFinite target) (referenceFinite : SigmaFinite reference)
    (continuous : AbsolutelyContinuous target reference) :
    RadonNikodymDerivative target reference := by
  have componentContinuous : ∀ index, AbsolutelyContinuous (targetFinite.components index) reference := by
    intro index
    apply continuous.of_le
    intro set _
    have included := Measure.le_sum targetFinite.components index set
    rw [targetFinite.sum_eq] at included
    exact included
  let derivatives := fun index => ofFiniteCover
    (targetFinite.finite index) referenceFinite (componentContinuous index)
  refine {
    density := fun value => ENNReal.tsum (fun index => (derivatives index).density value)
    density_measurable := ENNRealMeasurable.tsum (fun index => (derivatives index).density_measurable)
    reconstruct := ?_
  }
  change target = reference.withDensity
    (fun value => ENNReal.tsum (fun index => (derivatives index).density value))
  rw [reference.withDensity_tsum _ (fun index => (derivatives index).density_measurable)]
  calc
    target = Measure.sum targetFinite.components := targetFinite.sum_eq.symm
    _ = Measure.sum (fun index => reference.withDensity (derivatives index).density) :=
      congrArg Measure.sum (funext (fun index => (derivatives index).reconstruct_eq))

end Problib.Measure.Measure.RadonNikodymDerivative
