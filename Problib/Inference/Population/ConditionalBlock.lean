module

public import Problib.Inference.Population.Conditional
public import Problib.Measure.Normalization
import Problib.Measure.Additive.Algebra
import Problib.Measure.Integral.Density.Change
import Problib.Measure.Integral.Lebesgue.Algebra
import Problib.Measure.Integral.Lebesgue.Measure
import Problib.Measure.Kernel.Product

set_option autoImplicit false

/-! # The conditional exact block

An exact block at a path `x` has a finite measure `block x` on its values. Its
unconditional step extends each lane's path by a draw from the normalized block
(`sampler`) and multiplies the lane's weight by the block's mass at the path
(`mass`). At zero mass the sampler may be any law, since the weight it carries
is zero.

That step is a propagation on paths, so its conditional form is lane C's
`conditional_propagate_path`. The conditional step keeps the retained lane's
value, pinned at the marked lane, and draws every other lane from the
normalized block with the block's mass as its increment. Its target is the
source's semiproduct with the block itself (`pathTarget_block`), so the
conditional population is a conditional law for the exact target
(`conditional_block`). From one empty lane per particle, the block alone has a
conditional law for its own measure (`conditional_block_empty`), and particle
Gibbs keeps that target whenever the conditional kernel is Markov
(`particleGibbs_invariant`).

A retained value is pinned whatever it is. No part of the step depends on
whether the value lies in some distinguished subset of the block, which is
where a compiled proposal with a "none of these" option loses it. -/

namespace Problib.Inference

open Problib.Real Problib.Measure

public section

variable {α : Type} {β : Type} {space : Space α} {result : Space β}

/-- The block at a path is its mass times the sampler's law. At zero mass the
block is zero, and elsewhere the sampler is the normalized block. -/
theorem block_eq_smul_sampler {block sampler : Measure result} (mass : NNReal)
    (total : block Set.univ = ENNReal.finite mass)
    (conditional : ∀ nonzero : mass ≠ NNReal.zero,
      sampler = Measure.normalize block (Measure.IsNormalizable.of_finite_mass total nonzero)) :
    Measure.smul (ENNReal.finite mass) sampler = block := by
  by_cases zero : mass = NNReal.zero
  · have blockZero := (Measure.eq_zero_iff_univ_eq_zero block).mpr
      (total.trans (congrArg ENNReal.finite zero))
    rw [zero, blockZero]
    exact Measure.zero_smul sampler
  · rw [conditional zero, ← total]
    exact Measure.smul_normalize _ _

/-- The mass of the block at a path's prefix, as an increment on the extended
path. -/
theorem block_increment_measurable {mass : α → NNReal}
    (massMeasurable : MeasurableMap space weightSpace mass) :
    MeasurableMap (Space.product space result) weightSpace (fun pair => mass pair.1) :=
  MeasurableMap.comp massMeasurable (Space.first_measurable space result)

/-- Extending paths by the normalized block and weighing them by its mass gives
the source's semiproduct with the block. -/
theorem pathTarget_block (source : Measure space) (block sampler : Kernel space result)
    (blockFinite : Kernel.IsSFinite block) (samplerFinite : Kernel.IsSFinite sampler)
    (mass : α → NNReal) (massMeasurable : MeasurableMap space weightSpace mass)
    (total : ∀ input, block input Set.univ = ENNReal.finite (mass input))
    (conditional : ∀ input, ∀ nonzero : mass input ≠ NNReal.zero,
      sampler input = Measure.normalize (block input)
        (Measure.IsNormalizable.of_finite_mass (total input) nonzero)) :
    pathTarget source sampler samplerFinite (fun pair => mass pair.1) =
      source.semiproduct block blockFinite := by
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  have weight := finite_weight_measurable (block_increment_measurable (result := result)
    massMeasurable)
  rw [pathTarget, lintegral_withDensity _ weight measurable,
    lintegral_semiproduct _ _ _ (ENNRealMeasurable.mul weight measurable),
    lintegral_semiproduct _ _ _ measurable]
  refine lintegral_congr _ fun input => ?_
  have section_ := measurable.comp (Kernel.pair_left_measurable (source := space) input)
  rw [lintegral_smul (sampler input) (ENNReal.finite (mass input)) section_,
    ← block_eq_smul_sampler (mass input) (total input) (conditional input),
    lintegral_smul_measure]

/-- The conditional exact block. Propagating paths by the normalized block,
weighed by its mass, is a conditional step onto the source's semiproduct with
the block. Its lift keeps the retained path at the marked lane and draws every
other lane from the normalized block. -/
theorem conditional_block (extent : Nat) (source : Measure space)
    (block sampler : Kernel space result)
    (blockFinite : Kernel.IsSFinite block) (samplerFinite : Kernel.IsSFinite sampler)
    (mass : α → NNReal) (massMeasurable : MeasurableMap space weightSpace mass)
    (total : ∀ input, block input Set.univ = ENNReal.finite (mass input))
    (conditional : ∀ input, ∀ nonzero : mass input ≠ NNReal.zero,
      sampler input = Measure.normalize (block input)
        (Measure.IsNormalizable.of_finite_mass (total input) nonzero)) :
    ConditionalStep (Lanes.fin (extent + 1)) (Lanes.fin (extent + 1)) source
      (source.semiproduct block blockFinite)
      (propagate extent (sampler.attach samplerFinite) (Kernel.IsSFinite.attach samplerFinite)
        (fun pair => mass pair.2.1)
        (MeasurableMap.comp (block_increment_measurable massMeasurable)
          (Space.second_measurable _ _)))
      (fun conditional finite => propagateConditional extent (sampler.attach samplerFinite)
        (Kernel.IsSFinite.attach samplerFinite) (fun pair => mass pair.2.1)
        (MeasurableMap.comp (block_increment_measurable massMeasurable)
          (Space.second_measurable _ _)) conditional finite
        Prod.fst (Space.first_measurable space result)) := by
  rw [← pathTarget_block source block sampler blockFinite samplerFinite mass massMeasurable total
    conditional]
  exact conditional_propagate_path extent source sampler samplerFinite
    (block_increment_measurable massMeasurable)

/-- The block's population from empty lanes: every lane draws from the
normalized block at the one point and carries the block's mass. -/
@[expose] noncomputable def blockPopulation (extent : Nat) (sampler : Measure result)
    (samplerFinite : Measure.SFinite sampler) (mass : NNReal) :
    Measure (populationSpace (Fin (extent + 1)) (Space.product (Space.discrete Unit) result)) :=
  (Measure.dirac (populationSpace (Fin (extent + 1)) (Space.discrete Unit))
      (emptyPopulation extent)).bind
    (propagate extent ((Kernel.const (Space.discrete Unit) sampler).attach
        (Kernel.IsSFinite.const _ samplerFinite))
      (Kernel.IsSFinite.attach (Kernel.IsSFinite.const _ samplerFinite))
      (fun _ => mass) (MeasurableMap.constant _ _ mass))

/-- The block's conditional law from empty lanes: at a retained value, the
marked lane holds it and every other lane draws from the normalized block. -/
@[expose] noncomputable def blockConditional (extent : Nat) (sampler : Measure result)
    (samplerFinite : Measure.SFinite sampler) (mass : NNReal) :
    Kernel (Space.product (Space.discrete Unit) result)
      (markedSpace (Fin (extent + 1)) (Space.product (Space.discrete Unit) result)) :=
  propagateConditional extent ((Kernel.const (Space.discrete Unit) sampler).attach
      (Kernel.IsSFinite.const _ samplerFinite))
    (Kernel.IsSFinite.attach (Kernel.IsSFinite.const _ samplerFinite))
    (fun _ => mass) (MeasurableMap.constant _ _ mass) (emptyConditional extent)
    (emptyConditionalFinite extent) Prod.fst (Space.first_measurable _ result)

/-- One exact block from empty lanes has a conditional law for the block. The
target is the block on the paths `((), value)`. -/
theorem conditional_block_empty (extent : Nat) (block sampler : Measure result)
    (blockFinite : Measure.SFinite block) (samplerFinite : Measure.SFinite sampler)
    (mass : NNReal) (total : block Set.univ = ENNReal.finite mass)
    (conditional : ∀ nonzero : mass ≠ NNReal.zero,
      sampler = Measure.normalize block (Measure.IsNormalizable.of_finite_mass total nonzero)) :
    ConditionalLaw (Lanes.fin (extent + 1))
      (blockPopulation extent sampler samplerFinite mass)
      ((Measure.dirac (Space.discrete Unit) ()).semiproduct
        (Kernel.const (Space.discrete Unit) block) (Kernel.IsSFinite.const _ blockFinite))
      (blockConditional extent sampler samplerFinite mass) :=
  conditional_block extent (Measure.dirac (Space.discrete Unit) ())
    (Kernel.const (Space.discrete Unit) block) (Kernel.const (Space.discrete Unit) sampler)
    (Kernel.IsSFinite.const _ blockFinite) (Kernel.IsSFinite.const _ samplerFinite)
    (fun _ => mass) (MeasurableMap.constant _ _ mass) (fun _ => total) (fun _ => conditional)
    _ (emptyConditional extent) (emptyConditionalFinite extent) (emptyConditional_law extent)

end

end Problib.Inference
