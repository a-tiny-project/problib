module

public import Problib.Inference.Population.Conditional
public import Problib.Measure.Normalization
set_option autoImplicit false

/-! # Particle Gibbs

A particle Gibbs step at `x` draws a marked population from a conditional law
at `x`, redraws the marked lane from the categorical law of the weights, and
reads the marked lane's value (`particleGibbs`). It is the reference chain
(`referenceChain`) of the extended target through the conditional law and the
lane refresh. So it keeps the target of every Markov conditional law
(`particleGibbs_invariant`), and the normalized target when that is defined
(`particleGibbs_normalized`).

The conditional law is the input. A run of conditional SMC is one when it is
composed from `conditional_replicate`, `conditional_resample` and
`conditional_propagate` by `conditional_step_comp`, and its conditional kernel
is Markov. The step proves invariance only: convergence needs a minorization of
the conditional kernel, as `independence_approaches` has for independence
proposals. -/

namespace Problib.Inference

open Problib.Real Problib.Measure

public section

variable {α : Type} {space : Space α}

/-- One particle Gibbs step: draw a marked population from `conditional` at the
current point, redraw the marked lane from the categorical law of the weights,
and read the marked lane's value. At total weight zero the refresh takes the
lane that `ancestorLane` gives a single child, which is the kept uniform
fallback. The refresh needs a Markov fallback because it is a transition, and
`ancestorLane` is Markov. -/
@[expose] noncomputable def particleGibbs {ι : Type} (lanes : Lanes ι) (space : Space α)
    (conditional : Kernel space (markedSpace ι space)) : Kernel space space :=
  referenceChain reference (reference_measurable lanes space) conditional
    (laneRefresh lanes space (ancestorLane lanes 1 space 0) (ancestorLane_markov lanes 1 space 0))

/-- Particle Gibbs keeps the target of a conditional law. It needs the
conditional kernel Markov: the step draws a population from it, and only a
probability reads the target back at the marked lane (`conditional_reference`).
The population law need not be a probability, and the target need not be
normalized. -/
theorem particleGibbs_invariant {ι : Type} {lanes : Lanes ι}
    {population : Measure (populationSpace ι space)} {target : Measure space}
    {conditional : Kernel space (markedSpace ι space)}
    (law : ConditionalLaw lanes population target conditional)
    (markov : ∀ point, Measure.IsProbability (conditional point)) :
    KernelInvariant target (particleGibbs lanes space conditional) := by
  have invariant := referenceChain_invariant (extended lanes population) reference
    (reference_measurable lanes space) conditional (conditional_disintegrates law markov)
    (laneRefresh lanes space (ancestorLane lanes 1 space 0) (ancestorLane_markov lanes 1 space 0))
    (laneRefresh_invariant lanes population _ _)
  rw [conditional_reference law markov] at invariant
  exact invariant

/-- Particle Gibbs keeps the normalized target. It needs the target
normalizable, since only then is there a normalized target to keep, and the
conditional kernel Markov, as `particleGibbs_invariant` does. -/
theorem particleGibbs_normalized {ι : Type} {lanes : Lanes ι}
    {population : Measure (populationSpace ι space)} {target : Measure space}
    {conditional : Kernel space (markedSpace ι space)}
    (law : ConditionalLaw lanes population target conditional)
    (markov : ∀ point, Measure.IsProbability (conditional point))
    (normalizable : Measure.IsNormalizable target) :
    KernelInvariant (Measure.normalize target normalizable)
      (particleGibbs lanes space conditional) := by
  rcases ENNReal.exists_finite_of_finite normalizable.finite.univ_finite with ⟨mass, total⟩
  rw [Measure.normalize_eq_of_total_eq target normalizable total]
  exact kernel_invariant_smul _ (particleGibbs_invariant law markov)

end

end Problib.Inference
