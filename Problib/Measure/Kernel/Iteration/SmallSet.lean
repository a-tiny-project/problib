module

public import Problib.Measure.Kernel.Iteration.Minorization
import Problib.Measure.Integral.Lebesgue.Measure

set_option autoImplicit false

/-!
# Small sets

A small set is a measurable region on which one positive iterate of the kernel
dominates a common scaled law. Skeletonizing the iterate makes the step count
one, and pushing the law forward along the chain delays the bound.
-/

namespace Problib.Measure.Kernel

open Problib.Real

universe u
variable {α : Type u} {space : Space α}

/-- A measurable region on which one positive iterate minorizes a law. -/
@[expose] public def SmallSet (kernel : Kernel space space) (region : Set α) : Prop :=
  space.Measurable region ∧
    ∃ steps weight reference, MinorizationOn kernel region steps weight reference

/-- The `steps`-skeleton of a local minorization minorizes in one step. -/
public theorem MinorizationOn.skeleton {kernel : Kernel space space}
    {region : Set α} {steps : Nat} {weight : NNReal} {reference : Giry.Law space}
    (minor : MinorizationOn kernel region steps weight reference) :
    MinorizationOn (iterate kernel steps) region 1 weight reference := by
  refine ⟨iterate_isProbability kernel minor.markov steps, Nat.zero_lt_one,
    minor.weightPositive, minor.weightAtMostOne, ?_⟩
  intro input member event measurable
  rw [iterate_one]
  exact minor.lower input member event measurable

/-- Running the chain `count` more steps after the bound pushes its law forward
by `count` steps. -/
public theorem MinorizationOn.shift {kernel : Kernel space space}
    {region : Set α} {steps : Nat} {weight : NNReal} {reference : Giry.Law space}
    (minor : MinorizationOn kernel region steps weight reference) (count : Nat) :
    MinorizationOn kernel region (steps + count) weight
      (iterateLaw kernel minor.markov reference count) := by
  refine ⟨minor.markov, Nat.lt_of_lt_of_le minor.stepsPositive
    (Nat.le_add_right steps count), minor.weightPositive,
    minor.weightAtMostOne, ?_⟩
  intro input member event measurable
  have bound := lintegral_mono_measure
    (fun state => iterate kernel count state event)
    (Measure.smul (ENNReal.finite weight) reference.val)
    (iterate kernel steps input) (minor.lower input member)
  rw [lintegral_smul_measure, ← comp_apply_measurable _ _ _ measurable,
    ← iterate_add] at bound
  change ENNReal.le
    ((Measure.smul (ENNReal.finite weight)
      (reference.val.bind (iterate kernel count))) event)
    (iterate kernel (steps + count) input event)
  rw [Measure.smul_apply_measurable _ _ measurable,
    Measure.bind_apply _ _ measurable]
  exact bound

/-- A global minorization makes the whole space small. -/
public theorem smallSet_univ {kernel : Kernel space space} {steps : Nat}
    {weight : NNReal} {reference : Giry.Law space}
    (minor : Minorization kernel steps weight reference) :
    SmallSet kernel Set.univ :=
  ⟨space.univ, steps, weight, reference,
    (minorization_on_univ kernel steps weight reference).mp minor⟩

end Problib.Measure.Kernel
