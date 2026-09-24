module

public import Problib.Measure.Kernel.Iteration.Basic
public import Problib.Measure.Kernel.Product
public import Problib.Measure.Kernel.Composition.Bind
set_option autoImplicit false

/-! Invariance of Markov kernels.

A kernel `K` leaves a measure `π` invariant when one step from `π` returns
`π`: `π.bind K = π`. Invariance composes with a target-initialized start: a
chain started at `π` has marginal `π` at every step (`kernel_invariant_iterate`).
Invariance alone promises nothing about any other start. The identity kernel
leaves every measure invariant, and a chain started at a point never leaves it
(`identity_invariant`, `identity_stuck`). Convergence from other starts is a
separate fact.

Detailed balance is the usual way to prove invariance. It says the joint law of
one step from `π` is symmetric under swapping its coordinates. The first
marginal of that joint is `π` weighted by each state's total transition mass,
and its second marginal is `π.bind K`, so a Markov kernel in detailed balance
leaves `π` invariant (`detailed_balance_invariant`). No statement here asks
`π` to be finite: an s-finite kernel attaches to any measure. -/

namespace Problib.Inference

open Problib.Real Problib.Measure

universe u

variable {α : Type u} {space : Space α}

public section

/-- One step from `target` returns `target`. -/
@[expose] def KernelInvariant (target : Measure space) (kernel : Kernel space space) : Prop :=
  target.bind kernel = target

/-- A chain started at the target has the target's law after one step. -/
theorem kernel_invariant_step {initial target : Measure space} {kernel : Kernel space space}
    (start : initial = target) (invariant : KernelInvariant target kernel) :
    initial.bind kernel = target :=
  start ▸ invariant

/-- A chain started at the target has the target's law after every number of
steps. -/
theorem kernel_invariant_iterate {target : Measure space} {kernel : Kernel space space}
    (invariant : KernelInvariant target kernel) :
    ∀ count, target.bind (Kernel.iterate kernel count) = target
  | 0 => by
      rw [Kernel.iterate, Measure.bind_deterministic, Measure.map_id]
  | count + 1 => by
      rw [Kernel.iterate, ← Measure.bind_assoc, invariant]
      exact kernel_invariant_iterate invariant count

/-- Two kernels that each leave the target invariant leave it invariant in
sequence. -/
theorem kernel_invariant_comp {target : Measure space} {first second : Kernel space space}
    (firstInvariant : KernelInvariant target first)
    (secondInvariant : KernelInvariant target second) :
    KernelInvariant target (first.comp second) := by
  unfold KernelInvariant
  rw [← Measure.bind_assoc, firstInvariant, secondInvariant]

/-- Invariance is linear in the target, so it survives normalization. -/
theorem kernel_invariant_smul {target : Measure space} {kernel : Kernel space space}
    (factor : ENNReal) (invariant : KernelInvariant target kernel) :
    KernelInvariant (Measure.smul factor target) kernel := by
  unfold KernelInvariant
  rw [Measure.smul_bind, invariant]

/-- The joint law of one step from `target` is symmetric under swapping the two
states. -/
@[expose] def DetailedBalance (target : Measure space) (kernel : Kernel space space)
    (finite : Kernel.IsSFinite kernel) : Prop :=
  (target.semiproduct kernel finite).map (fun pair => (pair.2, pair.1))
      (Space.swap_measurable space space) =
    target.semiproduct kernel finite

/-- A Markov kernel in detailed balance with a measure leaves it invariant: the
two marginals of a symmetric joint agree, and the first is the measure itself. -/
theorem detailed_balance_invariant {target : Measure space} {kernel : Kernel space space}
    {finite : Kernel.IsSFinite kernel}
    (markov : ∀ state, Measure.IsProbability (kernel state))
    (balance : DetailedBalance target kernel finite) :
    KernelInvariant target kernel := by
  apply Measure.ext
  intro set setMeasurable
  have secondMarginal := Measure.semiproduct_apply_product target kernel finite
    space.univ setMeasurable
  have firstMarginal := Measure.semiproduct_apply_product target kernel finite
    setMeasurable space.univ
  rw [Measure.restrict_univ] at secondMarginal
  rw [Measure.bind_apply target kernel setMeasurable, ← secondMarginal, ← balance,
    Measure.map_apply _ _ _
      (Space.product_set_measurable space space space.univ setMeasurable)]
  have swapped : Set.preimage (fun pair : α × α => (pair.2, pair.1))
      (Set.product Set.univ set) = Set.product set Set.univ :=
    Set.ext fun _ => ⟨fun member => ⟨member.2, member.1⟩, fun member => ⟨member.2, member.1⟩⟩
  rw [swapped, firstMarginal]
  calc
    lintegral (target.restrict set) (fun state => kernel state Set.univ) =
        lintegral (target.restrict set) (fun _ => ENNReal.one) := by
      apply lintegral_congr
      intro state
      exact (markov state).univ_eq_one
    _ = target set := by
      rw [lintegral_const, Measure.restrict_apply_univ, ENNReal.one_mul]

/-- The kernel that stays where it is. -/
@[expose] noncomputable def stay (space : Space α) : Kernel space space :=
  Kernel.deterministic (fun state => state) (MeasurableMap.identity space)

/-- The identity kernel leaves every measure invariant. -/
theorem identity_invariant (target : Measure space) : KernelInvariant target (stay space) := by
  unfold KernelInvariant stay
  rw [Measure.bind_deterministic, Measure.map_id]

/-- A chain that follows the identity kernel from a point stays at that point:
invariance gives no convergence from other starts. -/
theorem identity_stuck (point : α) (count : Nat) :
    (Measure.dirac space point).bind
        (Kernel.iterate (stay space) count) =
      Measure.dirac space point := by
  induction count with
  | zero => rw [Kernel.iterate, Measure.bind_deterministic, Measure.map_id]
  | succ count induction =>
      have still : (Measure.dirac space point).bind (stay space) = Measure.dirac space point :=
        identity_invariant _
      rw [Kernel.iterate, ← Measure.bind_assoc, still, induction]

end

end Problib.Inference
