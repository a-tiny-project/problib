module

public import Problib.Measure.Kernel.Iteration.Basic
public import Problib.Measure.Kernel.Product
public import Problib.Measure.Kernel.Composition.Bind
public import Problib.Measure.Kernel.Composition.Bind.Transport
public import Problib.Measure.Kernel.Scale
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
`π` to be finite: an s-finite kernel attaches to any measure.

Invariance also transfers along a measurable map. A kernel that moves almost
every image point as the map carries the source kernel's step leaves the
pushed target invariant (`invariant_map`). -/

namespace Problib.Inference

open Problib.Real Problib.Measure

universe u v

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

/-- Invariance transfers along a measurable map: a kernel that moves almost
every image point as the map carries the source kernel's step keeps the pushed
target. -/
theorem invariant_map {β : Type v} {source : Space β} {target : Measure source}
    {kernel : Kernel source source} {move : Kernel space space} (embed : β → α)
    (measurable : MeasurableMap source space embed) (invariant : KernelInvariant target kernel)
    (agrees : target.AE fun x => move (embed x) = (kernel x).map embed measurable) :
    KernelInvariant (target.map embed measurable) move := by
  unfold KernelInvariant at invariant ⊢
  rw [Measure.bind_map, Measure.bind_congr_ae target (left := move.precomp embed measurable)
      (right := kernel.map embed measurable) agrees,
    ← Measure.map_bind, invariant]

/-- A finite cycle of invariant kernels leaves the target invariant.
`Kernel.comp` runs its left argument first, so the list runs in order. -/
theorem invariant_cycle (target : Measure space)
    (steps : List (Kernel space space))
    (each : ∀ step, step ∈ steps → KernelInvariant target step) :
    KernelInvariant target (steps.foldr Kernel.comp (stay space)) := by
  induction steps with
  | nil => exact identity_invariant target
  | cons head tail induction =>
      change KernelInvariant target (head.comp (tail.foldr Kernel.comp (stay space)))
      exact kernel_invariant_comp (each head (by simp))
        (induction (fun step member => each step (by simp [member])))

/-- A fixed mixture of invariant kernels leaves the target invariant. -/
theorem invariant_mixture (target : Measure space)
    {first second : Kernel space space} (weight : NNReal)
    (bounded : NNReal.le weight NNReal.one)
    (firstInvariant : KernelInvariant target first)
    (secondInvariant : KernelInvariant target second) :
    KernelInvariant target (Kernel.mixture weight first second) := by
  apply Measure.ext
  intro event eventMeasurable
  have firstMeasurable := first.measurable eventMeasurable
  have secondMeasurable := second.measurable eventMeasurable
  have firstEvent : lintegral target (fun input => first input event) = target event := by
    rw [← Measure.bind_apply target first eventMeasurable, firstInvariant]
  have secondEvent : lintegral target (fun input => second input event) = target event := by
    rw [← Measure.bind_apply target second eventMeasurable, secondInvariant]
  have weights : ENNReal.add (ENNReal.finite weight)
      (ENNReal.finite (NNReal.sub NNReal.one weight)) = ENNReal.one :=
    congrArg ENNReal.finite
      ((NNReal.add_comm weight (NNReal.sub NNReal.one weight)).trans
        (NNReal.sub_add_cancel bounded))
  rw [Measure.bind_apply target (Kernel.mixture weight first second) eventMeasurable]
  calc
    lintegral target (fun input => Kernel.mixture weight first second input event) =
        lintegral target (fun input => ENNReal.add
          (ENNReal.mul (ENNReal.finite weight) (first input event))
          (ENNReal.mul (ENNReal.finite (NNReal.sub NNReal.one weight))
            (second input event))) := by
      apply lintegral_congr
      intro input
      rw [Kernel.mixture, Kernel.add_apply,
        Measure.add_apply_measurable _ _ eventMeasurable,
        Kernel.smul_apply, Kernel.smul_apply,
        Measure.smul_apply_measurable _ _ eventMeasurable,
        Measure.smul_apply_measurable _ _ eventMeasurable]
    _ = ENNReal.add
          (ENNReal.mul (ENNReal.finite weight) (target event))
          (ENNReal.mul (ENNReal.finite (NNReal.sub NNReal.one weight))
            (target event)) := by
      rw [lintegral_add target
        (ENNRealMeasurable.mul (ENNRealMeasurable.constant _ _) firstMeasurable)
        (ENNRealMeasurable.mul (ENNRealMeasurable.constant _ _) secondMeasurable),
        lintegral_smul target _ firstMeasurable,
        lintegral_smul target _ secondMeasurable, firstEvent, secondEvent]
    _ = target event := by
      rw [ENNReal.mul_comm (ENNReal.finite weight),
        ENNReal.mul_comm (ENNReal.finite (NNReal.sub NNReal.one weight)),
        ← ENNReal.mul_add, weights, ENNReal.mul_one]

/-- A fixed mixture of kernels in detailed balance with the target is in
detailed balance with it. -/
theorem detailed_balance_mixture (target : Measure space)
    {first second : Kernel space space} (weight : NNReal)
    (firstFinite : Kernel.IsSFinite first)
    (secondFinite : Kernel.IsSFinite second)
    (firstBalance : DetailedBalance target first firstFinite)
    (secondBalance : DetailedBalance target second secondFinite) :
    DetailedBalance target (Kernel.mixture weight first second)
      (Kernel.IsSFinite.mixture weight firstFinite secondFinite) := by
  have joint : target.semiproduct (Kernel.mixture weight first second)
      (Kernel.IsSFinite.mixture weight firstFinite secondFinite) =
      Measure.add
        (Measure.smul (ENNReal.finite weight)
          (target.semiproduct first firstFinite))
        (Measure.smul (ENNReal.finite (NNReal.sub NNReal.one weight))
          (target.semiproduct second secondFinite)) := by
    refine (Measure.semiproduct_kernel_add target _ _
      (firstFinite.smul (ENNReal.finite weight) True.intro)
      (secondFinite.smul (ENNReal.finite (NNReal.sub NNReal.one weight)) True.intro)
      _).trans ?_
    rw [Measure.semiproduct_kernel_smul target _ first firstFinite,
      Measure.semiproduct_kernel_smul target _ second secondFinite]
  unfold DetailedBalance at *
  rw [joint, Measure.map_add, Measure.map_smul, Measure.map_smul,
    firstBalance, secondBalance]

/-- A finite weighted sum of invariant kernels whose weights sum to one leaves
the target invariant. -/
theorem invariant_weightedSum (target : Measure space)
    (steps : List (NNReal × Kernel space space))
    (each : ∀ entry, entry ∈ steps → KernelInvariant target entry.2)
    (total : NNReal.additiveLaws.listSum (steps.map Prod.fst) = NNReal.one) :
    KernelInvariant target (Kernel.weightedSum steps) := by
  have mass : ∀ (current : List (NNReal × Kernel space space)),
      (∀ entry, entry ∈ current → KernelInvariant target entry.2) →
      ∀ event, space.Measurable event →
      lintegral target (fun input => Kernel.weightedSum current input event) =
        ENNReal.mul (ENNReal.finite (NNReal.additiveLaws.listSum (current.map Prod.fst)))
          (target event) := by
    intro current
    induction current with
    | nil =>
        intro _ event _
        calc
          lintegral target (fun input => Kernel.weightedSum [] input event) =
              lintegral target (fun _ => ENNReal.zero) := by
            apply lintegral_congr
            intro input
            rw [Kernel.weightedSum, Kernel.zero_apply, Measure.zero_apply]
          _ = ENNReal.zero := by rw [lintegral_const, ENNReal.zero_mul]
          _ = _ := (ENNReal.zero_mul _).symm
    | cons entry rest induction =>
        intro invariant event eventMeasurable
        have headInvariant := invariant entry (List.mem_cons_self ..)
        have headEvent : lintegral target (fun input => entry.2 input event) =
            target event := by
          rw [← Measure.bind_apply target entry.2 eventMeasurable, headInvariant]
        have headMeasurable := entry.2.measurable eventMeasurable
        have restMeasurable := (Kernel.weightedSum rest).measurable eventMeasurable
        calc
          lintegral target
              (fun input => Kernel.weightedSum (entry :: rest) input event) =
            lintegral target (fun input => ENNReal.add
              (ENNReal.mul (ENNReal.finite entry.1) (entry.2 input event))
              (Kernel.weightedSum rest input event)) := by
            apply lintegral_congr
            intro input
            rw [Kernel.weightedSum, Kernel.add_apply,
              Measure.add_apply_measurable _ _ eventMeasurable,
              Kernel.smul_apply, Measure.smul_apply_measurable _ _ eventMeasurable]
          _ = ENNReal.add (ENNReal.mul (ENNReal.finite entry.1) (target event))
                (ENNReal.mul (ENNReal.finite (NNReal.additiveLaws.listSum (rest.map Prod.fst)))
                  (target event)) := by
            rw [lintegral_add target
              (ENNRealMeasurable.mul (ENNRealMeasurable.constant _ _)
                headMeasurable) restMeasurable,
              lintegral_smul target _ headMeasurable, headEvent,
              induction (fun other member =>
                invariant other (List.mem_cons_of_mem _ member))
                event eventMeasurable]
          _ = _ := by
            rw [ENNReal.mul_comm (ENNReal.finite entry.1),
              ENNReal.mul_comm (ENNReal.finite (NNReal.additiveLaws.listSum (rest.map Prod.fst))),
              ← ENNReal.mul_add, ENNReal.mul_comm]
            rfl
  apply Measure.ext
  intro event eventMeasurable
  rw [Measure.bind_apply target _ eventMeasurable,
    mass steps each event eventMeasurable, total]
  exact ENNReal.one_mul _

/-- A finite weighted sum of kernels in detailed balance with the target is in
detailed balance with it. -/
theorem detailed_balance_weightedSum (target : Measure space) :
    (steps : List (NNReal × Kernel space space)) →
    (finite : ∀ entry, entry ∈ steps → Kernel.IsSFinite entry.2) →
    (∀ entry (member : entry ∈ steps),
      DetailedBalance target entry.2 (finite entry member)) →
    DetailedBalance target (Kernel.weightedSum steps)
      (Kernel.IsSFinite.weightedSum steps finite)
  | [], _, _ => by
      unfold DetailedBalance
      apply Measure.ext
      intro set setMeasurable
      rw [Measure.map_apply _ _ _ setMeasurable,
        Measure.semiproduct_apply _ _ _
          (Space.swap_measurable space space setMeasurable),
        Measure.semiproduct_apply _ _ _ setMeasurable]
      apply lintegral_congr
      intro input
      rw [Kernel.weightedSum, Kernel.zero_apply, Measure.zero_apply,
        Measure.zero_apply]
  | entry :: rest, finite, each => by
      let headFinite := finite entry (List.mem_cons_self ..)
      let restFinite : ∀ other, other ∈ rest → Kernel.IsSFinite other.2 :=
        fun other member => finite other (List.mem_cons_of_mem _ member)
      have restBalance := detailed_balance_weightedSum target rest restFinite
        (fun other member => each other (List.mem_cons_of_mem _ member))
      have headBalance := each entry (List.mem_cons_self ..)
      have joint : target.semiproduct (Kernel.weightedSum (entry :: rest))
          (Kernel.IsSFinite.weightedSum (entry :: rest) finite) =
          Measure.add
            (Measure.smul (ENNReal.finite entry.1)
              (target.semiproduct entry.2 headFinite))
            (target.semiproduct (Kernel.weightedSum rest)
              (Kernel.IsSFinite.weightedSum rest restFinite)) := by
        refine (Measure.semiproduct_kernel_add target _ _
          (headFinite.smul (ENNReal.finite entry.1) True.intro)
          (Kernel.IsSFinite.weightedSum rest restFinite) _).trans ?_
        rw [Measure.semiproduct_kernel_smul target _ entry.2 headFinite]
      unfold DetailedBalance at *
      rw [joint, Measure.map_add, Measure.map_smul, headBalance, restBalance]

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
