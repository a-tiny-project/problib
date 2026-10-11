module

public import Problib.Inference.Involutive.Basic
public import Problib.Inference.MetropolisHastings
public import Problib.Inference.Invariance
public import Problib.Measure.Kernel.Product
public import Problib.Measure.Kernel.Density.Conditional
public import Problib.Measure.Space.Sum
public import Problib.Measure.Uniform

set_option autoImplicit false

/-! Involutive accept/reject kernels.

An auxiliary draw extends a state to a pair. A measurable involution proposes
the next state, and a strict uniform comparison chooses the move or the
current state. The symmetrized extended measure supplies a reference for
balance without a reversible proposal premise. -/

namespace Problib.Inference

open Problib.Real Problib.Measure
open Problib.Real.Construction
open Problib.Measure.Real (Carrier borel ofReal_measurable UnitInterval unitBorel
  unitInclusion_measurable measurable_lt measurable_mul uniform01
  uniform01_isProbability uniform01_univ)

universe u v w
variable {α : Type u} {β : Type v}
variable {state : Space α} {auxiliarySpace : Space β}

public section

open Classical in
/-- A strict uniform test chooses between a destination and the current state
with the law of Problib's move-or-stay kernel, when the kernel's acceptance at
the pair is the Uniform mass of the tested event. -/
theorem moveOrStayTo_uniform
    (destination : α × β → α)
    (destinationMeasurable :
      MeasurableMap (Space.product state auxiliarySpace) state destination)
    (accept : α × β → ENNReal)
    (acceptMeasurable : ENNRealMeasurable (Space.product state auxiliarySpace) accept)
    (pair : α × β) {event : Set UnitInterval} (eventMeasurable : unitBorel.Measurable event)
    (accepts : accept pair = uniform01 event)
    (choiceMeasurable : MeasurableMap unitBorel state
      (fun draw => if event draw then destination pair else pair.1)) :
    moveOrStayTo destination destinationMeasurable accept acceptMeasurable pair =
      uniform01.map (fun draw => if event draw then destination pair else pair.1)
        choiceMeasurable := by
  apply Measure.ext
  intro set setMeasurable
  rw [apply_eq_lintegral_indicator _ setMeasurable,
    lintegral_moveOrStayTo _ _ _ _ _
      (ENNRealMeasurable.indicator setMeasurable (ENNRealMeasurable.constant _ _)),
    Measure.map_apply _ _ _ setMeasurable, accepts]
  have atMostOne : ENNReal.le (uniform01 event) ENNReal.one := by
    have bound := uniform01.mono (Set.subset_univ event)
    rw [uniform01_univ] at bound
    exact bound
  change _ = uniform01 (fun draw => set (if event draw then destination pair else pair.1))
  by_cases here : set (destination pair) <;> by_cases there : set pair.1
  · have whole : (fun draw => set (if event draw then destination pair else pair.1)) =
        Set.univ := by
      apply Set.ext
      intro draw
      by_cases inside : event draw <;> simp [inside, here, there, Set.univ]
    simp only [ennrealIndicator, ennrealPiecewise, here, there, ite_true, ENNReal.mul_one]
    rw [whole, uniform01_univ, ENNReal.add_comm, ENNReal.sub_add_cancel atMostOne]
  · have exact : (fun draw => set (if event draw then destination pair else pair.1)) =
        event := by
      apply Set.ext
      intro draw
      by_cases inside : event draw <;> simp [inside, here, there]
    simp only [ennrealIndicator, ennrealPiecewise, here, there, ite_true, ite_false,
      ENNReal.mul_one, ENNReal.mul_zero, ENNReal.add_zero]
    rw [exact]
  · have rest : (fun draw => set (if event draw then destination pair else pair.1)) =
        Set.complement event := by
      apply Set.ext
      intro draw
      by_cases inside : event draw <;> simp [inside, here, there, Set.complement]
    simp only [ennrealIndicator, ennrealPiecewise, here, there, ite_true, ite_false,
      ENNReal.mul_one, ENNReal.mul_zero, ENNReal.zero_add]
    rw [rest, uniform01_isProbability.apply_complement eventMeasurable]
  · have nothing : (fun draw => set (if event draw then destination pair else pair.1)) =
        Set.empty := by
      apply Set.ext
      intro draw
      by_cases inside : event draw <;> simp [inside, here, there, Set.empty]
    simp only [ennrealIndicator, ennrealPiecewise, here, there, ite_false,
      ENNReal.mul_zero, ENNReal.add_zero]
    rw [nothing]
    exact (Measure.empty_apply uniform01).symm

/-- The strict uniform test on a pair and its involutive image. -/
@[expose] noncomputable def involutiveAccept
    (involution : α × β → α × β)
    (density : α × β → Carrier) (point : α × β) : ENNReal :=
  metropolisAccept density (point, involution point)

theorem involutiveAccept_measurable
    (involution : α × β → α × β)
    (involutionMeasurable :
      MeasurableMap (Space.product state auxiliarySpace)
        (Space.product state auxiliarySpace) involution)
    {density : α × β → Carrier}
    (densityMeasurable : MeasurableMap (Space.product state auxiliarySpace) borel density) :
    ENNRealMeasurable (Space.product state auxiliarySpace)
      (involutiveAccept involution density) := by
  unfold involutiveAccept
  exact (metropolisAccept_measurable densityMeasurable).comp
    (Space.pair_measurable (MeasurableMap.identity _) involutionMeasurable)

theorem involutiveAccept_le_one
    (involution : α × β → α × β) (density : α × β → Carrier)
    (point : α × β) :
    ENNReal.le (involutiveAccept involution density point) ENNReal.one := by
  change ENNReal.le (metropolisAccept density (point, involution point)) ENNReal.one
  exact metropolisAccept_le_one density (point, involution point)

/-- The symmetrized extended measure is fixed by the involution. -/
theorem symmetrized_map_involution
    (extended : Measure (Space.product state auxiliarySpace))
    (involution : α × β → α × β)
    (involutionMeasurable :
      MeasurableMap (Space.product state auxiliarySpace)
        (Space.product state auxiliarySpace) involution)
    (involutive : ∀ point, involution (involution point) = point) :
    (Measure.add extended (extended.map involution involutionMeasurable)).map
        involution involutionMeasurable =
      Measure.add extended (extended.map involution involutionMeasurable) := by
  have twice : (extended.map involution involutionMeasurable).map
      involution involutionMeasurable = extended := by
    apply Measure.ext
    intro set setMeasurable
    rw [Measure.map_apply _ _ _ setMeasurable,
      Measure.map_apply _ _ _ (involutionMeasurable setMeasurable)]
    have same : Set.preimage involution (Set.preimage involution set) = set := by
      apply Set.ext
      intro point
      change (involution (involution point) ∈ set) ↔ point ∈ set
      rw [involutive point]
    rw [same]
  rw [Measure.map_add, twice]
  exact Measure.add_comm _ _

/-- A density fixed by a measure-preserving map has a fixed weighted
measure. -/
theorem withDensity_involution
    (measure : Measure (Space.product state auxiliarySpace))
    (involution : α × β → α × β)
    (involutionMeasurable :
      MeasurableMap (Space.product state auxiliarySpace)
        (Space.product state auxiliarySpace) involution)
    (measureInvariant : measure.map involution involutionMeasurable = measure)
    {density : α × β → ENNReal}
    (densityMeasurable :
      ENNRealMeasurable (Space.product state auxiliarySpace) density)
    (densitySymmetric : ∀ point, density (involution point) = density point) :
    (measure.withDensity density).map involution involutionMeasurable =
      measure.withDensity density := by
  apply Measure.ext
  intro set setMeasurable
  let indicator : α × β → ENNReal := ennrealIndicator set fun _ => ENNReal.one
  have indicatorMeasurable :
      ENNRealMeasurable (Space.product state auxiliarySpace) indicator :=
    ENNRealMeasurable.indicator setMeasurable
      (ENNRealMeasurable.constant _ _)
  have productMeasurable :=
    ENNRealMeasurable.mul densityMeasurable indicatorMeasurable
  have mappedMeasurable : ENNRealMeasurable
      (Space.product state auxiliarySpace)
      (fun point => indicator (involution point)) :=
    indicatorMeasurable.comp involutionMeasurable
  rw [apply_eq_lintegral_indicator _ setMeasurable,
    apply_eq_lintegral_indicator _ setMeasurable,
    lintegral_map _ _ _ indicatorMeasurable,
    lintegral_withDensity _ densityMeasurable mappedMeasurable,
    lintegral_withDensity _ densityMeasurable indicatorMeasurable]
  calc
    lintegral measure (fun point =>
        ENNReal.mul (density point) (indicator (involution point))) =
      lintegral measure (fun point =>
        ENNReal.mul (density (involution point))
          (indicator (involution point))) := by
        apply lintegral_congr
        intro point
        rw [densitySymmetric]
    _ = lintegral (measure.map involution involutionMeasurable)
          (fun point => ENNReal.mul (density point) (indicator point)) :=
      (lintegral_map _ _ _ productMeasurable).symm
    _ = _ := by rw [measureInvariant]

/-- A balanced density over an invariant reference makes the accepted flux
invariant under the involution. -/
theorem accepted_symmetric_of_balance
    (reference extended : Measure (Space.product state auxiliarySpace))
    (involution : α × β → α × β)
    (involutionMeasurable :
      MeasurableMap (Space.product state auxiliarySpace)
        (Space.product state auxiliarySpace) involution)
    (referenceInvariant :
      reference.map involution involutionMeasurable = reference)
    {density accept : α × β → ENNReal}
    (densityMeasurable :
      ENNRealMeasurable (Space.product state auxiliarySpace) density)
    (acceptMeasurable :
      ENNRealMeasurable (Space.product state auxiliarySpace) accept)
    (represents : extended = reference.withDensity density)
    (balance : ∀ point,
      ENNReal.mul (density point) (accept point) =
      ENNReal.mul (density (involution point)) (accept (involution point))) :
    (extended.withDensity accept).map involution involutionMeasurable =
      extended.withDensity accept := by
  rw [represents,
    Measure.withDensity_withDensity _ densityMeasurable acceptMeasurable]
  exact withDensity_involution reference involution involutionMeasurable
    referenceInvariant (ENNRealMeasurable.mul densityMeasurable acceptMeasurable)
    (fun point => (balance point).symm)

/-- The strict test balances a density with its image under an involution. -/
theorem involutiveAccept_balanced
    (involution : α × β → α × β)
    (involutive : ∀ point, involution (involution point) = point)
    (density : α × β → Carrier) (point : α × β) :
    ENNReal.mul (ENNReal.ofReal (density point))
      (involutiveAccept involution density point) =
    ENNReal.mul (ENNReal.ofReal (density (involution point)))
      (involutiveAccept involution density (involution point)) := by
  unfold involutiveAccept
  rw [metropolis_balance density (point, involution point),
    metropolis_balance density
      (involution point, involution (involution point)), involutive point]
  have commute (left right : ENNReal) :
      ENNReal.min left right = ENNReal.min right left := by
    rcases ENNReal.le_total left right with included | included
    · rw [ENNReal.min_eq_left included, ENNReal.min_eq_right included]
    · rw [ENNReal.min_eq_right included, ENNReal.min_eq_left included]
  exact commute _ _

/-- A strict accept/reject step is invariant when the extended target has a
density against a reference that the involution preserves. A Jacobian, where
one applies, lives in this density. -/
theorem involutive_invariant_of_reference
    (target : Measure state) (auxiliary : Kernel state auxiliarySpace)
    (auxiliaryFinite : Kernel.IsSFinite auxiliary)
    (auxiliaryMarkov : ∀ input, Measure.IsProbability (auxiliary input))
    (involution : α × β → α × β)
    (involutionMeasurable :
      MeasurableMap (Space.product state auxiliarySpace)
        (Space.product state auxiliarySpace) involution)
    (involutive : ∀ point, involution (involution point) = point)
    (reference : Measure (Space.product state auxiliarySpace))
    (referenceInvariant :
      reference.map involution involutionMeasurable = reference)
    {density : α × β → Carrier}
    (densityMeasurable :
      MeasurableMap (Space.product state auxiliarySpace) borel density)
    (represents : target.semiproduct auxiliary auxiliaryFinite =
      reference.withDensity (fun point => ENNReal.ofReal (density point))) :
    KernelInvariant target
      (involutiveKernel auxiliary auxiliaryFinite involution involutionMeasurable
        (involutiveAccept involution density)
        (involutiveAccept_measurable involution involutionMeasurable
          densityMeasurable)) := by
  have symmetric := accepted_symmetric_of_balance
    _ _ involution involutionMeasurable referenceInvariant
    (ofReal_measurable.comp densityMeasurable)
    (involutiveAccept_measurable involution involutionMeasurable densityMeasurable)
    represents
    (involutiveAccept_balanced involution involutive density)
  have balance := involutive_detailed_balance target auxiliary auxiliaryFinite
    involution involutionMeasurable involutive
    (involutiveAccept_measurable involution involutionMeasurable densityMeasurable)
    symmetric
  exact detailed_balance_invariant
    (involutiveKernel_markov auxiliaryFinite auxiliaryMarkov
      involutionMeasurable
      (involutiveAccept_measurable involution involutionMeasurable densityMeasurable)
      (involutiveAccept_le_one involution density)) balance

/-- A strict accept/reject step is invariant when the extended target has a
density against its own symmetrization. That reference always exists, so no
reference measure is supplied. -/
theorem involutive_invariant
    (target : Measure state) (auxiliary : Kernel state auxiliarySpace)
    (auxiliaryFinite : Kernel.IsSFinite auxiliary)
    (auxiliaryMarkov : ∀ input, Measure.IsProbability (auxiliary input))
    (involution : α × β → α × β)
    (involutionMeasurable :
      MeasurableMap (Space.product state auxiliarySpace)
        (Space.product state auxiliarySpace) involution)
    (involutive : ∀ point, involution (involution point) = point)
    {density : α × β → Carrier}
    (densityMeasurable :
      MeasurableMap (Space.product state auxiliarySpace) borel density)
    (represents : Measure.IsDensity
      (target.semiproduct auxiliary auxiliaryFinite)
      (Measure.add (target.semiproduct auxiliary auxiliaryFinite)
        ((target.semiproduct auxiliary auxiliaryFinite).map
          involution involutionMeasurable))
      (fun point => ENNReal.ofReal (density point))) :
    KernelInvariant target
      (involutiveKernel auxiliary auxiliaryFinite involution involutionMeasurable
        (involutiveAccept involution density)
        (involutiveAccept_measurable involution involutionMeasurable
          densityMeasurable)) :=
  involutive_invariant_of_reference target auxiliary auxiliaryFinite
    auxiliaryMarkov involution involutionMeasurable involutive _
    (symmetrized_map_involution _ involution involutionMeasurable involutive)
    densityMeasurable represents.eq_withDensity

/-- Apply the strict uniform comparison to an extended state and a uniform
draw, returning the proposed state or the current state. -/
@[expose] noncomputable def involutiveDecision
    (involution : α × β → α × β)
    (density : α × β → Carrier)
    (sampled : (α × β) × UnitInterval) : α := by
  classical
  exact if Dedekind.lt
      (Dedekind.mul sampled.2.val (density sampled.1))
      (density (involution sampled.1))
    then (involution sampled.1).1 else sampled.1.1

theorem involutiveDecision_measurable
    (involution : α × β → α × β)
    (involutionMeasurable :
      MeasurableMap (Space.product state auxiliarySpace)
        (Space.product state auxiliarySpace) involution)
    (density : α × β → Carrier)
    (densityMeasurable :
      MeasurableMap (Space.product state auxiliarySpace) borel density) :
    MeasurableMap
      (Space.product (Space.product state auxiliarySpace) unitBorel)
      state (involutiveDecision involution density) := by
  classical
  let sampledSpace := Space.product (Space.product state auxiliarySpace) unitBorel
  let pairMeasurable : MeasurableMap sampledSpace
      (Space.product state auxiliarySpace) Prod.fst :=
    Space.first_measurable _ _
  let drawMeasurable : MeasurableMap sampledSpace borel
      (fun sampled => sampled.2.val) :=
    MeasurableMap.comp unitInclusion_measurable (Space.second_measurable _ _)
  let currentWeight : MeasurableMap sampledSpace borel
      (fun sampled => density sampled.1) :=
    MeasurableMap.comp densityMeasurable pairMeasurable
  let proposedWeight : MeasurableMap sampledSpace borel
      (fun sampled => density (involution sampled.1)) :=
    MeasurableMap.comp densityMeasurable
      (MeasurableMap.comp involutionMeasurable pairMeasurable)
  let event : Set ((α × β) × UnitInterval) := fun sampled =>
    Dedekind.lt (Dedekind.mul sampled.2.val (density sampled.1))
      (density (involution sampled.1))
  have eventMeasurable : sampledSpace.Measurable event :=
    measurable_lt (measurable_mul drawMeasurable currentWeight) proposedWeight
  have proposedMeasurable : MeasurableMap sampledSpace state
      (fun sampled => (involution sampled.1).1) :=
    MeasurableMap.comp (Space.first_measurable state auxiliarySpace)
      (MeasurableMap.comp involutionMeasurable pairMeasurable)
  have currentMeasurable : MeasurableMap sampledSpace state
      (fun sampled => sampled.1.1) :=
    MeasurableMap.comp (Space.first_measurable state auxiliarySpace)
      pairMeasurable
  intro set setMeasurable
  have same : Set.preimage (involutiveDecision involution density) set =
      Set.union (Set.inter event
        (Set.preimage (fun sampled => (involution sampled.1).1) set))
        (Set.inter (Set.complement event)
          (Set.preimage (fun sampled => sampled.1.1) set)) := by
    apply Set.ext
    intro sampled
    by_cases accepted : event sampled <;>
      simp [involutiveDecision, event, Set.preimage, Set.union, Set.inter,
        Set.complement, accepted]
  rw [same]
  exact sampledSpace.union
    (sampledSpace.inter eventMeasurable (proposedMeasurable setMeasurable))
    (sampledSpace.inter (sampledSpace.complement eventMeasurable)
      (currentMeasurable setMeasurable))

/-- From an extended state, draw a uniform coin and make the involutive
accept/reject decision. -/
@[expose] noncomputable def involutiveTest
    (involution : α × β → α × β)
    (involutionMeasurable :
      MeasurableMap (Space.product state auxiliarySpace)
        (Space.product state auxiliarySpace) involution)
    (density : α × β → Carrier)
    (densityMeasurable :
      MeasurableMap (Space.product state auxiliarySpace) borel density) :
    Kernel (Space.product state auxiliarySpace) state :=
  (Kernel.attach
    (Kernel.const (Space.product state auxiliarySpace) uniform01)
    (Kernel.IsSFinite.const _
      (Measure.SFinite.ofFinite uniform01_isProbability.to_finite))).comp
    (Kernel.deterministic (involutiveDecision involution density)
      (involutiveDecision_measurable involution involutionMeasurable
        density densityMeasurable))

/-- The coin test moves with the strict Metropolis acceptance of the pair and
its involutive image, and otherwise stays. -/
theorem involutiveTest_law
    (involution : α × β → α × β)
    (involutionMeasurable :
      MeasurableMap (Space.product state auxiliarySpace)
        (Space.product state auxiliarySpace) involution)
    (density : α × β → Carrier)
    (densityMeasurable :
      MeasurableMap (Space.product state auxiliarySpace) borel density) :
    involutiveTest involution involutionMeasurable density densityMeasurable =
      moveOrStayTo (fun pair => (involution pair).1)
        (MeasurableMap.comp (Space.first_measurable state auxiliarySpace)
          involutionMeasurable)
        (involutiveAccept involution density)
        (involutiveAccept_measurable involution involutionMeasurable
          densityMeasurable) := by
  classical
  apply Kernel.ext
  intro pair
  apply Measure.ext
  intro set setMeasurable
  have indicatorMeasurable : ENNRealMeasurable state
      (ennrealIndicator set fun _ => ENNReal.one) :=
    ENNRealMeasurable.indicator setMeasurable (ENNRealMeasurable.constant _ _)
  unfold involutiveTest
  rw [Kernel.comp_apply, Measure.bind_deterministic _ _
      (involutiveDecision_measurable involution involutionMeasurable
        density densityMeasurable),
    Kernel.attach_apply, Kernel.const_apply, Measure.map_comp, Measure.map_apply _ _ _ setMeasurable,
    apply_eq_lintegral_indicator _ setMeasurable,
    lintegral_moveOrStayTo _ _ _ _ pair indicatorMeasurable]
  let event : Set UnitInterval := fun draw =>
    Dedekind.lt (Dedekind.mul draw.val (density pair)) (density (involution pair))
  have eventMeasurable : unitBorel.Measurable event :=
    measurable_lt
      (measurable_mul unitInclusion_measurable (MeasurableMap.constant _ _ _))
      (MeasurableMap.constant _ _ _)
  have accept : involutiveAccept involution density pair = uniform01 event := rfl
  have atMostOne := involutiveAccept_le_one involution density pair
  have region : Set.preimage
      (fun draw => involutiveDecision involution density (pair, draw)) set =
      fun draw => set (if event draw then (involution pair).1 else pair.1) := by
    apply Set.ext
    intro draw
    by_cases inside : event draw <;>
      simp [involutiveDecision, event, Set.preimage, inside]
  rw [region, accept]
  by_cases here : set (involution pair).1 <;> by_cases there : set pair.1
  · have whole : (fun draw => set
        (if event draw then (involution pair).1 else pair.1)) = Set.univ := by
      apply Set.ext
      intro draw
      by_cases inside : event draw <;> simp [inside, here, there, Set.univ]
    simp only [ennrealIndicator, ennrealPiecewise, here, there, ite_true,
      ENNReal.mul_one]
    rw [whole, uniform01_univ, ENNReal.add_comm, ENNReal.sub_add_cancel]
    rw [← accept]
    exact atMostOne
  · have exact : (fun draw => set
        (if event draw then (involution pair).1 else pair.1)) = event := by
      apply Set.ext
      intro draw
      by_cases inside : event draw <;> simp [inside, here, there]
    simp only [ennrealIndicator, ennrealPiecewise, here, there, ite_true,
      ite_false, ENNReal.mul_one, ENNReal.mul_zero, ENNReal.add_zero]
    rw [exact]
  · have rest : (fun draw => set
        (if event draw then (involution pair).1 else pair.1)) =
        Set.complement event := by
      apply Set.ext
      intro draw
      by_cases inside : event draw <;>
        simp [inside, here, there, Set.complement]
    simp only [ennrealIndicator, ennrealPiecewise, here, there, ite_true,
      ite_false, ENNReal.mul_one, ENNReal.mul_zero, ENNReal.zero_add]
    rw [rest, uniform01_isProbability.apply_complement eventMeasurable]
  · have nothing : (fun draw => set
        (if event draw then (involution pair).1 else pair.1)) = Set.empty := by
      apply Set.ext
      intro draw
      by_cases inside : event draw <;> simp [inside, here, there, Set.empty]
    simp only [ennrealIndicator, ennrealPiecewise, here, there, ite_false,
      ENNReal.mul_zero, ENNReal.add_zero]
    rw [nothing]
    exact Measure.empty_apply uniform01

/-- Draw an auxiliary value and a uniform coin, then make the involutive
accept/reject decision. This is the program a sampler runs. -/
@[expose] noncomputable def realizedInvolutiveStep
    (auxiliary : Kernel state auxiliarySpace)
    (auxiliaryFinite : Kernel.IsSFinite auxiliary)
    (involution : α × β → α × β)
    (involutionMeasurable :
      MeasurableMap (Space.product state auxiliarySpace)
        (Space.product state auxiliarySpace) involution)
    (density : α × β → Carrier)
    (densityMeasurable :
      MeasurableMap (Space.product state auxiliarySpace) borel density) :
    Kernel state state :=
  (Kernel.attach auxiliary auxiliaryFinite).comp
    (involutiveTest involution involutionMeasurable density densityMeasurable)

/-- The realized step law: drawing the auxiliary value and a uniform coin and
running the strict test has the law of `involutiveKernel` with the strict
acceptance. -/
theorem involutive_step_law
    (auxiliary : Kernel state auxiliarySpace)
    (auxiliaryFinite : Kernel.IsSFinite auxiliary)
    (involution : α × β → α × β)
    (involutionMeasurable :
      MeasurableMap (Space.product state auxiliarySpace)
        (Space.product state auxiliarySpace) involution)
    (density : α × β → Carrier)
    (densityMeasurable :
      MeasurableMap (Space.product state auxiliarySpace) borel density) :
    realizedInvolutiveStep auxiliary auxiliaryFinite involution
        involutionMeasurable density densityMeasurable =
      involutiveKernel auxiliary auxiliaryFinite involution involutionMeasurable
        (involutiveAccept involution density)
        (involutiveAccept_measurable involution involutionMeasurable
          densityMeasurable) := by
  unfold realizedInvolutiveStep involutiveKernel
  rw [involutiveTest_law]

/-- Refresh the second coordinate from a conditional kernel indexed by the
first coordinate. -/
@[expose] noncomputable def gibbsKernel
    {A : Type u} {B : Type v} {aSpace : Space A} {bSpace : Space B}
    (conditional : Kernel aSpace bSpace)
    (conditionalFinite : Kernel.IsSFinite conditional) :
    Kernel (Space.product aSpace bSpace) (Space.product aSpace bSpace) :=
  (Kernel.deterministic Prod.fst (Space.first_measurable aSpace bSpace)).comp
    (Kernel.attach conditional conditionalFinite)

@[expose] noncomputable def gibbsKernelSFinite
    {A : Type u} {B : Type v} {aSpace : Space A} {bSpace : Space B}
    {conditional : Kernel aSpace bSpace}
    (conditionalFinite : Kernel.IsSFinite conditional) :
    Kernel.IsSFinite (gibbsKernel conditional conditionalFinite) := by
  unfold gibbsKernel
  exact Kernel.IsSFinite.comp
    (Kernel.IsSFinite.deterministic _ _)
    (Kernel.IsSFinite.attach conditionalFinite)

/-- Conditional refresh preserves total mass when the conditional is
Markov. -/
theorem gibbsKernel_markov
    {A : Type u} {B : Type v} {aSpace : Space A} {bSpace : Space B}
    {conditional : Kernel aSpace bSpace}
    (conditionalFinite : Kernel.IsSFinite conditional)
    (conditionalMarkov : ∀ input, Measure.IsProbability (conditional input))
    (input : A × B) :
    Measure.IsProbability (gibbsKernel conditional conditionalFinite input) := by
  unfold gibbsKernel
  rw [Kernel.comp_apply, Kernel.deterministic_apply,
    Measure.dirac_bind, Kernel.attach_apply]
  exact (conditionalMarkov input.1).map _ _

/-- A conditional refresh leaves its semiproduct target invariant. -/
theorem gibbs_invariant
    {A : Type u} {B : Type v} {aSpace : Space A} {bSpace : Space B}
    (marginal : Measure aSpace) (conditional : Kernel aSpace bSpace)
    (conditionalFinite : Kernel.IsSFinite conditional)
    (conditionalMarkov : ∀ input, Measure.IsProbability (conditional input)) :
    KernelInvariant (marginal.semiproduct conditional conditionalFinite)
      (gibbsKernel conditional conditionalFinite) := by
  have firstMarginal :
      (marginal.semiproduct conditional conditionalFinite).map Prod.fst
        (Space.first_measurable aSpace bSpace) = marginal := by
    apply Measure.ext
    intro set setMeasurable
    rw [Measure.map_apply _ _ _ setMeasurable]
    have firstSet : Set.preimage (Prod.fst : A × B → A) set =
        Set.product set (Set.univ : Set B) := by
      apply Set.ext
      intro pair
      exact ⟨fun member => ⟨member, trivial⟩,
        fun member => member.1⟩
    rw [firstSet,
      Measure.semiproduct_apply_product marginal conditional conditionalFinite
        setMeasurable bSpace.univ]
    calc
      lintegral (marginal.restrict set)
          (fun input => conditional input Set.univ) =
        lintegral (marginal.restrict set) (fun _ => ENNReal.one) := by
          apply lintegral_congr
          intro input
          exact (conditionalMarkov input).univ_eq_one
      _ = marginal set := by
        rw [lintegral_const, Measure.restrict_apply_univ, ENNReal.one_mul]
  unfold KernelInvariant gibbsKernel
  rw [← Measure.bind_assoc, Measure.bind_deterministic, firstMarginal]
  rfl

/-- Integral of one conditional refresh: the first block stays and the second
is drawn from the conditional. -/
theorem lintegral_gibbsKernel
    {A : Type u} {B : Type v} {aSpace : Space A} {bSpace : Space B}
    (conditional : Kernel aSpace bSpace)
    (conditionalFinite : Kernel.IsSFinite conditional)
    (input : A × B) {function : A × B → ENNReal}
    (functionMeasurable :
      ENNRealMeasurable (Space.product aSpace bSpace) function) :
    lintegral (gibbsKernel conditional conditionalFinite input) function =
      lintegral (conditional input.1) (fun value => function (input.1, value)) := by
  unfold gibbsKernel
  rw [Kernel.comp_apply, Kernel.deterministic_apply, Measure.dirac_bind,
    Kernel.attach_apply, lintegral_map _ _ _ functionMeasurable]

/-- A conditional refresh is reversible for its semiproduct target: the old
and new second blocks are two independent draws from the same conditional. -/
theorem gibbs_detailed_balance
    {A : Type u} {B : Type v} {aSpace : Space A} {bSpace : Space B}
    (marginal : Measure aSpace) (conditional : Kernel aSpace bSpace)
    (conditionalFinite : Kernel.IsSFinite conditional)
    (conditionalMarkov : ∀ input, Measure.IsProbability (conditional input)) :
    DetailedBalance (marginal.semiproduct conditional conditionalFinite)
      (gibbsKernel conditional conditionalFinite)
      (gibbsKernelSFinite conditionalFinite) := by
  let pairSpace := Space.product aSpace bSpace
  let target := marginal.semiproduct conditional conditionalFinite
  let refresh := gibbsKernel conditional conditionalFinite
  have iterated : ∀ {function : (A × B) × (A × B) → ENNReal},
      ENNRealMeasurable (Space.product pairSpace pairSpace) function →
      lintegral (target.semiproduct refresh (gibbsKernelSFinite conditionalFinite))
          function =
        lintegral marginal (fun first => lintegral (conditional first)
          (fun old => lintegral (conditional first)
            (fun new => function ((first, old), (first, new))))) := by
    intro function functionMeasurable
    have innerMeasurable : ENNRealMeasurable pairSpace
        (fun pair => lintegral (refresh pair)
          (fun next => function (pair, next))) :=
      Kernel.lintegral_measurable_joint refresh
        (gibbsKernelSFinite conditionalFinite) functionMeasurable
    rw [lintegral_semiproduct _ _ _ functionMeasurable,
      lintegral_semiproduct _ _ _ innerMeasurable]
    apply lintegral_congr
    intro first
    apply lintegral_congr
    intro old
    exact lintegral_gibbsKernel conditional conditionalFinite (first, old)
      (functionMeasurable.comp (Kernel.pair_left_measurable (first, old)))
  unfold DetailedBalance
  apply Measure.ext
  intro set setMeasurable
  let indicator : (A × B) × (A × B) → ENNReal :=
    ennrealIndicator set fun _ => ENNReal.one
  have indicatorMeasurable :
      ENNRealMeasurable (Space.product pairSpace pairSpace) indicator :=
    ENNRealMeasurable.indicator setMeasurable (ENNRealMeasurable.constant _ _)
  rw [apply_eq_lintegral_indicator _ setMeasurable,
    apply_eq_lintegral_indicator _ setMeasurable,
    lintegral_map _ _ _ indicatorMeasurable,
    iterated (indicatorMeasurable.comp (Space.swap_measurable _ _)),
    iterated indicatorMeasurable]
  apply lintegral_congr
  intro first
  let draws := conditional first
  have drawsFinite : Measure.SFinite draws :=
    Measure.SFinite.ofFinite (conditionalMarkov first).to_finite
  let swapped : B × B → ENNReal := fun values =>
    indicator ((first, values.2), (first, values.1))
  have swappedMeasurable : ENNRealMeasurable (Space.product bSpace bSpace) swapped :=
    indicatorMeasurable.comp
      (Space.pair_measurable
        (Space.pair_measurable (MeasurableMap.constant _ _ first)
          (Space.second_measurable bSpace bSpace))
        (Space.pair_measurable (MeasurableMap.constant _ _ first)
          (Space.first_measurable bSpace bSpace)))
  calc
    lintegral draws (fun old => lintegral draws
        (fun new => indicator ((first, new), (first, old)))) =
      lintegral (Measure.prod draws draws drawsFinite) swapped :=
        (lintegral_prod draws draws drawsFinite swappedMeasurable).symm
    _ = lintegral draws (fun new => lintegral draws
          (fun old => indicator ((first, new), (first, old)))) :=
        lintegral_prod_symm draws draws drawsFinite drawsFinite swappedMeasurable

/-- Refreshing the second block from the conditional kernel of a joint density
leaves the joint density invariant when fiber masses are finite almost
everywhere under the base measure. -/
theorem gibbs_densityConditional_invariant
    {A : Type u} {B : Type v} {aSpace : Space A} {bSpace : Space B}
    (base : Measure aSpace) (reference : Measure bSpace)
    (referenceFinite : Measure.SFinite reference) {density : A → B → ENNReal}
    (densityMeasurable : ENNRealMeasurable (Space.product aSpace bSpace)
      (fun pair => density pair.1 pair.2))
    (fallback : B)
    (finite : base.AE (fun input =>
      ENNReal.Finite (Kernel.densityMass reference density input))) :
    KernelInvariant
      ((Measure.prod base reference referenceFinite).withDensity
        (fun pair => density pair.1 pair.2))
      (gibbsKernel
        (Kernel.densityConditional reference referenceFinite density densityMeasurable fallback)
        (Kernel.densityConditional_isFinite reference referenceFinite densityMeasurable
          fallback).toSFinite) := by
  rw [← Kernel.semiproduct_densityConditional base reference referenceFinite densityMeasurable
    fallback finite]
  exact gibbs_invariant _ _ _
    (Kernel.densityConditional_isProbability reference referenceFinite densityMeasurable
      fallback)

/-- Refreshing the second block from the conditional kernel of a joint density
is reversible for the joint density when fiber masses are finite almost
everywhere under the base measure. -/
theorem gibbs_densityConditional_detailed_balance
    {A : Type u} {B : Type v} {aSpace : Space A} {bSpace : Space B}
    (base : Measure aSpace) (reference : Measure bSpace)
    (referenceFinite : Measure.SFinite reference) {density : A → B → ENNReal}
    (densityMeasurable : ENNRealMeasurable (Space.product aSpace bSpace)
      (fun pair => density pair.1 pair.2))
    (fallback : B)
    (finite : base.AE (fun input =>
      ENNReal.Finite (Kernel.densityMass reference density input))) :
    DetailedBalance
      ((Measure.prod base reference referenceFinite).withDensity
        (fun pair => density pair.1 pair.2))
      (gibbsKernel
        (Kernel.densityConditional reference referenceFinite density densityMeasurable fallback)
        (Kernel.densityConditional_isFinite reference referenceFinite densityMeasurable
          fallback).toSFinite)
      (gibbsKernelSFinite (Kernel.densityConditional_isFinite reference referenceFinite
        densityMeasurable fallback).toSFinite) := by
  rw [← Kernel.semiproduct_densityConditional base reference referenceFinite densityMeasurable
    fallback finite]
  exact gibbs_detailed_balance _ _ _
    (Kernel.densityConditional_isProbability reference referenceFinite densityMeasurable
      fallback)

/-- A tagged-sum reversible-jump step. Move selection and dimension-matching
draws live in `auxiliary`. The density is taken against a reference that the
involution preserves, so a Jacobian, where one applies, is part of it. -/
theorem reversible_jump_invariant
    {γ : Type w} {left : Space α} {right : Space γ}
    (target : Measure (Space.sum left right))
    (auxiliary : Kernel (Space.sum left right) auxiliarySpace)
    (auxiliaryFinite : Kernel.IsSFinite auxiliary)
    (auxiliaryMarkov : ∀ input, Measure.IsProbability (auxiliary input))
    (involution : (Sum α γ) × β → (Sum α γ) × β)
    (involutionMeasurable : MeasurableMap _ _ involution)
    (involutive : ∀ point, involution (involution point) = point)
    (reference : Measure (Space.product (Space.sum left right) auxiliarySpace))
    (referenceInvariant :
      reference.map involution involutionMeasurable = reference)
    {density : (Sum α γ) × β → Carrier}
    (densityMeasurable : MeasurableMap _ borel density)
    (represents : target.semiproduct auxiliary auxiliaryFinite =
      reference.withDensity (fun point => ENNReal.ofReal (density point))) :
    KernelInvariant target
      (involutiveKernel auxiliary auxiliaryFinite involution involutionMeasurable
        (involutiveAccept involution density)
        (involutiveAccept_measurable involution involutionMeasurable
          densityMeasurable)) :=
  involutive_invariant_of_reference target auxiliary auxiliaryFinite
    auxiliaryMarkov involution involutionMeasurable involutive reference
    referenceInvariant densityMeasurable represents

/-- A reversible integrator supplies a measurable, involutive proposal on
position and momentum. Its reference equation records volume preservation;
the density premise of `involutive_invariant` may also carry a correction. -/
public structure ReversibleIntegrator (position : Space α) (momentum : Space β)
    (reference : Measure (Space.product position momentum)) where
  integrate : α × β → α × β
  integrateMeasurable :
    MeasurableMap (Space.product position momentum)
      (Space.product position momentum) integrate
  flip : α × β → α × β
  flipMeasurable :
    MeasurableMap (Space.product position momentum)
      (Space.product position momentum) flip
  involutive : ∀ point, flip (integrate (flip (integrate point))) = point
  referenceInvariant :
    reference.map (fun point => flip (integrate point))
      (MeasurableMap.comp flipMeasurable integrateMeasurable) = reference

@[expose] def ReversibleIntegrator.trajectory
    {reference : Measure (Space.product state auxiliarySpace)}
    (integrator : ReversibleIntegrator state auxiliarySpace reference)
    (point : α × β) : α × β :=
  integrator.flip (integrator.integrate point)

theorem ReversibleIntegrator.trajectory_measurable
    {reference : Measure (Space.product state auxiliarySpace)}
    (integrator : ReversibleIntegrator state auxiliarySpace reference) :
    MeasurableMap (Space.product state auxiliarySpace)
      (Space.product state auxiliarySpace) integrator.trajectory :=
  MeasurableMap.comp integrator.flipMeasurable integrator.integrateMeasurable

theorem ReversibleIntegrator.trajectory_involutive
    {reference : Measure (Space.product state auxiliarySpace)}
    (integrator : ReversibleIntegrator state auxiliarySpace reference)
    (point : α × β) :
    integrator.trajectory (integrator.trajectory point) = point :=
  integrator.involutive point

/-- Extend an HMC trajectory across a unit auxiliary draw. -/
@[expose] def hmcTrajectory
    {reference : Measure (Space.product state auxiliarySpace)}
    (integrator : ReversibleIntegrator state auxiliarySpace reference)
    (pair : (α × β) × Unit) : (α × β) × Unit :=
  (integrator.trajectory pair.1, pair.2)

theorem hmcTrajectory_measurable
    {reference : Measure (Space.product state auxiliarySpace)}
    (integrator : ReversibleIntegrator state auxiliarySpace reference)
    (unitSpace : Space Unit) :
    MeasurableMap
      (Space.product (Space.product state auxiliarySpace) unitSpace)
      (Space.product (Space.product state auxiliarySpace) unitSpace)
      (hmcTrajectory integrator) :=
  Space.pair_measurable
    (MeasurableMap.comp integrator.trajectory_measurable
      (Space.first_measurable _ _))
    (Space.second_measurable _ _)

theorem hmcTrajectory_involutive
    {reference : Measure (Space.product state auxiliarySpace)}
    (integrator : ReversibleIntegrator state auxiliarySpace reference)
    (pair : (α × β) × Unit) :
    hmcTrajectory integrator (hmcTrajectory integrator pair) = pair := by
  cases pair with
  | mk joint unitValue =>
      change (integrator.trajectory (integrator.trajectory joint), unitValue) =
        (joint, unitValue)
      rw [integrator.trajectory_involutive joint]

/-- Attach the unit value to a state. -/
@[expose] def attachUnit (point : α × β) : (α × β) × Unit := (point, ())

theorem attachUnit_measurable (unitSpace : Space Unit) :
    MeasurableMap (Space.product state auxiliarySpace)
      (Space.product (Space.product state auxiliarySpace) unitSpace)
      (attachUnit (α := α) (β := β)) :=
  Space.pair_measurable (MeasurableMap.identity _)
    (MeasurableMap.constant _ _ ())

/-- A Markov draw of the unit value only attaches it. -/
private theorem semiproduct_unit
    (measure : Measure (Space.product state auxiliarySpace))
    (unitSpace : Space Unit)
    (unitProposal : Kernel (Space.product state auxiliarySpace) unitSpace)
    (unitFinite : Kernel.IsSFinite unitProposal)
    (unitMarkov : ∀ input, Measure.IsProbability (unitProposal input)) :
    measure.semiproduct unitProposal unitFinite =
      measure.map attachUnit (attachUnit_measurable unitSpace) := by
  classical
  apply Measure.ext
  intro set setMeasurable
  rw [Measure.semiproduct_apply _ _ _ setMeasurable,
    Measure.map_apply _ _ _ setMeasurable,
    apply_eq_lintegral_indicator _
      ((attachUnit_measurable unitSpace) setMeasurable)]
  apply lintegral_congr
  intro point
  by_cases inside : set (point, ())
  · have whole : Set.preimage (fun value : Unit => (point, value)) set =
        Set.univ := by
      apply Set.ext
      intro value
      cases value
      exact ⟨fun _ => True.intro, fun _ => inside⟩
    rw [whole, (unitMarkov point).univ_eq_one]
    simp [ennrealIndicator, ennrealPiecewise, attachUnit, Set.preimage, inside]
  · have none : Set.preimage (fun value : Unit => (point, value)) set =
        Set.empty := by
      apply Set.ext
      intro value
      cases value
      exact ⟨fun member => absurd member inside, fun member => False.elim member⟩
    rw [none, Measure.empty_apply]
    simp [ennrealIndicator, ennrealPiecewise, attachUnit, Set.preimage, inside]

/-- Attaching the unit value carries a density along. -/
private theorem map_attachUnit_withDensity
    (measure : Measure (Space.product state auxiliarySpace))
    (unitSpace : Space Unit)
    {density : α × β → ENNReal}
    (densityMeasurable :
      ENNRealMeasurable (Space.product state auxiliarySpace) density) :
    (measure.withDensity density).map attachUnit
        (attachUnit_measurable unitSpace) =
      (measure.map attachUnit (attachUnit_measurable unitSpace)).withDensity
        (fun point => density point.1) := by
  apply Measure.ext
  intro set setMeasurable
  let indicator : (α × β) × Unit → ENNReal :=
    ennrealIndicator set fun _ => ENNReal.one
  have indicatorMeasurable : ENNRealMeasurable
      (Space.product (Space.product state auxiliarySpace) unitSpace) indicator :=
    ENNRealMeasurable.indicator setMeasurable (ENNRealMeasurable.constant _ _)
  have firstMeasurable : ENNRealMeasurable
      (Space.product (Space.product state auxiliarySpace) unitSpace)
      (fun point : (α × β) × Unit => density point.1) :=
    densityMeasurable.comp (Space.first_measurable _ _)
  rw [apply_eq_lintegral_indicator _ setMeasurable,
    apply_eq_lintegral_indicator _ setMeasurable,
    lintegral_map _ _ _ indicatorMeasurable,
    lintegral_withDensity _ densityMeasurable
      (indicatorMeasurable.comp (attachUnit_measurable unitSpace)),
    lintegral_withDensity _ firstMeasurable indicatorMeasurable,
    lintegral_map _ _ _
      (ENNRealMeasurable.mul firstMeasurable indicatorMeasurable)]
  rfl

/-- A conditional momentum refresh followed by a reversible integrator step
preserves the joint target. The joint target has a density against the
integrator's preserved volume, so no Jacobian appears. This states no
recurrence claim. -/
theorem hmc_invariant
    (positionLaw : Measure state)
    (momentum : Kernel state auxiliarySpace)
    (momentumFinite : Kernel.IsSFinite momentum)
    (momentumMarkov : ∀ input, Measure.IsProbability (momentum input))
    (volume : Measure (Space.product state auxiliarySpace))
    (integrator : ReversibleIntegrator state auxiliarySpace volume)
    (unitSpace : Space Unit)
    (unitProposal : Kernel (Space.product state auxiliarySpace) unitSpace)
    (unitFinite : Kernel.IsSFinite unitProposal)
    (unitMarkov : ∀ input, Measure.IsProbability (unitProposal input))
    {density : α × β → Carrier}
    (densityMeasurable :
      MeasurableMap (Space.product state auxiliarySpace) borel density)
    (represents : positionLaw.semiproduct momentum momentumFinite =
      volume.withDensity (fun point => ENNReal.ofReal (density point))) :
    KernelInvariant (positionLaw.semiproduct momentum momentumFinite)
      ((gibbsKernel momentum momentumFinite).comp
        (involutiveKernel unitProposal unitFinite
          (hmcTrajectory integrator)
          (hmcTrajectory_measurable integrator unitSpace)
          (involutiveAccept (hmcTrajectory integrator)
            (fun point => density point.1))
          (involutiveAccept_measurable (hmcTrajectory integrator)
            (hmcTrajectory_measurable integrator unitSpace)
            (densityMeasurable.comp (Space.first_measurable _ _))))) := by
  let lifted := volume.map attachUnit (attachUnit_measurable unitSpace)
  have liftedInvariant : lifted.map (hmcTrajectory integrator)
      (hmcTrajectory_measurable integrator unitSpace) = lifted := by
    calc
      lifted.map (hmcTrajectory integrator)
          (hmcTrajectory_measurable integrator unitSpace) =
        (volume.map integrator.trajectory
          integrator.trajectory_measurable).map attachUnit
          (attachUnit_measurable unitSpace) := by
        rw [Measure.map_comp, Measure.map_comp]
        rfl
      _ = lifted := by
        change (volume.map (fun point => integrator.flip (integrator.integrate point))
          (MeasurableMap.comp integrator.flipMeasurable
            integrator.integrateMeasurable)).map attachUnit
          (attachUnit_measurable unitSpace) = lifted
        rw [integrator.referenceInvariant]
  have extended : (positionLaw.semiproduct momentum momentumFinite).semiproduct
      unitProposal unitFinite =
      lifted.withDensity (fun point => ENNReal.ofReal (density point.1)) := by
    rw [semiproduct_unit _ unitSpace unitProposal unitFinite unitMarkov,
      represents,
      map_attachUnit_withDensity _ unitSpace
        (ofReal_measurable.comp densityMeasurable)]
  have trajectoryInvariant := involutive_invariant_of_reference
    (positionLaw.semiproduct momentum momentumFinite)
    unitProposal unitFinite unitMarkov
    (hmcTrajectory integrator)
    (hmcTrajectory_measurable integrator unitSpace)
    (hmcTrajectory_involutive integrator)
    lifted liftedInvariant
    (densityMeasurable.comp (Space.first_measurable _ _)) extended
  exact kernel_invariant_comp
    (gibbs_invariant positionLaw momentum momentumFinite momentumMarkov)
    trajectoryInvariant

end
end Problib.Inference
