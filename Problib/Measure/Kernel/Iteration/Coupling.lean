module

public import Problib.Measure.Kernel.Subtract
public import Problib.Measure.Kernel.Product.Parallel
public import Problib.Measure.Kernel.Iteration.SmallSet
public import Problib.Measure.Kernel.Piecewise
public import Problib.Measure.Kernel.Sum
public import Problib.Measure.Kernel.Scale
import Problib.Measure.Integral.Lebesgue.Algebra
import Problib.Measure.Integral.Lebesgue.Transport
public import Problib.Measure.Kernel.Iteration.Termination
import Problib.Measure.Integral.Lebesgue.Measure

set_option autoImplicit false

/-!
# The small-set coupling

A one-step minorization on `region` splits each fiber there into a shared part,
`weight` times the reference law, and a residual. Two copies of the chain then
run on the pair space. When both copies stand in `region` at the same time,
they couple with probability `weight` by moving together to one draw from the
reference law. Otherwise they move by the normalized product of residuals, and
pairs outside `region × region` move independently. A coupled state moves by
the kernel itself. Each coordinate of the pair chain is a copy of the original
chain, and the mass still uncoupled bounds the total variation between them.
-/

namespace Problib.Measure.Kernel

open Problib.Real

universe u
variable {α : Type u} {space : Space α}
  {kernel : Kernel space space} {region : Set α}
  {weight : NNReal} {reference : Giry.Law space}

/-- The mass shared by all fibers inside the region. -/
@[expose] public noncomputable def minorant (region : Set α)
    (measurable : space.Measurable region) (weight : NNReal)
    (reference : Giry.Law space) : Kernel space space :=
  piecewise region measurable
    (Kernel.const space (Measure.smul (ENNReal.finite weight) reference.val))
    (Kernel.zero space space)

public theorem minorant_apply_of_mem (measurable : space.Measurable region)
    (weight : NNReal) (reference : Giry.Law space) {input : α}
    (member : region input) :
    minorant region measurable weight reference input =
      Measure.smul (ENNReal.finite weight) reference.val := by
  rw [minorant, piecewise_apply_of_mem _ _ _ _ _ member, Kernel.const_apply]

public theorem minorant_apply_of_not_mem (measurable : space.Measurable region)
    (weight : NNReal) (reference : Giry.Law space) {input : α}
    (outside : ¬ region input) :
    minorant region measurable weight reference input = Measure.zero space := by
  rw [minorant, piecewise_apply_of_not_mem _ _ _ _ _ outside, Kernel.zero_apply]

public theorem minorant_isFinite (measurable : space.Measurable region)
    (weight : NNReal) (reference : Giry.Law space) (input : α) :
    Measure.IsFinite (minorant region measurable weight reference input) := by
  by_cases member : region input
  · rw [minorant_apply_of_mem measurable weight reference member]
    exact Measure.IsFinite.smul _ True.intro reference.property.to_finite
  · rw [minorant_apply_of_not_mem measurable weight reference member]
    exact Measure.IsFinite.zero space

public theorem minorant_le (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) :
    Kernel.le (minorant region measurable weight reference) kernel := by
  intro input event eventMeasurable
  by_cases member : region input
  · rw [minorant_apply_of_mem measurable weight reference member]
    have lower := minor.lower input member event eventMeasurable
    rw [iterate_one] at lower
    exact lower
  · rw [minorant_apply_of_not_mem measurable weight reference member,
      Measure.zero_apply]
    exact ENNReal.zero_le _

/-- The fibers with the shared mass removed inside the region. Outside the
region they are the original fibers. -/
@[expose] public noncomputable def residual
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) : Kernel space space :=
  Kernel.subtract (minorant_isFinite measurable weight reference)
    (minorant_le minor measurable)

public theorem residual_add_minorant
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) :
    Kernel.add (residual minor measurable)
      (minorant region measurable weight reference) = kernel :=
  Kernel.subtract_add _ _

public theorem residual_le (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) :
    Kernel.le (residual minor measurable) kernel :=
  Kernel.subtract_le _ _

public theorem residual_isFinite
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) (input : α) :
    Measure.IsFinite (residual minor measurable input) :=
  (minor.markov input).to_finite.of_le
    (residual_le minor measurable input Set.univ space.univ)

public theorem residual_apply_of_not_mem
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) {input : α}
    (outside : ¬ region input) :
    residual minor measurable input = kernel input := by
  have fiber := congrArg (fun current => current input)
    (residual_add_minorant minor measurable)
  simp only [Kernel.add_apply,
    minorant_apply_of_not_mem measurable weight reference outside,
    Measure.add_zero] at fiber
  exact fiber

public theorem residual_mass
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) {input : α}
    (member : region input) :
    residual minor measurable input Set.univ =
      ENNReal.sub ENNReal.one (ENNReal.finite weight) := by
  rw [residual, Kernel.subtract_apply _ _ input space.univ,
    minorant_apply_of_mem measurable weight reference member,
    Measure.smul_apply_measurable _ _ space.univ,
    reference.property.univ_eq_one, ENNReal.mul_one,
    (minor.markov input).univ_eq_one]

public theorem residual_add_minorant_apply
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) (input : α) {event : Set α}
    (eventMeasurable : space.Measurable event) :
    kernel input event =
      ENNReal.add (residual minor measurable input event)
        (minorant region measurable weight reference input event) := by
  calc
    kernel input event =
        Kernel.add (residual minor measurable)
          (minorant region measurable weight reference) input event := by
      rw [residual_add_minorant minor measurable]
    _ = ENNReal.add (residual minor measurable input event)
          (minorant region measurable weight reference input event) := by
      rw [Kernel.add_apply, Measure.add_apply_measurable _ _ eventMeasurable]

/-- At full weight nothing is left once the shared mass is removed. -/
public theorem residual_eq_zero
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) (full : weight = NNReal.one)
    {input : α} (member : region input) :
    residual minor measurable input = Measure.zero space := by
  apply (Measure.eq_zero_iff_univ_eq_zero _).mpr
  rw [residual_mass minor measurable member, full]
  exact ENNReal.sub_self ENNReal.one

/-- Uncoupled pairs sit on the left summand and coupled states on the right. -/
public abbrev couplingSpace (space : Space α) : Space (Sum (α × α) α) :=
  Space.sum (Space.product space space) space

@[expose] public def couplingFirst : Sum (α × α) α → α :=
  Sum.elim Prod.fst (fun value => value)

@[expose] public def couplingSecond : Sum (α × α) α → α :=
  Sum.elim Prod.snd (fun value => value)

@[expose] public def uncoupledStates : Set (Sum (α × α) α) :=
  fun state => ∃ pair, state = Sum.inl pair

public theorem couplingFirst_measurable (space : Space α) :
    MeasurableMap (couplingSpace space) space couplingFirst :=
  MeasurableMap.sum_elim (Space.first_measurable space space)
    (MeasurableMap.identity space)

public theorem couplingSecond_measurable (space : Space α) :
    MeasurableMap (couplingSpace space) space couplingSecond :=
  MeasurableMap.sum_elim (Space.second_measurable space space)
    (MeasurableMap.identity space)

public theorem uncoupledStates_measurable (space : Space α) :
    (couplingSpace space).Measurable uncoupledStates := by
  have left : Set.preimage Sum.inl (uncoupledStates (α := α)) = Set.univ := by
    apply Set.ext
    intro pair
    exact ⟨fun _ => True.intro, fun _ => ⟨pair, rfl⟩⟩
  have right : Set.preimage Sum.inr (uncoupledStates (α := α)) = Set.empty := by
    apply Set.ext
    intro value
    constructor
    · rintro ⟨pair, equal⟩
      cases equal
    · exact False.elim
  refine (Space.sum_measurable_iff _ _ _).mpr ⟨?_, ?_⟩
  · rw [left]
    exact (Space.product space space).univ
  · rw [right]
    exact space.empty

/-- The normalizing factor of the residual product after a failed trial. At
full weight the residual product is zero, so this value never multiplies
positive mass. -/
@[expose] public noncomputable def failureScale (weight : NNReal) : ENNReal :=
  ENNReal.finite (NNReal.div NNReal.one (NNReal.sub NNReal.one weight))

/-- Normalizing one residual mass away. The value must vanish at full weight. -/
public theorem failureScale_cancel {weight : NNReal}
    (atMostOne : NNReal.le weight NNReal.one) (value : ENNReal)
    (vanishes : weight = NNReal.one → value = ENNReal.zero) :
    ENNReal.mul (failureScale weight)
        (ENNReal.mul (ENNReal.sub ENNReal.one (ENNReal.finite weight)) value) =
      value := by
  by_cases full : weight = NNReal.one
  · rw [vanishes full, ENNReal.mul_zero, ENNReal.mul_zero]
  · have nonzero : NNReal.sub NNReal.one weight ≠ NNReal.zero := by
      intro zero
      exact full (NNReal.le_antisymm atMostOne (NNReal.sub_eq_zero_iff_le.mp zero))
    rw [← ENNReal.mul_assoc]
    change ENNReal.mul
      (ENNReal.mul (ENNReal.finite (NNReal.div NNReal.one (NNReal.sub NNReal.one weight)))
        (ENNReal.finite (NNReal.sub NNReal.one weight))) value = value
    rw [ENNReal.finite_mul_finite, NNReal.div_mul_cancel _ nonzero]
    exact ENNReal.one_mul value

/-- The coupling trial: from `region × region`, both coordinates coupling
at one draw from the reference law, or moving by the normalized residual
product. -/
@[expose] public noncomputable def couplingTrial
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) :
    Kernel (Space.product space space) (couplingSpace space) :=
  Kernel.add
    (Kernel.const (Space.product space space)
      ((Measure.smul (ENNReal.finite weight) reference.val).map Sum.inr
        (MeasurableMap.inr (Space.product space space) space)))
    ((Kernel.smul (failureScale weight)
      (parallel (residual minor measurable) (residual minor measurable)
        (residual_isFinite minor measurable)
        (residual_isFinite minor measurable))).map
      Sum.inl (MeasurableMap.inl (Space.product space space) space))

/-- Two copies of the chain, trying to couple whenever both stand in the
region. -/
@[expose] public noncomputable def couplingKernel
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) :
    Kernel (couplingSpace space) (couplingSpace space) :=
  Kernel.copair
    (piecewise (Set.product region region)
      (Space.product_set_measurable space space measurable measurable)
      (couplingTrial minor measurable)
      ((parallel kernel kernel (fun input => (minor.markov input).to_finite)
          (fun input => (minor.markov input).to_finite)).map
        Sum.inl (MeasurableMap.inl (Space.product space space) space)))
    (kernel.map Sum.inr (MeasurableMap.inr (Space.product space space) space))

public theorem couplingKernel_inr
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) (value : α) :
    couplingKernel minor measurable (Sum.inr value) =
      (kernel value).map Sum.inr
        (MeasurableMap.inr (Space.product space space) space) := by
  rw [couplingKernel, copair_inr, Kernel.map_apply]

public theorem couplingKernel_inl_of_mem
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) {pair : α × α}
    (member : Set.product region region pair) :
    couplingKernel minor measurable (Sum.inl pair) =
      couplingTrial minor measurable pair := by
  rw [couplingKernel, copair_inl, piecewise_apply_of_mem _ _ _ _ _ member]

public theorem couplingKernel_inl_of_not_mem
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) {pair : α × α}
    (outside : ¬ Set.product region region pair) :
    couplingKernel minor measurable (Sum.inl pair) =
      (parallel kernel kernel (fun input => (minor.markov input).to_finite)
          (fun input => (minor.markov input).to_finite) pair).map
        Sum.inl (MeasurableMap.inl (Space.product space space) space) := by
  rw [couplingKernel, copair_inl, piecewise_apply_of_not_mem _ _ _ _ _ outside,
    Kernel.map_apply]

/-- The trial evaluated on a measurable set of coupling states. -/
private theorem couplingTrial_apply
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) (pair : α × α)
    {event : Set (Sum (α × α) α)}
    (eventMeasurable : (couplingSpace space).Measurable event) :
    couplingTrial minor measurable pair event =
      ENNReal.add
        (ENNReal.mul (ENNReal.finite weight)
          (reference.val (Set.preimage Sum.inr event)))
        (ENNReal.mul (failureScale weight)
          (parallel (residual minor measurable) (residual minor measurable)
            (residual_isFinite minor measurable)
            (residual_isFinite minor measurable) pair
            (Set.preimage Sum.inl event))) := by
  have inrMeasurable := MeasurableMap.inr (Space.product space space) space
    eventMeasurable
  have inlMeasurable := MeasurableMap.inl (Space.product space space) space
    eventMeasurable
  rw [couplingTrial, Kernel.add_apply,
    Measure.add_apply_measurable _ _ eventMeasurable, Kernel.const_apply,
    Kernel.map_apply _ _ (MeasurableMap.inl (Space.product space space) space),
    Measure.map_apply _ _ (MeasurableMap.inr (Space.product space space) space)
      eventMeasurable,
    Measure.map_apply _ _ (MeasurableMap.inl (Space.product space space) space)
      eventMeasurable,
    Measure.smul_apply_measurable _ _ inrMeasurable, Kernel.smul_apply,
    Measure.smul_apply_measurable _ _ inlMeasurable]

public theorem couplingKernel_isProbability
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) (state : Sum (α × α) α) :
    Measure.IsProbability (couplingKernel minor measurable state) := by
  constructor
  cases state with
  | inr value =>
      rw [couplingKernel_inr, Measure.map_apply _ _ _ (couplingSpace space).univ]
      exact (minor.markov value).univ_eq_one
  | inl pair =>
      by_cases member : Set.product region region pair
      · rw [couplingKernel_inl_of_mem minor measurable member,
          couplingTrial_apply minor measurable pair (couplingSpace space).univ]
        have residualMass : parallel (residual minor measurable)
            (residual minor measurable) (residual_isFinite minor measurable)
            (residual_isFinite minor measurable) pair
            (Set.preimage (Sum.inl (β := α)) (Set.univ : Set (Sum (α × α) α))) =
            ENNReal.mul (ENNReal.sub ENNReal.one (ENNReal.finite weight))
              (ENNReal.sub ENNReal.one (ENNReal.finite weight)) := by
          have marginal := congrArg (fun measure => measure Set.univ)
            (parallel_map_fst (residual minor measurable)
              (residual minor measurable) (residual_isFinite minor measurable)
              (residual_isFinite minor measurable) pair)
          rw [Measure.map_apply _ _ _ space.univ,
            Measure.smul_apply_measurable _ _ space.univ,
            residual_mass minor measurable member.1,
            residual_mass minor measurable member.2] at marginal
          exact marginal
        change ENNReal.add
            (ENNReal.mul (ENNReal.finite weight) (reference.val Set.univ))
            (ENNReal.mul (failureScale weight)
              (parallel (residual minor measurable) (residual minor measurable)
                (residual_isFinite minor measurable)
                (residual_isFinite minor measurable) pair
                (Set.preimage (Sum.inl (β := α))
                  (Set.univ : Set (Sum (α × α) α))))) = ENNReal.one
        rw [residualMass,
          failureScale_cancel minor.weightAtMostOne _ (fun full => by
            rw [full]
            exact ENNReal.sub_self ENNReal.one),
          reference.property.univ_eq_one, ENNReal.mul_one, ENNReal.add_comm]
        exact ENNReal.sub_add_cancel minor.weightAtMostOne
      · rw [couplingKernel_inl_of_not_mem minor measurable member,
          Measure.map_apply _ _ _ (couplingSpace space).univ]
        have marginal := congrArg (fun measure => measure Set.univ)
          (parallel_map_fst kernel kernel
            (fun input => (minor.markov input).to_finite)
            (fun input => (minor.markov input).to_finite) pair)
        rw [Measure.map_apply _ _ _ space.univ,
          Measure.smul_apply_measurable _ _ space.univ,
          (minor.markov pair.1).univ_eq_one,
          (minor.markov pair.2).univ_eq_one, ENNReal.mul_one] at marginal
        exact marginal

/-- On a measurable event, the first coordinate's step from a trial pair is
the shared mass plus the first residual. -/
private theorem couplingTrial_first
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) {pair : α × α}
    (member : Set.product region region pair) {event : Set α}
    (eventMeasurable : space.Measurable event) :
    couplingTrial minor measurable pair (Set.preimage couplingFirst event) =
      kernel pair.1 event := by
  rw [couplingTrial_apply minor measurable pair
    (couplingFirst_measurable space eventMeasurable)]
  have marginal := congrArg (fun measure => measure event)
    (parallel_map_fst (residual minor measurable) (residual minor measurable)
      (residual_isFinite minor measurable) (residual_isFinite minor measurable)
      pair)
  rw [Measure.map_apply _ _ _ eventMeasurable,
    Measure.smul_apply_measurable _ _ eventMeasurable,
    residual_mass minor measurable member.2] at marginal
  change ENNReal.add
      (ENNReal.mul (ENNReal.finite weight) (reference.val event))
      (ENNReal.mul (failureScale weight)
        (parallel (residual minor measurable) (residual minor measurable)
          (residual_isFinite minor measurable)
          (residual_isFinite minor measurable) pair
          (Set.preimage Prod.fst event))) = kernel pair.1 event
  rw [marginal, failureScale_cancel minor.weightAtMostOne _ (fun full => by
    rw [residual_eq_zero minor measurable full member.1, Measure.zero_apply])]
  have fiber := residual_add_minorant_apply minor measurable pair.1 eventMeasurable
  rw [minorant_apply_of_mem measurable weight reference member.1,
    Measure.smul_apply_measurable _ _ eventMeasurable] at fiber
  rw [ENNReal.add_comm]
  exact fiber.symm

private theorem couplingTrial_second
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) {pair : α × α}
    (member : Set.product region region pair) {event : Set α}
    (eventMeasurable : space.Measurable event) :
    couplingTrial minor measurable pair (Set.preimage couplingSecond event) =
      kernel pair.2 event := by
  rw [couplingTrial_apply minor measurable pair
    (couplingSecond_measurable space eventMeasurable)]
  have marginal := congrArg (fun measure => measure event)
    (parallel_map_snd (residual minor measurable) (residual minor measurable)
      (residual_isFinite minor measurable) (residual_isFinite minor measurable)
      pair)
  rw [Measure.map_apply _ _ _ eventMeasurable,
    Measure.smul_apply_measurable _ _ eventMeasurable,
    residual_mass minor measurable member.1] at marginal
  change ENNReal.add
      (ENNReal.mul (ENNReal.finite weight) (reference.val event))
      (ENNReal.mul (failureScale weight)
        (parallel (residual minor measurable) (residual minor measurable)
          (residual_isFinite minor measurable)
          (residual_isFinite minor measurable) pair
          (Set.preimage Prod.snd event))) = kernel pair.2 event
  rw [marginal, failureScale_cancel minor.weightAtMostOne _ (fun full => by
    rw [residual_eq_zero minor measurable full member.2, Measure.zero_apply])]
  have fiber := residual_add_minorant_apply minor measurable pair.2 eventMeasurable
  rw [minorant_apply_of_mem measurable weight reference member.2,
    Measure.smul_apply_measurable _ _ eventMeasurable] at fiber
  rw [ENNReal.add_comm]
  exact fiber.symm

/-- The first coordinate of the coupling moves as the chain. -/
public theorem couplingKernel_first
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) :
    (couplingKernel minor measurable).comp
        (Kernel.deterministic couplingFirst (couplingFirst_measurable space)) =
      (Kernel.deterministic couplingFirst (couplingFirst_measurable space)).comp
        kernel := by
  apply Kernel.ext_measurable
  intro state event eventMeasurable
  rw [comp_deterministic, Kernel.map_apply,
    Measure.map_apply _ _ _ eventMeasurable, deterministic_comp_apply]
  cases state with
  | inr value =>
      rw [couplingKernel_inr, Measure.map_apply _ _ _
        (couplingFirst_measurable space eventMeasurable)]
      rfl
  | inl pair =>
      by_cases member : Set.product region region pair
      · rw [couplingKernel_inl_of_mem minor measurable member]
        exact couplingTrial_first minor measurable member eventMeasurable
      · rw [couplingKernel_inl_of_not_mem minor measurable member,
          Measure.map_apply _ _ _
            (couplingFirst_measurable space eventMeasurable)]
        have marginal := congrArg (fun measure => measure event)
          (parallel_map_fst kernel kernel
            (fun input => (minor.markov input).to_finite)
            (fun input => (minor.markov input).to_finite) pair)
        rw [Measure.map_apply _ _ _ eventMeasurable,
          Measure.smul_apply_measurable _ _ eventMeasurable,
          (minor.markov pair.2).univ_eq_one, ENNReal.one_mul] at marginal
        exact marginal

/-- The second coordinate of the coupling moves as the chain. -/
public theorem couplingKernel_second
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) :
    (couplingKernel minor measurable).comp
        (Kernel.deterministic couplingSecond (couplingSecond_measurable space)) =
      (Kernel.deterministic couplingSecond (couplingSecond_measurable space)).comp
        kernel := by
  apply Kernel.ext_measurable
  intro state event eventMeasurable
  rw [comp_deterministic, Kernel.map_apply,
    Measure.map_apply _ _ _ eventMeasurable, deterministic_comp_apply]
  cases state with
  | inr value =>
      rw [couplingKernel_inr, Measure.map_apply _ _ _
        (couplingSecond_measurable space eventMeasurable)]
      rfl
  | inl pair =>
      by_cases member : Set.product region region pair
      · rw [couplingKernel_inl_of_mem minor measurable member]
        exact couplingTrial_second minor measurable member eventMeasurable
      · rw [couplingKernel_inl_of_not_mem minor measurable member,
          Measure.map_apply _ _ _
            (couplingSecond_measurable space eventMeasurable)]
        have marginal := congrArg (fun measure => measure event)
          (parallel_map_snd kernel kernel
            (fun input => (minor.markov input).to_finite)
            (fun input => (minor.markov input).to_finite) pair)
        rw [Measure.map_apply _ _ _ eventMeasurable,
          Measure.smul_apply_measurable _ _ eventMeasurable,
          (minor.markov pair.1).univ_eq_one, ENNReal.one_mul] at marginal
        exact marginal

private theorem deterministic_identity_comp {β : Type u} {target : Space β}
    (next : Kernel space target) :
    (Kernel.deterministic (fun value => value) (MeasurableMap.identity space)).comp
      next = next := by
  apply Kernel.ext
  intro input
  rw [deterministic_comp_apply]

private theorem comp_deterministic_identity {β : Type u} {source : Space β}
    (first : Kernel source space) :
    first.comp
      (Kernel.deterministic (fun value => value) (MeasurableMap.identity space)) =
      first := by
  rw [comp_deterministic]
  apply Kernel.ext
  intro input
  rw [Kernel.map_apply, Measure.map_id]

private theorem iterate_marginal
    (coupled : Kernel (couplingSpace space) (couplingSpace space))
    (projection : Sum (α × α) α → α)
    (projectionMeasurable : MeasurableMap (couplingSpace space) space projection)
    (step : coupled.comp (Kernel.deterministic projection projectionMeasurable) =
      (Kernel.deterministic projection projectionMeasurable).comp kernel)
    (count : Nat) :
    (iterate coupled count).comp
        (Kernel.deterministic projection projectionMeasurable) =
      (Kernel.deterministic projection projectionMeasurable).comp
        (iterate kernel count) := by
  induction count with
  | zero =>
      rw [iterate_zero, iterate_zero, deterministic_identity_comp,
        comp_deterministic_identity]
  | succ count induction =>
      rw [iterate_succ, iterate_succ, comp_assoc, induction, ← comp_assoc, step,
        comp_assoc]

/-- Each coordinate of the iterated coupling is the iterated chain. -/
public theorem small_set_coupling_marginals
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) (count : Nat) :
    (iterate (couplingKernel minor measurable) count).comp
        (Kernel.deterministic couplingFirst (couplingFirst_measurable space)) =
      (Kernel.deterministic couplingFirst (couplingFirst_measurable space)).comp
        (iterate kernel count) ∧
    (iterate (couplingKernel minor measurable) count).comp
        (Kernel.deterministic couplingSecond (couplingSecond_measurable space)) =
      (Kernel.deterministic couplingSecond (couplingSecond_measurable space)).comp
        (iterate kernel count) :=
  ⟨iterate_marginal _ _ _ (couplingKernel_first minor measurable) count,
    iterate_marginal _ _ _ (couplingKernel_second minor measurable) count⟩

/-- Once coupled, the two copies stay coupled. -/
public theorem coupled_absorbing
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) (count : Nat) (value : α) :
    iterate (couplingKernel minor measurable) count (Sum.inr value)
      uncoupledStates = ENNReal.zero := by
  induction count generalizing value with
  | zero =>
      rw [iterate_zero, Kernel.deterministic_apply,
        Measure.dirac_apply _ _ (uncoupledStates_measurable space)]
      apply ite_eq_right
      rintro ⟨pair, equal⟩
      cases equal
  | succ count induction =>
      rw [iterate_succ, comp_apply_measurable _ _ _
          (uncoupledStates_measurable space),
        couplingKernel_inr,
        lintegral_map _ _ _
          ((iterate (couplingKernel minor measurable) count).measurable
            (uncoupledStates_measurable space))]
      rw [lintegral_congr _ (fun other => induction other)]
      exact lintegral_zero _

/-- The uncoupled mass bounds the total variation between the two coordinates. -/
public theorem coupling_totalVariation_le
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) (count : Nat)
    (state : Sum (α × α) α) :
    ENNReal.le
      (Giry.Law.totalVariation
        ⟨iterate kernel count (couplingFirst state),
          iterate_isProbability kernel minor.markov count (couplingFirst state)⟩
        ⟨iterate kernel count (couplingSecond state),
          iterate_isProbability kernel minor.markov count (couplingSecond state)⟩)
      (iterate (couplingKernel minor measurable) count state uncoupledStates) := by
  have marginals := small_set_coupling_marginals minor measurable count
  let coupled := iterate (couplingKernel minor measurable) count state
  have coordinate : ∀ (projection : Sum (α × α) α → α)
      (projectionMeasurable : MeasurableMap (couplingSpace space) space projection),
      (iterate (couplingKernel minor measurable) count).comp
          (Kernel.deterministic projection projectionMeasurable) =
        (Kernel.deterministic projection projectionMeasurable).comp
          (iterate kernel count) →
      ∀ event, space.Measurable event →
        iterate kernel count (projection state) event =
          coupled (Set.preimage projection event) := by
    intro projection projectionMeasurable equal event eventMeasurable
    have evaluated := congrArg (fun current => current state event) equal
    rw [comp_deterministic, Kernel.map_apply,
      Measure.map_apply _ _ _ eventMeasurable,
      deterministic_comp_apply] at evaluated
    exact evaluated.symm
  have oneSided : ∀ (event : Set α), space.Measurable event →
      ∀ (leftProjection rightProjection : Sum (α × α) α → α),
      (∀ value, leftProjection (Sum.inr value) = rightProjection (Sum.inr value)) →
      ENNReal.le
        (ENNReal.sub (coupled (Set.preimage leftProjection event))
          (coupled (Set.preimage rightProjection event)))
        (coupled uncoupledStates) := by
    intro event _ leftProjection rightProjection agree
    apply ENNReal.sub_le_iff_le_add.mpr
    apply ENNReal.le_trans (coupled.mono (right := Set.union uncoupledStates
      (Set.preimage rightProjection event)) ?_)
      (coupled.union_le _ _)
    intro target member
    cases target with
    | inl pair => exact Or.inl ⟨pair, rfl⟩
    | inr value =>
        apply Or.inr
        change event (rightProjection (Sum.inr value))
        rw [← agree value]
        exact member
  unfold Giry.Law.totalVariation
  apply ENNReal.supremum_le
  rintro distance ⟨event, eventMeasurable, rfl⟩
  change ENNReal.le
    (ENNReal.max
      (ENNReal.sub (iterate kernel count (couplingFirst state) event)
        (iterate kernel count (couplingSecond state) event))
      (ENNReal.sub (iterate kernel count (couplingSecond state) event)
        (iterate kernel count (couplingFirst state) event)))
    (coupled uncoupledStates)
  rw [coordinate couplingFirst (couplingFirst_measurable space) marginals.1 event
      eventMeasurable,
    coordinate couplingSecond (couplingSecond_measurable space) marginals.2 event
      eventMeasurable]
  exact ENNReal.max_le
    (oneSided event eventMeasurable couplingFirst couplingSecond (fun _ => rfl))
    (oneSided event eventMeasurable couplingSecond couplingFirst (fun _ => rfl))

/-- The pair chain with the coupled mass removed. A trial pair keeps the
normalized residual product, and every other pair moves independently. -/
@[expose] public noncomputable def uncoupledKernel
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) :
    Kernel (Space.product space space) (Space.product space space) :=
  piecewise (Set.product region region)
    (Space.product_set_measurable space space measurable measurable)
    (Kernel.smul (failureScale weight)
      (parallel (residual minor measurable) (residual minor measurable)
        (residual_isFinite minor measurable) (residual_isFinite minor measurable)))
    (parallel kernel kernel (fun input => (minor.markov input).to_finite)
      (fun input => (minor.markov input).to_finite))

/-- The mass still uncoupled after `count` steps from a pair. -/
@[expose] public noncomputable def uncoupledMass
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) (count : Nat) (pair : α × α) : ENNReal :=
  iterate (uncoupledKernel minor measurable) count pair Set.univ

public theorem uncoupledKernel_apply_of_mem
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) {pair : α × α}
    (member : Set.product region region pair) :
    uncoupledKernel minor measurable pair =
      Measure.smul (failureScale weight)
        (parallel (residual minor measurable) (residual minor measurable)
          (residual_isFinite minor measurable)
          (residual_isFinite minor measurable) pair) := by
  rw [uncoupledKernel, piecewise_apply_of_mem _ _ _ _ _ member, Kernel.smul_apply]

public theorem uncoupledKernel_apply_of_not_mem
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) {pair : α × α}
    (outside : ¬ Set.product region region pair) :
    uncoupledKernel minor measurable pair =
      parallel kernel kernel (fun input => (minor.markov input).to_finite)
        (fun input => (minor.markov input).to_finite) pair := by
  rw [uncoupledKernel, piecewise_apply_of_not_mem _ _ _ _ _ outside]

/-- A failed trial keeps mass `1 − ε`. -/
public theorem uncoupledKernel_region_mass
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) (pair : α × α)
    (member : Set.product region region pair) :
    uncoupledKernel minor measurable pair Set.univ =
      ENNReal.sub ENNReal.one (ENNReal.finite weight) := by
  rw [uncoupledKernel_apply_of_mem minor measurable member,
    Measure.smul_apply_measurable _ _ (Space.product space space).univ,
    parallel_apply_univ, residual_mass minor measurable member.1,
    residual_mass minor measurable member.2,
    failureScale_cancel minor.weightAtMostOne _ (fun full => by
      rw [full]
      exact ENNReal.sub_self ENNReal.one)]

public theorem uncoupledKernel_le_one
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) (pair : α × α) :
    ENNReal.le (uncoupledKernel minor measurable pair Set.univ) ENNReal.one := by
  by_cases member : Set.product region region pair
  · rw [uncoupledKernel_region_mass minor measurable pair member]
    exact ENNReal.sub_le_self _ _
  · rw [uncoupledKernel_apply_of_not_mem minor measurable member,
      parallel_apply_univ, (minor.markov pair.1).univ_eq_one,
      (minor.markov pair.2).univ_eq_one, ENNReal.mul_one]
    exact ENNReal.le_refl _

public theorem uncoupledMass_antitone
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) {first second : Nat}
    (included : first ≤ second) (pair : α × α) :
    ENNReal.le (uncoupledMass minor measurable second pair)
      (uncoupledMass minor measurable first pair) :=
  iterate_mass_antitone _ (uncoupledKernel_le_one minor measurable) included pair

/-- The uncoupled coupling mass is the mass of the uncoupled pair chain. -/
public theorem iterate_couplingKernel_inl
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) (count : Nat) (pair : α × α) :
    iterate (couplingKernel minor measurable) count (Sum.inl pair)
      uncoupledStates = uncoupledMass minor measurable count pair := by
  induction count generalizing pair with
  | zero =>
      rw [iterate_zero, Kernel.deterministic_apply,
        Measure.dirac_apply _ _ (uncoupledStates_measurable space),
        ite_eq_left ⟨pair, rfl⟩, uncoupledMass, iterate_zero,
        Kernel.deterministic_apply, Measure.dirac_apply_univ]
  | succ count induction =>
      let continuation := fun state =>
        iterate (couplingKernel minor measurable) count state uncoupledStates
      have continuationMeasurable : ENNRealMeasurable (couplingSpace space)
          continuation :=
        (iterate (couplingKernel minor measurable) count).measurable
          (uncoupledStates_measurable space)
      have onPairs : ∀ other, continuation (Sum.inl other) =
          uncoupledMass minor measurable count other := induction
      have onCoupled : ∀ value, continuation (Sum.inr value) = ENNReal.zero :=
        coupled_absorbing minor measurable count
      rw [iterate_succ, comp_apply_measurable _ _ _
          (uncoupledStates_measurable space), uncoupledMass, iterate_succ,
        comp_apply_measurable _ _ _ (Space.product space space).univ]
      change lintegral (couplingKernel minor measurable (Sum.inl pair)) continuation =
        lintegral (uncoupledKernel minor measurable pair)
          (uncoupledMass minor measurable count)
      by_cases member : Set.product region region pair
      · rw [couplingKernel_inl_of_mem minor measurable member, couplingTrial,
          Kernel.add_apply, lintegral_add_measure, Kernel.const_apply,
          lintegral_map _ _ (MeasurableMap.inr (Space.product space space) space)
            continuationMeasurable,
          Kernel.map_apply _ _ (MeasurableMap.inl (Space.product space space) space),
          lintegral_map _ _ (MeasurableMap.inl (Space.product space space) space)
            continuationMeasurable,
          Kernel.smul_apply, uncoupledKernel_apply_of_mem minor measurable member,
          lintegral_congr _ onCoupled, lintegral_zero, ENNReal.zero_add]
        exact lintegral_congr _ onPairs
      · rw [couplingKernel_inl_of_not_mem minor measurable member,
          lintegral_map _ _ _ continuationMeasurable,
          uncoupledKernel_apply_of_not_mem minor measurable member]
        exact lintegral_congr _ onPairs

/-- No mass is coupled before the first step. -/
public theorem uncoupledMass_zero
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) (pair : α × α) :
    uncoupledMass minor measurable 0 pair = ENNReal.one := by
  rw [uncoupledMass, iterate_zero, Kernel.deterministic_apply,
    Measure.dirac_apply_univ]

/-- A set the independent pair chain misses is missed by the uncoupled chain,
including at full weight. -/
public theorem uncoupledKernel_null_of_parallel_null
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) (pair : α × α)
    {event : Set (α × α)}
    (eventMeasurable : (Space.product space space).Measurable event)
    (zero : parallel kernel kernel (fun input => (minor.markov input).to_finite)
      (fun input => (minor.markov input).to_finite) pair event = ENNReal.zero) :
    uncoupledKernel minor measurable pair event = ENNReal.zero := by
  by_cases member : Set.product region region pair
  · rw [uncoupledKernel_apply_of_mem minor measurable member,
      Measure.smul_apply_measurable _ _ eventMeasurable]
    have below := parallel_le_parallel (residual_isFinite minor measurable)
      (residual_isFinite minor measurable)
      (fun input => (minor.markov input).to_finite)
      (fun input => (minor.markov input).to_finite)
      (residual_le minor measurable) (residual_le minor measurable)
      pair event eventMeasurable
    rw [zero] at below
    rw [ENNReal.eq_zero_of_le_zero below, ENNReal.mul_zero]
  · rw [uncoupledKernel_apply_of_not_mem minor measurable member]
    exact zero

end Problib.Measure.Kernel
