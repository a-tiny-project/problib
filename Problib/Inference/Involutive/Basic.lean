module

public import Problib.Inference.Invariance
public import Problib.Measure.Kernel.Density
public import Problib.Measure.Integral.Density.Change
public import Problib.Measure.Extended.Algebra.Binary
public import Problib.Measure.Extended.Algebra.Fixed
public import Problib.Measure.Kernel.Measurable
public import Problib.Measure.Integral.Lebesgue.Transport

set_option autoImplicit false

/-! The involutive accept/reject kernel.

An auxiliary draw extends a state to a pair, a measurable map on pairs
proposes the next state, and an acceptance weight chooses the move or the
current state (`involutiveKernel`). One step's joint law is the accepted
moves plus the rejected mass on the diagonal (`involutive_joint`), so the step
is in detailed balance as soon as the map is an involution that preserves the
accepted mass (`involutive_detailed_balance`). Metropolis–Hastings is the
instance whose auxiliary draw is the proposal and whose map swaps the pair. -/

namespace Problib.Inference

open Problib.Real Problib.Measure

universe u v
variable {α : Type u} {β : Type v}
variable {state : Space α} {auxiliarySpace : Space β}

public section

/-- Send accepted mass to `destination pair` and rejected mass to `pair.1`. -/
@[expose] noncomputable def moveOrStayTo
    (destination : α × β → α)
    (destinationMeasurable :
      MeasurableMap (Space.product state auxiliarySpace) state destination)
    (accept : α × β → ENNReal)
    (acceptMeasurable : ENNRealMeasurable (Space.product state auxiliarySpace) accept) :
    Kernel (Space.product state auxiliarySpace) state :=
  Kernel.add
    ((Kernel.deterministic destination destinationMeasurable).withDensity
      (Kernel.IsSFinite.deterministic _ _) (fun pair _ => accept pair)
      (acceptMeasurable.comp (Space.first_measurable _ _)))
    ((Kernel.deterministic Prod.fst (Space.first_measurable state auxiliarySpace)).withDensity
      (Kernel.IsSFinite.deterministic _ _)
      (fun pair _ => ENNReal.sub ENNReal.one (accept pair))
      ((ENNRealMeasurable.sub (ENNRealMeasurable.constant _ ENNReal.one)
        acceptMeasurable).comp (Space.first_measurable _ _)))

/-- Integral of one accept/reject decision with an arbitrary destination. -/
theorem lintegral_moveOrStayTo
    (destination : α × β → α)
    (destinationMeasurable :
      MeasurableMap (Space.product state auxiliarySpace) state destination)
    (accept : α × β → ENNReal)
    (acceptMeasurable : ENNRealMeasurable (Space.product state auxiliarySpace) accept)
    (pair : α × β) {function : α → ENNReal}
    (functionMeasurable : ENNRealMeasurable state function) :
    lintegral
        (moveOrStayTo destination destinationMeasurable accept acceptMeasurable pair)
        function =
      ENNReal.add (ENNReal.mul (accept pair) (function (destination pair)))
        (ENNReal.mul (ENNReal.sub ENNReal.one (accept pair)) (function pair.1)) := by
  unfold moveOrStayTo
  rw [Kernel.add_apply, lintegral_add_measure,
    Kernel.withDensity_apply, Kernel.withDensity_apply,
    Kernel.deterministic_apply, Kernel.deterministic_apply,
    lintegral_withDensity _ (ENNRealMeasurable.constant _ _) functionMeasurable,
    lintegral_withDensity _ (ENNRealMeasurable.constant _ _) functionMeasurable,
    lintegral_dirac _ _
      (ENNRealMeasurable.mul (ENNRealMeasurable.constant _ _) functionMeasurable),
    lintegral_dirac _ _
      (ENNRealMeasurable.mul (ENNRealMeasurable.constant _ _) functionMeasurable)]

/-- Draw an auxiliary value, then accept the state projection of an
involution or keep the current state. -/
@[expose] noncomputable def involutiveKernel
    (auxiliary : Kernel state auxiliarySpace)
    (auxiliaryFinite : Kernel.IsSFinite auxiliary)
    (involution : α × β → α × β)
    (involutionMeasurable :
      MeasurableMap (Space.product state auxiliarySpace)
        (Space.product state auxiliarySpace) involution)
    (accept : α × β → ENNReal)
    (acceptMeasurable : ENNRealMeasurable (Space.product state auxiliarySpace) accept) :
    Kernel state state :=
  (Kernel.attach auxiliary auxiliaryFinite).comp
    (moveOrStayTo (fun pair => (involution pair).1)
      (MeasurableMap.comp (Space.first_measurable state auxiliarySpace)
        involutionMeasurable)
      accept acceptMeasurable)

@[expose] noncomputable def involutiveKernelSFinite
    {auxiliary : Kernel state auxiliarySpace}
    (auxiliaryFinite : Kernel.IsSFinite auxiliary)
    {involution : α × β → α × β}
    (involutionMeasurable :
      MeasurableMap (Space.product state auxiliarySpace)
        (Space.product state auxiliarySpace) involution)
    {accept : α × β → ENNReal}
    (acceptMeasurable : ENNRealMeasurable (Space.product state auxiliarySpace) accept) :
    Kernel.IsSFinite
      (involutiveKernel auxiliary auxiliaryFinite involution
        involutionMeasurable accept acceptMeasurable) := by
  unfold involutiveKernel moveOrStayTo
  exact Kernel.IsSFinite.comp (Kernel.IsSFinite.attach auxiliaryFinite)
    (Kernel.IsSFinite.add
      (Kernel.IsSFinite.withDensity (Kernel.IsSFinite.deterministic _ _) _ _)
      (Kernel.IsSFinite.withDensity (Kernel.IsSFinite.deterministic _ _) _ _))

/-- Integral of the involutive transition from one state. -/
theorem lintegral_involutiveKernel
    (auxiliary : Kernel state auxiliarySpace)
    (auxiliaryFinite : Kernel.IsSFinite auxiliary)
    (involution : α × β → α × β)
    (involutionMeasurable :
      MeasurableMap (Space.product state auxiliarySpace)
        (Space.product state auxiliarySpace) involution)
    (accept : α × β → ENNReal)
    (acceptMeasurable : ENNRealMeasurable (Space.product state auxiliarySpace) accept)
    (input : α) {function : α → ENNReal}
    (functionMeasurable : ENNRealMeasurable state function) :
    lintegral
        (involutiveKernel auxiliary auxiliaryFinite involution involutionMeasurable
          accept acceptMeasurable input) function =
      lintegral (auxiliary input) fun drawn =>
        ENNReal.add
          (ENNReal.mul (accept (input, drawn)) (function (involution (input, drawn)).1))
          (ENNReal.mul (ENNReal.sub ENNReal.one (accept (input, drawn)))
            (function input)) := by
  unfold involutiveKernel
  rw [Kernel.comp_apply, Measure.lintegral_bind _ _ functionMeasurable,
    Kernel.attach_apply, lintegral_map]
  · apply lintegral_congr
    intro drawn
    exact lintegral_moveOrStayTo
      (fun pair => (involution pair).1)
      (MeasurableMap.comp (Space.first_measurable state auxiliarySpace)
        involutionMeasurable)
      accept acceptMeasurable (input, drawn) functionMeasurable
  · exact Kernel.lintegral_measurable _ functionMeasurable

/-- An at-most-one acceptance gives a probability transition from a Markov
auxiliary kernel. -/
theorem involutiveKernel_markov
    {auxiliary : Kernel state auxiliarySpace}
    (auxiliaryFinite : Kernel.IsSFinite auxiliary)
    (auxiliaryMarkov : ∀ input, Measure.IsProbability (auxiliary input))
    {involution : α × β → α × β}
    (involutionMeasurable :
      MeasurableMap (Space.product state auxiliarySpace)
        (Space.product state auxiliarySpace) involution)
    {accept : α × β → ENNReal}
    (acceptMeasurable : ENNRealMeasurable (Space.product state auxiliarySpace) accept)
    (atMostOne : ∀ point, ENNReal.le (accept point) ENNReal.one)
    (input : α) :
    Measure.IsProbability
      (involutiveKernel auxiliary auxiliaryFinite involution
        involutionMeasurable accept acceptMeasurable input) := by
  constructor
  have total := lintegral_const
    (involutiveKernel auxiliary auxiliaryFinite involution
      involutionMeasurable accept acceptMeasurable input) ENNReal.one
  rw [ENNReal.one_mul] at total
  rw [← total, lintegral_involutiveKernel _ _ _ _ _ _ _
    (ENNRealMeasurable.constant _ _)]
  calc
    lintegral (auxiliary input) (fun drawn =>
        ENNReal.add (ENNReal.mul (accept (input, drawn)) ENNReal.one)
          (ENNReal.mul (ENNReal.sub ENNReal.one (accept (input, drawn)))
            ENNReal.one)) =
      lintegral (auxiliary input) (fun _ => ENNReal.one) := by
        apply lintegral_congr
        intro drawn
        rw [ENNReal.mul_one, ENNReal.mul_one, ENNReal.add_comm,
          ENNReal.sub_add_cancel (atMostOne (input, drawn))]
    _ = ENNReal.one := by
      rw [lintegral_const, (auxiliaryMarkov input).univ_eq_one, ENNReal.one_mul]

/-- The initial and proposed states of an extended involutive move. -/
@[expose] def involutiveMove (involution : α × β → α × β)
    (point : α × β) : α × α := (point.1, (involution point).1)

theorem involutiveMove_measurable
    {involution : α × β → α × β}
    (involutionMeasurable :
      MeasurableMap (Space.product state auxiliarySpace)
        (Space.product state auxiliarySpace) involution) :
    MeasurableMap (Space.product state auxiliarySpace)
      (Space.product state state) (involutiveMove involution) :=
  Space.pair_measurable
    (Space.first_measurable state auxiliarySpace)
    (MeasurableMap.comp (Space.first_measurable state auxiliarySpace)
      involutionMeasurable)

/-- The diagonal states of a rejected extended move. -/
@[expose] def involutiveStay (point : α × β) : α × α := (point.1, point.1)

theorem involutiveStay_measurable :
    MeasurableMap (Space.product state auxiliarySpace)
      (Space.product state state) involutiveStay :=
  Space.pair_measurable (Space.first_measurable state auxiliarySpace)
    (Space.first_measurable state auxiliarySpace)

/-- The joint law consists of accepted proposed moves and rejected diagonal
mass. -/
theorem involutive_joint
    (target : Measure state) {auxiliary : Kernel state auxiliarySpace}
    (auxiliaryFinite : Kernel.IsSFinite auxiliary)
    {involution : α × β → α × β}
    (involutionMeasurable :
      MeasurableMap (Space.product state auxiliarySpace)
        (Space.product state auxiliarySpace) involution)
    {accept : α × β → ENNReal}
    (acceptMeasurable : ENNRealMeasurable (Space.product state auxiliarySpace) accept) :
    target.semiproduct
        (involutiveKernel auxiliary auxiliaryFinite involution
          involutionMeasurable accept acceptMeasurable)
        (involutiveKernelSFinite auxiliaryFinite involutionMeasurable
          acceptMeasurable) =
      Measure.add
        (((target.semiproduct auxiliary auxiliaryFinite).withDensity accept).map
          (involutiveMove involution)
          (involutiveMove_measurable involutionMeasurable))
        (((target.semiproduct auxiliary auxiliaryFinite).withDensity
            (fun point => ENNReal.sub ENNReal.one (accept point))).map
          involutiveStay involutiveStay_measurable) := by
  apply Measure.ext
  intro set setMeasurable
  let indicator : α × α → ENNReal := ennrealIndicator set fun _ => ENNReal.one
  have indicatorMeasurable : ENNRealMeasurable (Space.product state state) indicator :=
    ENNRealMeasurable.indicator setMeasurable (ENNRealMeasurable.constant _ _)
  have rejectMeasurable : ENNRealMeasurable
      (Space.product state auxiliarySpace)
      (fun point => ENNReal.sub ENNReal.one (accept point)) :=
    ENNRealMeasurable.sub (ENNRealMeasurable.constant _ _) acceptMeasurable
  have sectionMeasurable (input : α) :
      ENNRealMeasurable state (fun output => indicator (input, output)) :=
    indicatorMeasurable.comp (Kernel.pair_left_measurable input)
  rw [Measure.add_apply_measurable _ _ setMeasurable,
    apply_eq_lintegral_indicator _ setMeasurable,
    apply_eq_lintegral_indicator _ setMeasurable,
    apply_eq_lintegral_indicator _ setMeasurable,
    lintegral_semiproduct _ _ _ indicatorMeasurable,
    lintegral_map _ _ _ indicatorMeasurable,
    lintegral_withDensity _ acceptMeasurable
      (indicatorMeasurable.comp
        (involutiveMove_measurable involutionMeasurable)),
    lintegral_map _ _ _ indicatorMeasurable,
    lintegral_withDensity _ rejectMeasurable
      (indicatorMeasurable.comp involutiveStay_measurable),
    ← lintegral_add _
      (ENNRealMeasurable.mul acceptMeasurable
        (indicatorMeasurable.comp
          (involutiveMove_measurable involutionMeasurable)))
      (ENNRealMeasurable.mul rejectMeasurable
        (indicatorMeasurable.comp involutiveStay_measurable)),
    lintegral_semiproduct _ _ _
      (ENNRealMeasurable.add
        (ENNRealMeasurable.mul acceptMeasurable
          (indicatorMeasurable.comp
            (involutiveMove_measurable involutionMeasurable)))
        (ENNRealMeasurable.mul rejectMeasurable
          (indicatorMeasurable.comp involutiveStay_measurable)))]
  apply lintegral_congr
  intro input
  exact lintegral_involutiveKernel auxiliary auxiliaryFinite
    involution involutionMeasurable accept acceptMeasurable input
    (sectionMeasurable input)

private theorem map_eq_of_pointwise
    (measure : Measure (Space.product state auxiliarySpace))
    {first second : α × β → α × α}
    (firstMeasurable : MeasurableMap (Space.product state auxiliarySpace)
      (Space.product state state) first)
    (secondMeasurable : MeasurableMap (Space.product state auxiliarySpace)
      (Space.product state state) second)
    (equal : ∀ point, first point = second point) :
    measure.map first firstMeasurable = measure.map second secondMeasurable := by
  apply Measure.ext
  intro set setMeasurable
  rw [Measure.map_apply _ _ _ setMeasurable,
    Measure.map_apply _ _ _ setMeasurable]
  apply congrArg measure
  apply Set.ext
  intro point
  change (first point ∈ set) ↔ (second point ∈ set)
  rw [equal point]

/-- Symmetry of accepted extended mass gives detailed balance of the
state transition. The rejected mass remains on the diagonal. -/
theorem involutive_detailed_balance
    (target : Measure state) (auxiliary : Kernel state auxiliarySpace)
    (auxiliaryFinite : Kernel.IsSFinite auxiliary)
    (involution : α × β → α × β)
    (involutionMeasurable :
      MeasurableMap (Space.product state auxiliarySpace)
        (Space.product state auxiliarySpace) involution)
    (involutive : ∀ point, involution (involution point) = point)
    {accept : α × β → ENNReal}
    (acceptMeasurable : ENNRealMeasurable (Space.product state auxiliarySpace) accept)
    (acceptedSymmetric :
      (((target.semiproduct auxiliary auxiliaryFinite).withDensity accept).map
        involution involutionMeasurable) =
       (target.semiproduct auxiliary auxiliaryFinite).withDensity accept) :
    DetailedBalance target
      (involutiveKernel auxiliary auxiliaryFinite involution involutionMeasurable
        accept acceptMeasurable)
      (involutiveKernelSFinite auxiliaryFinite involutionMeasurable acceptMeasurable) := by
  let swap : α × α → α × α := fun pair => (pair.2, pair.1)
  unfold DetailedBalance
  rw [involutive_joint target auxiliaryFinite involutionMeasurable
    acceptMeasurable, Measure.map_add]
  congr 1
  · let flux := (target.semiproduct auxiliary auxiliaryFinite).withDensity accept
    let moveMeasurable : MeasurableMap (Space.product state auxiliarySpace)
        (Space.product state state) (involutiveMove involution) :=
      involutiveMove_measurable involutionMeasurable
    let swapMeasurable : MeasurableMap (Space.product state state)
        (Space.product state state) swap := Space.swap_measurable state state
    calc
      (flux.map (involutiveMove involution) moveMeasurable).map swap
          swapMeasurable =
        flux.map (fun point => swap (involutiveMove involution point))
          (MeasurableMap.comp swapMeasurable moveMeasurable) :=
        Measure.map_comp flux (involutiveMove involution) swap
          moveMeasurable swapMeasurable
      _ = flux.map (fun point => involutiveMove involution (involution point))
          (MeasurableMap.comp moveMeasurable involutionMeasurable) := by
        apply map_eq_of_pointwise
        intro point
        change ((involution point).1, point.1) =
          ((involution point).1, (involution (involution point)).1)
        rw [involutive point]
      _ = (flux.map involution involutionMeasurable).map
          (involutiveMove involution) moveMeasurable :=
        (Measure.map_comp flux involution (involutiveMove involution)
          involutionMeasurable moveMeasurable).symm
      _ = flux.map (involutiveMove involution) moveMeasurable := by
        rw [acceptedSymmetric]

end

end Problib.Inference
