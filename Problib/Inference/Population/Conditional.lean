module

public import Problib.Inference.ExtendedTarget
public import Problib.Measure.Kernel.Scale
public import Problib.Inference.Sequential
import Problib.Measure.Integral.Lebesgue.Extensionality
import Problib.Measure.Integral.Lebesgue.Transport
import Problib.Measure.Kernel.Composition.Bind.Transport
import Problib.Measure.Kernel.Measurable
import Problib.Measure.Kernel.Precomp
import Problib.Measure.Kernel.Product
import Problib.Measure.Kernel.Piecewise
set_option autoImplicit false

/-! # Conditional population laws

A conditional law of a population is a disintegration of its extended target
along the marked lane's value, with the marked lane pinned: `conditional x` is
carried by the marked populations whose marked lane holds `x` (`HoldsAt`). It is
the joint law of a population built around one retained reference lane, and it
says more than invariance does. A Markov conditional law makes the population
invariant for its target (`empirical_invariant_of_conditional`), and the
extended target then reads the target at the marked lane (`conditional_reference`).

A conditional step carries every conditional law of its input to one of its
output (`ConditionalStep`), and conditional steps compose
(`conditional_step_comp`). A step with a move on marked populations that
intertwines the marking and keeps the marked value is a conditional step
(`conditional_step_of_move`). Multinomial resampling is one
(`conditional_resample`): its move sends a uniform child to the marked lane and
draws every other child's parent from the categorical law of the weights.

The identities take s-finite kernels and measures, and no normalization. Lanes
are `Fin (extent + 1)` wherever the lanes' joint law enters: the conditional
steps are `Kernel.finProduct` products with one lane pinned (`Kernel.pinLane`). -/

namespace Problib.Inference

open Problib.Real Problib.Measure

universe u v

public section


private theorem mul_listSum {ι : Type} (indices : List ι) (factor : ENNReal)
    (values : ι → ENNReal) :
    ENNReal.mul factor (ENNReal.additiveLaws.listSum (indices.map values)) =
      ENNReal.additiveLaws.listSum (indices.map fun index => ENNReal.mul factor (values index)) :=
  (ENNReal.semiring.listSum_map_mul_left indices factor values).symm

private theorem mul_left_comm (first second third : ENNReal) :
    ENNReal.mul first (ENNReal.mul second third) = ENNReal.mul second (ENNReal.mul first third) := by
  rw [← ENNReal.mul_assoc, ENNReal.mul_comm first second, ENNReal.mul_assoc]

/-! ### Conditional laws -/

variable {α : Type} {β : Type} {γ : Type} {space : Space α} {result : Space β}
  {final : Space γ}

/-- The marked lane's value, paired with the marked population. -/
theorem readMarked_measurable {ι : Type} (lanes : Lanes ι) (space : Space α) :
    MeasurableMap (markedSpace ι space) (Space.product space (markedSpace ι space))
      (fun marked => (reference marked, marked)) :=
  Space.pair_measurable (reference_measurable lanes space) (MeasurableMap.identity _)

/-- `measure` is carried by the marked populations whose marked lane holds
`point`: pairing each with its marked lane's value pairs it with `point`. It
needs no measurable singletons and no finite mass. -/
@[expose] def HoldsAt {ι : Type} (lanes : Lanes ι) (point : α)
    (measure : Measure (markedSpace ι space)) : Prop :=
  measure.map (fun marked => (reference marked, marked)) (readMarked_measurable lanes space) =
    measure.map (fun marked => (point, marked)) (Kernel.pair_left_measurable point)

/-- Under a measure held at `point`, the marked lane's value reads as `point`. -/
theorem lintegral_holdsAt {ι : Type} {lanes : Lanes ι} {point : α}
    {measure : Measure (markedSpace ι space)} (holds : HoldsAt lanes point measure)
    {function : α × ((ι → α × NNReal) × ι) → ENNReal}
    (measurable : ENNRealMeasurable (Space.product space (markedSpace ι space)) function) :
    lintegral measure (fun marked => function (reference marked, marked)) =
      lintegral measure (fun marked => function (point, marked)) := by
  have integrals := congrArg (fun image => lintegral image function) holds
  rw [lintegral_map _ _ (readMarked_measurable lanes space) measurable,
    lintegral_map _ _ (Kernel.pair_left_measurable (source := space) point) measurable]
    at integrals
  exact integrals

/-- ConditionalLaw: `conditional` disintegrates the extended target of
`population` along the marked lane's value, from `target`, and `conditional x`
holds `x` at the marked lane. The kernel may be infinite and the target
unnormalized. -/
structure ConditionalLaw {ι : Type} (lanes : Lanes ι)
    (population : Measure (populationSpace ι space)) (target : Measure space)
    (conditional : Kernel space (markedSpace ι space)) : Prop where
  disintegrates : target.bind conditional = extended lanes population
  pinned : ∀ point, HoldsAt lanes point (conditional point)

/-- A Markov conditional law's extended target reads its target at the marked
lane. It needs `conditional` Markov: the marked lane's value is `x` under
`conditional x`, and only a probability integrates it to the Dirac at `x`. -/
theorem conditional_reference {ι : Type} {lanes : Lanes ι}
    {population : Measure (populationSpace ι space)} {target : Measure space}
    {conditional : Kernel space (markedSpace ι space)}
    (law : ConditionalLaw lanes population target conditional)
    (markov : ∀ point, Measure.IsProbability (conditional point)) :
    (extended lanes population).map reference (reference_measurable lanes space) = target := by
  rw [← law.disintegrates, Measure.map_bind]
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  rw [Measure.lintegral_bind _ _ measurable]
  refine lintegral_congr _ fun point => ?_
  have held : lintegral (conditional point) (fun marked => function (reference marked)) =
      lintegral (conditional point) (fun _ => function point) :=
    lintegral_holdsAt (law.pinned point) (function := fun pair => function pair.1)
      (measurable.comp (Space.first_measurable _ _))
  rw [Kernel.map_apply, lintegral_map _ _ _ measurable, held, lintegral_const,
    (markov point).univ_eq_one, ENNReal.mul_one]

/-- The disintegration in the form `referenceChain_invariant` reads. -/
theorem conditional_disintegrates {ι : Type} {lanes : Lanes ι}
    {population : Measure (populationSpace ι space)} {target : Measure space}
    {conditional : Kernel space (markedSpace ι space)}
    (law : ConditionalLaw lanes population target conditional)
    (markov : ∀ point, Measure.IsProbability (conditional point)) :
    ((extended lanes population).map reference (reference_measurable lanes space)).bind
      conditional = extended lanes population := by
  rw [conditional_reference law markov]
  exact law.disintegrates

/-- A population with a Markov conditional law is invariant for its target. It
needs `conditional` Markov, for `conditional_reference`, and `population` a
probability, since `EmpiricalInvariant` is a statement about a probability. -/
theorem empirical_invariant_of_conditional {ι : Type} {lanes : Lanes ι}
    {population : Measure (populationSpace ι space)} {target : Measure space}
    {conditional : Kernel space (markedSpace ι space)}
    (law : ConditionalLaw lanes population target conditional)
    (markov : ∀ point, Measure.IsProbability (conditional point))
    (probability : Measure.IsProbability population) :
    EmpiricalInvariant lanes target population :=
  ⟨probability, (extended_reference lanes population).symm.trans (conditional_reference law markov)⟩

/-! ### Conditional steps -/

/-- A population step with a conditional counterpart: `lift` carries every
s-finite conditional law of the input for `source` to a conditional law of the
output for `target`. -/
@[expose] def ConditionalStep {ι κ : Type} (inLanes : Lanes ι) (outLanes : Lanes κ)
    (source : Measure space) (target : Measure result)
    (step : Kernel (populationSpace ι space) (populationSpace κ result))
    (lift : (conditional : Kernel space (markedSpace ι space)) → Kernel.IsSFinite conditional →
      Kernel result (markedSpace κ result)) : Prop :=
  ∀ population conditional (finite : Kernel.IsSFinite conditional),
    ConditionalLaw inLanes population source conditional →
      ConditionalLaw outLanes (population.bind step) target (lift conditional finite)

/-- Conditional steps compose, when the first lifts s-finite kernels to s-finite
kernels. -/
theorem conditional_step_comp {ι κ ν : Type} {first : Lanes ι} {second : Lanes κ}
    {third : Lanes ν} {source : Measure space} {middle : Measure result}
    {target : Measure final}
    {step : Kernel (populationSpace ι space) (populationSpace κ result)}
    {next : Kernel (populationSpace κ result) (populationSpace ν final)}
    {lift : (conditional : Kernel space (markedSpace ι space)) → Kernel.IsSFinite conditional →
      Kernel result (markedSpace κ result)}
    {nextLift : (conditional : Kernel result (markedSpace κ result)) →
      Kernel.IsSFinite conditional → Kernel final (markedSpace ν final)}
    (firstStep : ConditionalStep first second source middle step lift)
    (liftFinite : ∀ conditional finite, Kernel.IsSFinite (lift conditional finite))
    (secondStep : ConditionalStep second third middle target next nextLift) :
    ConditionalStep first third source target (step.comp next)
      (fun conditional finite => nextLift (lift conditional finite) (liftFinite conditional finite)) := by
  intro population conditional finite law
  have carried := secondStep _ _ (liftFinite conditional finite)
    (firstStep population conditional finite law)
  rw [Measure.bind_assoc] at carried
  exact carried

/-- A move on marked populations retains the marked value when each of its
outputs holds its input's marked value. -/
@[expose] def Retains {ι κ : Type} (outLanes : Lanes κ)
    (move : Kernel (markedSpace ι space) (markedSpace κ space)) : Prop :=
  ∀ marked, HoldsAt outLanes (reference marked) (move marked)

/-- A step whose marking is intertwined with a retaining move is a conditional
step for every target, and its lift composes with the move. -/
theorem conditional_step_of_move {ι κ : Type} (inLanes : Lanes ι) (outLanes : Lanes κ)
    (target : Measure space) (step : Kernel (populationSpace ι space) (populationSpace κ space))
    (move : Kernel (markedSpace ι space) (markedSpace κ space))
    (moveFinite : Kernel.IsSFinite move)
    (intertwines : step.comp (markedLane outLanes space) = (markedLane inLanes space).comp move)
    (retains : Retains outLanes move) :
    ConditionalStep inLanes outLanes target target step
      (fun conditional _ => conditional.comp move) := by
  intro population conditional _ law
  constructor
  · show target.bind (conditional.comp move) = extended outLanes (population.bind step)
    rw [← Measure.bind_assoc, law.disintegrates]
    unfold extended
    rw [Measure.bind_assoc, Measure.bind_assoc, intertwines]
  · intro point
    unfold HoldsAt
    refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
    have leftSide : lintegral (((conditional.comp move) point).map
        (fun marked => (reference marked, marked)) (readMarked_measurable outLanes space)) function =
        lintegral (conditional point) fun marked =>
          lintegral (move marked) fun next => function (reference next, next) := by
      rw [lintegral_map _ _ (readMarked_measurable outLanes space) measurable, Kernel.comp_apply,
        Measure.lintegral_bind _ _ (measurable.comp (readMarked_measurable outLanes space))]
    have rightSide : lintegral (((conditional.comp move) point).map
        (fun marked => (point, marked))
        (Kernel.pair_left_measurable (source := space) point)) function =
        lintegral (conditional point) fun marked =>
          lintegral (move marked) fun next => function (point, next) := by
      rw [lintegral_map _ _ (Kernel.pair_left_measurable (source := space) point) measurable,
        Kernel.comp_apply, Measure.lintegral_bind _ _
          (measurable.comp (Kernel.pair_left_measurable (source := space) point))]
    have joint : ENNRealMeasurable (Space.product space (markedSpace ι space))
        (fun pair : α × ((ι → α × NNReal) × ι) =>
          lintegral (move pair.2) fun next => function (pair.1, next)) :=
      Kernel.lintegral_measurable_joint (move.precomp Prod.snd (Space.second_measurable _ _))
        (moveFinite.precomp Prod.snd (Space.second_measurable _ _))
        (function := fun pair next => function (pair.1, next))
        (measurable.comp (Space.pair_measurable
          (MeasurableMap.comp (Space.first_measurable _ _) (Space.first_measurable _ _))
          (Space.second_measurable _ _)))
    rw [leftSide, rightSide,
      lintegral_congr _ fun marked => lintegral_holdsAt (retains marked) measurable]
    exact lintegral_holdsAt (law.pinned point)
      (function := fun pair => lintegral (move pair.2) fun next => function (pair.1, next)) joint

/-! ### Multinomial resampling -/

/-- Child `child`'s parent is the marked lane, and every other child's parent is
drawn from `ancestorLane` at the marked population. -/
@[expose] noncomputable def conditionalAncestors {ι : Type} (inLanes : Lanes ι) (extent : Nat)
    (space : Space α) (child : Fin (extent + 1)) :
    Kernel (markedSpace ι space) (ancestorSpace ι (Fin (extent + 1))) :=
  Kernel.finProduct (extent + 1)
    (Kernel.pinLane (fun other => (ancestorLane inLanes (extent + 1) space other).precomp Prod.fst
      (Space.first_measurable _ _)) child
      (Kernel.deterministic Prod.snd (Space.second_measurable _ _)))
    (Kernel.pinLaneFinite (fun other => (ancestorLaneFinite inLanes (extent + 1) space other).precomp
      Prod.fst (Space.first_measurable _ _)) child (Kernel.IsSFinite.deterministic _ _))

noncomputable def conditionalAncestorsFinite {ι : Type} (inLanes : Lanes ι) (extent : Nat)
    (space : Space α) (child : Fin (extent + 1)) :
    Kernel.IsSFinite (conditionalAncestors inLanes extent space child) :=
  Kernel.IsSFinite.finProduct _ _ _

/-- The conditional ancestors read the other children's parents as the
unconditional ancestors do, with the marked lane inserted at `child`. -/
theorem lintegral_conditionalAncestors {ι : Type} (inLanes : Lanes ι) (extent : Nat)
    (space : Space α) (child : Fin (extent + 1)) (draws : ι → α × NNReal) (lane : ι)
    {function : (Fin (extent + 1) → ι) → ENNReal}
    (measurable : ENNRealMeasurable (ancestorSpace ι (Fin (extent + 1))) function) :
    lintegral (conditionalAncestors inLanes extent space child (draws, lane)) function =
      lintegral (Kernel.finProduct extent
          (fun position => ancestorLane inLanes (extent + 1) space (Kernel.laneSkip child position))
          (fun position => ancestorLaneFinite inLanes (extent + 1) space
            (Kernel.laneSkip child position)) draws)
        fun rest => function (Kernel.laneInsert child (lane, rest)) := by
  unfold conditionalAncestors
  rw [Kernel.lintegral_finProduct_pinned extent _ _ child
    (Kernel.deterministic Prod.snd (Space.second_measurable _ _)) _ (draws, lane) lane
    (Kernel.deterministic_apply _ _ _) measurable]
  exact congrArg (fun measure => lintegral measure fun rest => function (Kernel.laneInsert child (lane, rest)))
    (Kernel.finProduct_congr_at extent _ _ _ _ (draws, lane) draws fun _ => rfl)

/-- Weighing the ancestors by the mean weight marks each lane at its share of the
weight and makes it `child`'s parent. -/
theorem weighted_ancestors {ι : Type} (inLanes : Lanes ι) (extent : Nat) (space : Space α)
    (child : Fin (extent + 1)) (draws : ι → α × NNReal)
    {function : (Fin (extent + 1) → ι) → ENNReal}
    (measurable : ENNRealMeasurable (ancestorSpace ι (Fin (extent + 1))) function) :
    ENNReal.mul (ENNReal.finite (meanWeight inLanes draws))
        (lintegral (multinomialAncestors inLanes (extent + 1) space draws) function) =
      ENNReal.mul (ENNReal.finite inLanes.share)
        (ENNReal.additiveLaws.listSum (inLanes.list.map fun lane =>
          ENNReal.mul (drawWeight (draws lane))
            (lintegral (conditionalAncestors inLanes extent space child (draws, lane)) function))) := by
  rw [multinomialAncestors, Kernel.lintegral_finProduct_insert extent _ _ child draws measurable]
  refine (weighted_laneLaw inLanes space
    (Kernel.const _ (Measure.dirac _ (zeroParents inLanes (Lanes.fin (extent + 1)) child)))
    draws _).trans ?_
  refine congrArg (ENNReal.mul _)
    (congrArg ENNReal.additiveLaws.listSum (List.map_congr_left fun lane _ => ?_))
  rw [lintegral_conditionalAncestors inLanes extent space child draws lane measurable]

/-- The resampled population with child `child` marked. -/
theorem resampleMarked_measurable {ι : Type} (inLanes : Lanes ι) (extent : Nat)
    (space : Space α) (child : Fin (extent + 1)) :
    MeasurableMap (Space.product (markedSpace ι space) (ancestorSpace ι (Fin (extent + 1))))
      (markedSpace (Fin (extent + 1)) space)
      (fun pair => (fun position => ((pair.1.1 (pair.2 position)).1,
        meanWeight inLanes pair.1.1), child)) :=
  Space.pair_measurable
    (MeasurableMap.comp (resample_measurable inLanes space)
      (Space.pair_measurable
        (MeasurableMap.comp (Space.first_measurable _ _) (Space.first_measurable _ _))
        (Space.second_measurable _ _)))
    (MeasurableMap.constant _ _ child)

/-- Resample from the conditional ancestors of `child`, and mark `child`. -/
@[expose] noncomputable def childMove {ι : Type} (inLanes : Lanes ι) (extent : Nat)
    (space : Space α) (child : Fin (extent + 1)) :
    Kernel (markedSpace ι space) (markedSpace (Fin (extent + 1)) space) :=
  ((conditionalAncestors inLanes extent space child).attach
    (conditionalAncestorsFinite inLanes extent space child)).map _
    (resampleMarked_measurable inLanes extent space child)

noncomputable def childMoveFinite {ι : Type} (inLanes : Lanes ι) (extent : Nat)
    (space : Space α) (child : Fin (extent + 1)) :
    Kernel.IsSFinite (childMove inLanes extent space child) :=
  (Kernel.IsSFinite.attach (conditionalAncestorsFinite inLanes extent space child)).map _
    (resampleMarked_measurable inLanes extent space child)

theorem lintegral_childMove {ι : Type} (inLanes : Lanes ι) (extent : Nat)
    (space : Space α) (child : Fin (extent + 1)) (marked : (ι → α × NNReal) × ι)
    {function : ((Fin (extent + 1) → α × NNReal) × Fin (extent + 1)) → ENNReal}
    (measurable : ENNRealMeasurable (markedSpace (Fin (extent + 1)) space) function) :
    lintegral (childMove inLanes extent space child marked) function =
      lintegral (conditionalAncestors inLanes extent space child marked) fun parents =>
        function (fun position => ((marked.1 (parents position)).1, meanWeight inLanes marked.1),
          child) := by
  rw [childMove, Kernel.map_apply, lintegral_map _ _ _ measurable, Kernel.attach_apply,
    lintegral_map _ _ _ (measurable.comp (resampleMarked_measurable inLanes extent space child))]

/-- The conditional move of multinomial resampling: a uniform child takes the
marked lane as its parent and is marked, and every other child's parent is drawn
from the categorical law of the weights. -/
@[expose] noncomputable def resampleMove {ι : Type} (inLanes : Lanes ι) (extent : Nat)
    (space : Space α) : Kernel (markedSpace ι space) (markedSpace (Fin (extent + 1)) space) :=
  Kernel.weightedSum ((Lanes.fin (extent + 1)).list.map fun child =>
    ((Lanes.fin (extent + 1)).share, childMove inLanes extent space child))

noncomputable def childrenMoveFinite {ι : Type} (inLanes : Lanes ι) (extent : Nat)
    (space : Space α) : (children : List (Fin (extent + 1))) →
    Kernel.IsSFinite (Kernel.weightedSum (children.map fun child =>
      ((Lanes.fin (extent + 1)).share, childMove inLanes extent space child)))
  | [] => Kernel.IsSFinite.zero _ _
  | child :: rest => Kernel.IsSFinite.add
      ((childMoveFinite inLanes extent space child).smul _ True.intro)
      (childrenMoveFinite inLanes extent space rest)

noncomputable def resampleMoveFinite {ι : Type} (inLanes : Lanes ι) (extent : Nat)
    (space : Space α) : Kernel.IsSFinite (resampleMove inLanes extent space) :=
  childrenMoveFinite inLanes extent space _

theorem lintegral_resampleMove {ι : Type} (inLanes : Lanes ι) (extent : Nat)
    (space : Space α) (marked : (ι → α × NNReal) × ι)
    {function : ((Fin (extent + 1) → α × NNReal) × Fin (extent + 1)) → ENNReal}
    (measurable : ENNRealMeasurable (markedSpace (Fin (extent + 1)) space) function) :
    lintegral (resampleMove inLanes extent space marked) function =
      ENNReal.additiveLaws.listSum ((Lanes.fin (extent + 1)).list.map fun child =>
        ENNReal.mul (ENNReal.finite (Lanes.fin (extent + 1)).share)
          (lintegral (conditionalAncestors inLanes extent space child marked) fun parents =>
            function (fun position => ((marked.1 (parents position)).1,
              meanWeight inLanes marked.1), child))) := by
  rw [resampleMove, Kernel.lintegral_weightedSum, List.map_map]
  exact congrArg ENNReal.additiveLaws.listSum (List.map_congr_left fun child _ =>
    congrArg (ENNReal.mul _) (lintegral_childMove inLanes extent space child marked measurable))

/-- Multinomial resampling's marking is intertwined with `resampleMove`. -/
theorem resample_intertwines {ι : Type} (inLanes : Lanes ι) (extent : Nat) (space : Space α) :
    (resample inLanes (multinomialAncestors inLanes (extent + 1) space)
        (multinomialFinite inLanes (extent + 1) space)).comp
        (markedLane (Lanes.fin (extent + 1)) space) =
      (markedLane inLanes space).comp (resampleMove inLanes extent space) := by
  apply Kernel.ext
  intro draws
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  have childMeasurable : ∀ child, ENNRealMeasurable (ancestorSpace ι (Fin (extent + 1)))
      (fun parents => function (fun position => ((draws (parents position)).1,
        meanWeight inLanes draws), child)) := fun child =>
    measurable.comp (Space.pair_measurable
      (MeasurableMap.comp (resample_measurable inLanes space)
        (Kernel.pair_left_measurable (source := populationSpace ι space) draws))
      (MeasurableMap.constant _ _ child))
  rw [Kernel.comp_apply, Kernel.comp_apply,
    Measure.lintegral_bind _ _ measurable, Measure.lintegral_bind _ _ measurable,
    resample_apply, lintegral_map _ _ _ (Kernel.lintegral_measurable _ measurable),
    lintegral_markedLane inLanes draws (Kernel.lintegral_measurable _ measurable)]
  have marked : ∀ parents : Fin (extent + 1) → ι,
      lintegral (markedLane (Lanes.fin (extent + 1)) space
        (fun position => ((draws (parents position)).1, meanWeight inLanes draws))) function =
      ENNReal.mul (ENNReal.finite (Lanes.fin (extent + 1)).share)
        (ENNReal.additiveLaws.listSum ((Lanes.fin (extent + 1)).list.map fun child =>
          ENNReal.mul (ENNReal.finite (meanWeight inLanes draws))
            (function (fun position => ((draws (parents position)).1,
              meanWeight inLanes draws), child)))) := fun parents =>
    lintegral_markedLane _ _ measurable
  rw [lintegral_congr _ marked,
    lintegral_smul _ _ (ENNRealMeasurable.listSum_map _ fun child =>
      (childMeasurable child).const_mul _),
    lintegral_listSum_map _ _ fun child => (childMeasurable child).const_mul _]
  have each : ∀ child, lintegral (multinomialAncestors inLanes (extent + 1) space draws)
      (fun parents => ENNReal.mul (ENNReal.finite (meanWeight inLanes draws))
        (function (fun position => ((draws (parents position)).1,
          meanWeight inLanes draws), child))) =
      ENNReal.mul (ENNReal.finite inLanes.share)
        (ENNReal.additiveLaws.listSum (inLanes.list.map fun lane =>
          ENNReal.mul (drawWeight (draws lane))
            (lintegral (conditionalAncestors inLanes extent space child (draws, lane))
              fun parents => function (fun position => ((draws (parents position)).1,
                meanWeight inLanes draws), child)))) := fun child =>
    (lintegral_smul _ _ (childMeasurable child)).trans
      (weighted_ancestors inLanes extent space child draws (childMeasurable child))
  have moves : ∀ lane, lintegral (resampleMove inLanes extent space (draws, lane)) function =
      ENNReal.additiveLaws.listSum ((Lanes.fin (extent + 1)).list.map fun child =>
        ENNReal.mul (ENNReal.finite (Lanes.fin (extent + 1)).share)
          (lintegral (conditionalAncestors inLanes extent space child (draws, lane))
            fun parents => function (fun position => ((draws (parents position)).1,
              meanWeight inLanes draws), child))) := fun lane =>
    lintegral_resampleMove inLanes extent space (draws, lane) measurable
  simp only [each, moves, mul_listSum]
  refine Eq.trans ?_ (ENNReal.additiveLaws.listSum_comm (Lanes.fin (extent + 1)).list
    inLanes.list _)
  refine congrArg ENNReal.additiveLaws.listSum (List.map_congr_left fun child _ => ?_)
  refine congrArg ENNReal.additiveLaws.listSum (List.map_congr_left fun lane _ => ?_)
  rw [mul_left_comm (ENNReal.finite (Lanes.fin (extent + 1)).share),
    mul_left_comm (ENNReal.finite (Lanes.fin (extent + 1)).share) (drawWeight (draws lane))]

/-- Every child of `resampleMove` holds the marked lane's value at its marked
child. -/
theorem resample_retains {ι : Type} (inLanes : Lanes ι) (extent : Nat) (space : Space α) :
    Retains (Lanes.fin (extent + 1)) (resampleMove inLanes extent space) := by
  rintro ⟨draws, lane⟩
  unfold HoldsAt
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  have readMeasurable := measurable.comp (readMarked_measurable (Lanes.fin (extent + 1)) space)
  have pointMeasurable := measurable.comp
    (Kernel.pair_left_measurable (source := space) (target := markedSpace (Fin (extent + 1)) space)
      (reference (draws, lane)))
  rw [lintegral_map _ _ (readMarked_measurable (Lanes.fin (extent + 1)) space) measurable,
    lintegral_map _ _ (Kernel.pair_left_measurable (source := space) (reference (draws, lane)))
      measurable,
    lintegral_resampleMove inLanes extent space (draws, lane) readMeasurable,
    lintegral_resampleMove inLanes extent space (draws, lane) pointMeasurable]
  refine congrArg ENNReal.additiveLaws.listSum (List.map_congr_left fun child _ => ?_)
  refine congrArg (ENNReal.mul _) ?_
  have parentsMeasurable : ∀ {integrand : ((Fin (extent + 1) → α × NNReal) × Fin (extent + 1)) → ENNReal},
      ENNRealMeasurable (markedSpace (Fin (extent + 1)) space) integrand →
      ENNRealMeasurable (ancestorSpace ι (Fin (extent + 1))) (fun parents => integrand
        (fun position => ((draws (parents position)).1, meanWeight inLanes draws), child)) :=
    fun integrandMeasurable => integrandMeasurable.comp (Space.pair_measurable
      (MeasurableMap.comp (resample_measurable inLanes space)
        (Kernel.pair_left_measurable (source := populationSpace ι space) draws))
      (MeasurableMap.constant _ _ child))
  rw [lintegral_conditionalAncestors inLanes extent space child draws lane
      (parentsMeasurable readMeasurable),
    lintegral_conditionalAncestors inLanes extent space child draws lane
      (parentsMeasurable pointMeasurable)]
  refine lintegral_congr _ fun rest => ?_
  show function ((draws (Kernel.laneInsert child (lane, rest) child)).1, _) =
    function ((draws lane).1, _)
  rw [Kernel.laneInsert_self]

/-- Multinomial resampling is a conditional step for every target: its lift
composes the conditional law with `resampleMove`. -/
theorem conditional_resample {ι : Type} (inLanes : Lanes ι) (extent : Nat) (space : Space α)
    (target : Measure space) :
    ConditionalStep inLanes (Lanes.fin (extent + 1)) target target
      (resample inLanes (multinomialAncestors inLanes (extent + 1) space)
        (multinomialFinite inLanes (extent + 1) space))
      (fun conditional _ => conditional.comp (resampleMove inLanes extent space)) :=
  conditional_step_of_move inLanes (Lanes.fin (extent + 1)) target _
    (resampleMove inLanes extent space) (resampleMoveFinite inLanes extent space)
    (resample_intertwines inLanes extent space) (resample_retains inLanes extent space)


/-! ### Propagation -/

/-- The proposal retains its input through `parent`: `proposal x` is carried by
the values whose parent is `x`. A proposal on paths that extends its input path
retains it through the path's prefix. -/
@[expose] def ProposalRetains (proposal : Kernel space result) (parent : β → α)
    (parentMeasurable : MeasurableMap result space parent) : Prop :=
  ∀ input, (proposal input).map (fun value => (parent value, value))
      (Space.pair_measurable parentMeasurable (MeasurableMap.identity result)) =
    (proposal input).map (fun value => (input, value))
      (Kernel.pair_left_measurable (source := space) input)

/-- Under a retaining proposal, a value's parent reads as the input. -/
theorem lintegral_proposalRetains {proposal : Kernel space result} {parent : β → α}
    {parentMeasurable : MeasurableMap result space parent}
    (retains : ProposalRetains proposal parent parentMeasurable) (input : α)
    {function : α × β → ENNReal}
    (measurable : ENNRealMeasurable (Space.product space result) function) :
    lintegral (proposal input) (fun value => function (parent value, value)) =
      lintegral (proposal input) (fun value => function (input, value)) := by
  have integrals := congrArg (fun image => lintegral image function) (retains input)
  rw [lintegral_map _ _ (Space.pair_measurable parentMeasurable (MeasurableMap.identity result))
      measurable,
    lintegral_map _ _ (Kernel.pair_left_measurable (source := space) input) measurable]
    at integrals
  exact integrals

/-- One lane of a propagation: draw from the proposal at the lane's value and
multiply its weight by the increment. -/
@[expose] noncomputable def laneStep (proposal : Kernel space result)
    (proposalFinite : Kernel.IsSFinite proposal) (increment : α × β → NNReal)
    (incrementMeasurable : MeasurableMap (Space.product space result) weightSpace increment) :
    Kernel (Space.product space weightSpace) (Space.product result weightSpace) :=
  reweight (incrementKernel proposal proposalFinite increment incrementMeasurable)
    (incrementKernelFinite proposalFinite incrementMeasurable)

noncomputable def laneStepFinite {proposal : Kernel space result}
    (proposalFinite : Kernel.IsSFinite proposal) {increment : α × β → NNReal}
    (incrementMeasurable : MeasurableMap (Space.product space result) weightSpace increment) :
    Kernel.IsSFinite (laneStep proposal proposalFinite increment incrementMeasurable) :=
  (Kernel.IsSFinite.attach ((incrementKernelFinite proposalFinite incrementMeasurable).precomp
    Prod.fst (draw_value_measurable space))).map _ (reweight_pair_measurable space result)

theorem lintegral_laneStep (proposal : Kernel space result)
    (proposalFinite : Kernel.IsSFinite proposal) (increment : α × β → NNReal)
    (incrementMeasurable : MeasurableMap (Space.product space result) weightSpace increment)
    (draw : α × NNReal) {function : β × NNReal → ENNReal}
    (measurable : ENNRealMeasurable (Space.product result weightSpace) function) :
    lintegral (laneStep proposal proposalFinite increment incrementMeasurable draw) function =
      lintegral (proposal draw.1) fun value =>
        function (value, NNReal.mul draw.2 (increment (draw.1, value))) := by
  rw [laneStep, reweight_apply, lintegral_map _ _ (scale_weight_measurable result draw.2) measurable,
    incrementKernel_apply, lintegral_map _ _ (increment_value_measurable incrementMeasurable draw.1)
      (measurable.comp (scale_weight_measurable result draw.2))]

/-- Propagate every lane of a population independently by `laneStep`. -/
@[expose] noncomputable def propagate (extent : Nat) (proposal : Kernel space result)
    (proposalFinite : Kernel.IsSFinite proposal) (increment : α × β → NNReal)
    (incrementMeasurable : MeasurableMap (Space.product space result) weightSpace increment) :
    Kernel (populationSpace (Fin (extent + 1)) space) (populationSpace (Fin (extent + 1)) result) :=
  Kernel.finProduct (extent + 1)
    (fun lane => (laneStep proposal proposalFinite increment incrementMeasurable).precomp
      (fun draws : Fin (extent + 1) → α × NNReal => draws lane) (lane_measurable space lane))
    (fun lane => (laneStepFinite proposalFinite incrementMeasurable).precomp
      (fun draws : Fin (extent + 1) → α × NNReal => draws lane) (lane_measurable space lane))

/-- Propagate every lane but `lane`. -/
@[expose] noncomputable def otherLanes (extent : Nat) (proposal : Kernel space result)
    (proposalFinite : Kernel.IsSFinite proposal) (increment : α × β → NNReal)
    (incrementMeasurable : MeasurableMap (Space.product space result) weightSpace increment)
    (lane : Fin (extent + 1)) :
    Kernel (populationSpace (Fin (extent + 1)) space) (populationSpace (Fin extent) result) :=
  Kernel.finProduct extent
    (fun position => (laneStep proposal proposalFinite increment incrementMeasurable).precomp
      (fun draws : Fin (extent + 1) → α × NNReal => draws (Kernel.laneSkip lane position))
      (lane_measurable space (Kernel.laneSkip lane position)))
    (fun position => (laneStepFinite proposalFinite incrementMeasurable).precomp
      (fun draws : Fin (extent + 1) → α × NNReal => draws (Kernel.laneSkip lane position))
      (lane_measurable space (Kernel.laneSkip lane position)))

noncomputable def otherLanesFinite (extent : Nat) {proposal : Kernel space result}
    (proposalFinite : Kernel.IsSFinite proposal) {increment : α × β → NNReal}
    (incrementMeasurable : MeasurableMap (Space.product space result) weightSpace increment)
    (lane : Fin (extent + 1)) :
    Kernel.IsSFinite (otherLanes extent proposal proposalFinite increment incrementMeasurable lane) := by
  unfold otherLanes
  exact Kernel.IsSFinite.finProduct _ _ _

/-- The draw at `lane` of a marked population, beside a propagated value. -/
theorem markedDraw_measurable (space : Space α) (result : Space β) {extent : Nat}
    (lane : Fin (extent + 1)) :
    MeasurableMap (Space.product result (markedSpace (Fin (extent + 1)) space))
      (Space.product space weightSpace) (fun input => input.2.1 lane) :=
  MeasurableMap.comp (lane_measurable space lane)
    (MeasurableMap.comp (Space.first_measurable _ _) (Space.second_measurable _ _))

/-- Lane `lane`'s propagated draw: the given value, weighted by the lane's
weight times the increment from the lane's value. -/
@[expose] noncomputable def pinnedValue {extent : Nat} (increment : α × β → NNReal) (lane : Fin (extent + 1))
    (input : β × ((Fin (extent + 1) → α × NNReal) × Fin (extent + 1))) : β × NNReal :=
  (input.1, NNReal.mul (input.2.1 lane).2 (increment ((input.2.1 lane).1, input.1)))

theorem pinnedValue_measurable (space : Space α) (result : Space β) {extent : Nat}
    {increment : α × β → NNReal}
    (incrementMeasurable : MeasurableMap (Space.product space result) weightSpace increment)
    (lane : Fin (extent + 1)) :
    MeasurableMap (Space.product result (markedSpace (Fin (extent + 1)) space))
      (Space.product result weightSpace) (pinnedValue increment lane) :=
  Space.pair_measurable (Space.first_measurable _ _)
    (weight_mul_measurable
      (MeasurableMap.comp (Space.second_measurable space weightSpace)
        (markedDraw_measurable space result lane))
      (MeasurableMap.comp incrementMeasurable
        (Space.pair_measurable
          (MeasurableMap.comp (Space.first_measurable space weightSpace)
            (markedDraw_measurable space result lane))
          (Space.first_measurable _ _))))

/-- The inputs whose marked lane is `lane`. -/
theorem markedAt_measurable (space : Space α) (result : Space β) {extent : Nat}
    (lane : Fin (extent + 1)) :
    (Space.product result (markedSpace (Fin (extent + 1)) space)).Measurable
      (fun input => input.2.2 = lane) :=
  MeasurableMap.comp (Space.second_measurable (populationSpace _ space) (Space.discrete _))
    (Space.second_measurable result _) (Space.discrete_measurable fun marked => marked = lane)

/-- Lane `lane` of the pinned propagation: the pinned value when `lane` is
marked, and `laneStep` otherwise. -/
@[expose] noncomputable def pinnedFamily (extent : Nat) (proposal : Kernel space result)
    (proposalFinite : Kernel.IsSFinite proposal) (increment : α × β → NNReal)
    (incrementMeasurable : MeasurableMap (Space.product space result) weightSpace increment)
    (lane : Fin (extent + 1)) :
    Kernel (Space.product result (markedSpace (Fin (extent + 1)) space))
      (Space.product result weightSpace) :=
  Kernel.piecewise (fun input => input.2.2 = lane) (markedAt_measurable space result lane)
    (Kernel.deterministic (pinnedValue increment lane)
      (pinnedValue_measurable space result incrementMeasurable lane))
    ((laneStep proposal proposalFinite increment incrementMeasurable).precomp
      (fun input => input.2.1 lane) (markedDraw_measurable space result lane))

noncomputable def pinnedFamilyFinite (extent : Nat) {proposal : Kernel space result}
    (proposalFinite : Kernel.IsSFinite proposal) {increment : α × β → NNReal}
    (incrementMeasurable : MeasurableMap (Space.product space result) weightSpace increment)
    (lane : Fin (extent + 1)) :
    Kernel.IsSFinite
      (pinnedFamily extent proposal proposalFinite increment incrementMeasurable lane) := by
  unfold pinnedFamily
  exact Kernel.IsSFinite.piecewise
    (Kernel.IsSFinite.deterministic (pinnedValue increment lane)
      (pinnedValue_measurable space result incrementMeasurable lane))
    ((laneStepFinite proposalFinite incrementMeasurable).precomp
      (fun input : β × ((Fin (extent + 1) → α × NNReal) × Fin (extent + 1)) => input.2.1 lane)
      (markedDraw_measurable space result lane))
    (fun input => input.2.2 = lane) (markedAt_measurable space result lane)

theorem pinnedMark_measurable (space : Space α) (result : Space β) (extent : Nat) :
    MeasurableMap
      (Space.product (Space.product result (markedSpace (Fin (extent + 1)) space))
        (populationSpace (Fin (extent + 1)) result))
      (markedSpace (Fin (extent + 1)) result) (fun pair => (pair.2, pair.1.2.2)) :=
  Space.pair_measurable (Space.second_measurable _ _)
    (MeasurableMap.comp (Space.second_measurable _ (Space.discrete _))
      (MeasurableMap.comp (Space.second_measurable result _) (Space.first_measurable _ _)))

/-- Given a propagated value `y` and a marked population `(draws, k)`: lane `k`
takes `y` with its weight times the increment, every other lane propagates, and
`k` stays marked. -/
@[expose] noncomputable def pinnedMove (extent : Nat) (proposal : Kernel space result)
    (proposalFinite : Kernel.IsSFinite proposal) (increment : α × β → NNReal)
    (incrementMeasurable : MeasurableMap (Space.product space result) weightSpace increment) :
    Kernel (Space.product result (markedSpace (Fin (extent + 1)) space))
      (markedSpace (Fin (extent + 1)) result) :=
  (Kernel.attach (Kernel.finProduct (extent + 1)
      (pinnedFamily extent proposal proposalFinite increment incrementMeasurable)
      (pinnedFamilyFinite extent proposalFinite incrementMeasurable))
    (Kernel.IsSFinite.finProduct _ _ _)).map (fun pair => (pair.2, pair.1.2.2))
    (pinnedMark_measurable space result extent)

noncomputable def pinnedMoveFinite (extent : Nat) {proposal : Kernel space result}
    (proposalFinite : Kernel.IsSFinite proposal) {increment : α × β → NNReal}
    (incrementMeasurable : MeasurableMap (Space.product space result) weightSpace increment) :
    Kernel.IsSFinite (pinnedMove extent proposal proposalFinite increment incrementMeasurable) :=
  (Kernel.IsSFinite.attach (Kernel.IsSFinite.finProduct _ _ _)).map _ _

/-- The pinned move integrates the other lanes' propagation, with the pinned
value inserted at the marked lane. -/
theorem lintegral_pinnedMove (extent : Nat) (proposal : Kernel space result)
    (proposalFinite : Kernel.IsSFinite proposal) (increment : α × β → NNReal)
    (incrementMeasurable : MeasurableMap (Space.product space result) weightSpace increment)
    (value : β) (draws : Fin (extent + 1) → α × NNReal) (lane : Fin (extent + 1))
    {function : (Fin (extent + 1) → β × NNReal) × Fin (extent + 1) → ENNReal}
    (measurable : ENNRealMeasurable (markedSpace (Fin (extent + 1)) result) function) :
    lintegral (pinnedMove extent proposal proposalFinite increment incrementMeasurable
        (value, (draws, lane))) function =
      lintegral (otherLanes extent proposal proposalFinite increment incrementMeasurable lane draws)
        fun rest => function
          (Kernel.laneInsert lane (pinnedValue increment lane (value, (draws, lane)), rest), lane) := by
  have marked : ENNRealMeasurable (populationSpace (Fin (extent + 1)) result)
      (fun table => function (table, lane)) :=
    measurable.comp (markLane_measurable result lane)
  have moved : lintegral (pinnedMove extent proposal proposalFinite increment incrementMeasurable
      (value, (draws, lane))) function =
      lintegral (Kernel.finProduct (extent + 1)
          (pinnedFamily extent proposal proposalFinite increment incrementMeasurable)
          (pinnedFamilyFinite extent proposalFinite incrementMeasurable) (value, (draws, lane)))
        fun table => function (table, lane) := by
    rw [pinnedMove, Kernel.map_apply,
      lintegral_map _ _ (pinnedMark_measurable space result extent) measurable,
      Kernel.attach_apply,
      lintegral_map _ _ (Kernel.pair_left_measurable _)
        (measurable.comp (pinnedMark_measurable space result extent))]
  have pinned : Kernel.finProduct (extent + 1)
      (pinnedFamily extent proposal proposalFinite increment incrementMeasurable)
      (pinnedFamilyFinite extent proposalFinite incrementMeasurable) (value, (draws, lane)) =
      Kernel.finProduct (extent + 1)
        (Kernel.pinLane (fun position => (laneStep proposal proposalFinite increment
            incrementMeasurable).precomp (fun input : β × ((Fin (extent + 1) → α × NNReal) × Fin (extent + 1)) =>
              input.2.1 position)
            (markedDraw_measurable space result position)) lane
          (Kernel.deterministic (pinnedValue increment lane)
            (pinnedValue_measurable space result incrementMeasurable lane)))
        (Kernel.pinLaneFinite (fun position => (laneStepFinite proposalFinite incrementMeasurable).precomp
            (fun input : β × ((Fin (extent + 1) → α × NNReal) × Fin (extent + 1)) =>
              input.2.1 position) (markedDraw_measurable space result position)) lane
          (Kernel.IsSFinite.deterministic _ _)) (value, (draws, lane)) :=
    Kernel.finProduct_congr_at _ _ _ _ _ _ _ fun position => by
      by_cases same : position = lane
      · subst same
        unfold pinnedFamily Kernel.pinLane
        rw [ite_eq_left rfl]
        exact Kernel.piecewise_apply_of_mem _ _ _ _ _ rfl
      · unfold pinnedFamily Kernel.pinLane
        rw [ite_eq_right same]
        exact Kernel.piecewise_apply_of_not_mem _ _ _ _ _ fun marked => same marked.symm
  rw [moved, pinned, Kernel.lintegral_finProduct_pinned extent _ _ lane _
    (Kernel.IsSFinite.deterministic _ _) (value, (draws, lane))
    (pinnedValue increment lane (value, (draws, lane))) (Kernel.deterministic_apply _ _ _) marked]
  exact congrArg (fun measure => lintegral measure fun rest =>
      function (Kernel.laneInsert lane (pinnedValue increment lane (value, (draws, lane)), rest), lane))
    (Kernel.finProduct_congr_at _ _ _ _ _ _ _ fun _ => rfl)

/-- The conditional law after propagation: at `y`, draw a marked population from
`conditional` at `y`'s parent, and pin `y` at its marked lane. -/
@[expose] noncomputable def propagateConditional (extent : Nat) (proposal : Kernel space result)
    (proposalFinite : Kernel.IsSFinite proposal) (increment : α × β → NNReal)
    (incrementMeasurable : MeasurableMap (Space.product space result) weightSpace increment)
    (conditional : Kernel space (markedSpace (Fin (extent + 1)) space))
    (conditionalFinite : Kernel.IsSFinite conditional) (parent : β → α)
    (parentMeasurable : MeasurableMap result space parent) :
    Kernel result (markedSpace (Fin (extent + 1)) result) :=
  ((conditional.precomp parent parentMeasurable).attach
      (conditionalFinite.precomp parent parentMeasurable)).comp
    (pinnedMove extent proposal proposalFinite increment incrementMeasurable)

noncomputable def propagateConditionalFinite (extent : Nat) {proposal : Kernel space result}
    (proposalFinite : Kernel.IsSFinite proposal) {increment : α × β → NNReal}
    (incrementMeasurable : MeasurableMap (Space.product space result) weightSpace increment)
    {conditional : Kernel space (markedSpace (Fin (extent + 1)) space)}
    (conditionalFinite : Kernel.IsSFinite conditional) {parent : β → α}
    (parentMeasurable : MeasurableMap result space parent) :
    Kernel.IsSFinite (propagateConditional extent proposal proposalFinite increment
      incrementMeasurable conditional conditionalFinite parent parentMeasurable) :=
  Kernel.IsSFinite.comp (Kernel.IsSFinite.attach (conditionalFinite.precomp _ _))
    (pinnedMoveFinite extent proposalFinite incrementMeasurable)

theorem lintegral_propagateConditional (extent : Nat) (proposal : Kernel space result)
    (proposalFinite : Kernel.IsSFinite proposal) (increment : α × β → NNReal)
    (incrementMeasurable : MeasurableMap (Space.product space result) weightSpace increment)
    (conditional : Kernel space (markedSpace (Fin (extent + 1)) space))
    (conditionalFinite : Kernel.IsSFinite conditional) (parent : β → α)
    (parentMeasurable : MeasurableMap result space parent) (value : β)
    {function : (Fin (extent + 1) → β × NNReal) × Fin (extent + 1) → ENNReal}
    (measurable : ENNRealMeasurable (markedSpace (Fin (extent + 1)) result) function) :
    lintegral (propagateConditional extent proposal proposalFinite increment incrementMeasurable
        conditional conditionalFinite parent parentMeasurable value) function =
      lintegral (conditional (parent value)) fun marked =>
        lintegral (pinnedMove extent proposal proposalFinite increment incrementMeasurable
          (value, marked)) function := by
  rw [propagateConditional, Kernel.comp_apply, Measure.lintegral_bind _ _ measurable,
    Kernel.attach_apply, Kernel.precomp_apply,
    lintegral_map _ _ (Kernel.pair_left_measurable (source := result) value)
      (Kernel.lintegral_measurable _ measurable)]

/-- The increment-weighted pinned integral, jointly in the parent value and the
marked population. -/
theorem pinnedIncrement_measurable (extent : Nat) (proposal : Kernel space result)
    (proposalFinite : Kernel.IsSFinite proposal) (increment : α × β → NNReal)
    (incrementMeasurable : MeasurableMap (Space.product space result) weightSpace increment)
    {function : (Fin (extent + 1) → β × NNReal) × Fin (extent + 1) → ENNReal}
    (measurable : ENNRealMeasurable (markedSpace (Fin (extent + 1)) result) function) :
    ENNRealMeasurable (Space.product space (markedSpace (Fin (extent + 1)) space))
      (fun pair => lintegral (proposal pair.1) fun value =>
        ENNReal.mul (ENNReal.finite (increment (pair.1, value)))
          (lintegral (pinnedMove extent proposal proposalFinite increment incrementMeasurable
            (value, pair.2)) function)) := by
  have moved : ENNRealMeasurable (Space.product result (markedSpace (Fin (extent + 1)) space))
      (fun pair => lintegral (pinnedMove extent proposal proposalFinite increment
        incrementMeasurable pair) function) :=
    Kernel.lintegral_measurable _ measurable
  have weighed : ENNRealMeasurable
      (Space.product (Space.product space (markedSpace (Fin (extent + 1)) space)) result)
      (fun triple => ENNReal.mul (ENNReal.finite (increment (triple.1.1, triple.2)))
        (lintegral (pinnedMove extent proposal proposalFinite increment incrementMeasurable
          (triple.2, triple.1.2)) function)) :=
    ENNRealMeasurable.mul
      (finite_weight_measurable (MeasurableMap.comp incrementMeasurable
        (Space.pair_measurable
          (MeasurableMap.comp (Space.first_measurable _ _) (Space.first_measurable _ _))
          (Space.second_measurable _ _))))
      (moved.comp (Space.pair_measurable (Space.second_measurable _ _)
        (MeasurableMap.comp (Space.second_measurable _ _) (Space.first_measurable _ _))))
  exact Kernel.lintegral_measurable_joint (proposal.precomp Prod.fst (Space.first_measurable _ _))
      (proposalFinite.precomp Prod.fst (Space.first_measurable _ _))
      (function := fun pair value => ENNReal.mul (ENNReal.finite (increment (pair.1, value)))
        (lintegral (pinnedMove extent proposal proposalFinite increment incrementMeasurable
          (value, pair.2)) function)) weighed

/-- The extended target after propagation, read before it: each marked
population weighs the increment from its marked lane's value and pins the
propagated value there. -/
theorem extended_propagate (extent : Nat) (proposal : Kernel space result)
    (proposalFinite : Kernel.IsSFinite proposal) (increment : α × β → NNReal)
    (incrementMeasurable : MeasurableMap (Space.product space result) weightSpace increment)
    (population : Measure (populationSpace (Fin (extent + 1)) space))
    {function : (Fin (extent + 1) → β × NNReal) × Fin (extent + 1) → ENNReal}
    (measurable : ENNRealMeasurable (markedSpace (Fin (extent + 1)) result) function) :
    lintegral (extended (Lanes.fin (extent + 1))
        (population.bind (propagate extent proposal proposalFinite increment incrementMeasurable)))
        function =
      lintegral (extended (Lanes.fin (extent + 1)) population) fun marked =>
        lintegral (proposal (reference marked)) fun value =>
          ENNReal.mul (ENNReal.finite (increment (reference marked, value)))
            (lintegral (pinnedMove extent proposal proposalFinite increment incrementMeasurable
              (value, marked)) function) := by
  have moved : ENNRealMeasurable (Space.product result (markedSpace (Fin (extent + 1)) space))
      (fun pair => lintegral (pinnedMove extent proposal proposalFinite increment
        incrementMeasurable pair) function) :=
    Kernel.lintegral_measurable _ measurable
  have joint := pinnedIncrement_measurable extent proposal proposalFinite increment
    incrementMeasurable measurable
  have weighted : ENNRealMeasurable (markedSpace (Fin (extent + 1)) space) (fun marked =>
      lintegral (proposal (reference marked)) fun value =>
        ENNReal.mul (ENNReal.finite (increment (reference marked, value)))
          (lintegral (pinnedMove extent proposal proposalFinite increment incrementMeasurable
            (value, marked)) function)) :=
    joint.comp (readMarked_measurable (Lanes.fin (extent + 1)) space)
  have marking : ENNRealMeasurable (populationSpace (Fin (extent + 1)) result) (fun table =>
      lintegral (markedLane (Lanes.fin (extent + 1)) result table) function) :=
    Kernel.lintegral_measurable _ measurable
  have term : ∀ lane : Fin (extent + 1), ENNRealMeasurable
      (populationSpace (Fin (extent + 1)) result)
      (fun table => ENNReal.mul (drawWeight (table lane)) (function (table, lane))) := fun lane =>
    ENNRealMeasurable.mul ((drawWeight_measurable result).comp (lane_measurable result lane))
      (measurable.comp (markLane_measurable result lane))
  unfold extended
  rw [Measure.lintegral_bind _ _ measurable, Measure.lintegral_bind _ _ marking,
    Measure.lintegral_bind _ _ weighted]
  refine lintegral_congr _ fun draws => ?_
  have marks : ∀ table, lintegral (markedLane (Lanes.fin (extent + 1)) result table) function =
      ENNReal.mul (ENNReal.finite (Lanes.fin (extent + 1)).share)
        (ENNReal.additiveLaws.listSum ((Lanes.fin (extent + 1)).list.map fun lane =>
          ENNReal.mul (drawWeight (table lane)) (function (table, lane)))) := fun table =>
    lintegral_markedLane _ table measurable
  rw [lintegral_congr _ marks,
    lintegral_smul _ _ (ENNRealMeasurable.listSum_map _ term),
    lintegral_listSum_map _ _ term, lintegral_markedLane _ draws weighted]
  refine congrArg (ENNReal.mul _)
    (congrArg ENNReal.additiveLaws.listSum (List.map_congr_left fun lane _ => ?_))
  have restMeasurable : ∀ value : β × NNReal, ENNRealMeasurable
      (populationSpace (Fin extent) result)
      (fun rest => function (Kernel.laneInsert lane (value, rest), lane)) := fun value =>
    measurable.comp (Space.pair_measurable
      (MeasurableMap.comp (Kernel.laneInsert_measurable lane) (Kernel.pair_left_measurable value))
      (MeasurableMap.constant _ _ lane))
  have split : lintegral (propagate extent proposal proposalFinite increment incrementMeasurable
      draws) (fun table => ENNReal.mul (drawWeight (table lane)) (function (table, lane))) =
      lintegral (laneStep proposal proposalFinite increment incrementMeasurable (draws lane))
        fun value => ENNReal.mul (drawWeight value)
          (lintegral (otherLanes extent proposal proposalFinite increment incrementMeasurable
            lane draws) fun rest => function (Kernel.laneInsert lane (value, rest), lane)) := by
    have inserted := Kernel.lintegral_finProduct_insert extent _
      (fun position => (laneStepFinite proposalFinite incrementMeasurable).precomp
        (fun draws : Fin (extent + 1) → α × NNReal => draws position)
        (lane_measurable space position)) lane draws (term lane)
    simp only [Kernel.laneInsert_self] at inserted
    exact inserted.trans (lintegral_congr _ fun value =>
      lintegral_smul _ _ (restMeasurable value))
  have restFinite := (otherLanesFinite extent proposalFinite incrementMeasurable lane).measure draws
  have outer : ENNRealMeasurable (Space.product result weightSpace) (fun value =>
      ENNReal.mul (drawWeight value)
        (lintegral (otherLanes extent proposal proposalFinite increment incrementMeasurable
          lane draws) fun rest => function (Kernel.laneInsert lane (value, rest), lane))) :=
    ENNRealMeasurable.mul (drawWeight_measurable result)
      (Kernel.lintegral_measurable_joint (Kernel.const _ _) (Kernel.IsSFinite.const _ restFinite)
        (function := fun value rest => function (Kernel.laneInsert lane (value, rest), lane))
        (measurable.comp (Space.pair_measurable
          (MeasurableMap.comp (Kernel.laneInsert_measurable lane) (MeasurableMap.identity _))
          (MeasurableMap.constant _ _ lane))))
  have inner : ENNRealMeasurable result (fun value =>
      ENNReal.mul (ENNReal.finite (increment (reference (draws, lane), value)))
        (lintegral (pinnedMove extent proposal proposalFinite increment incrementMeasurable
          (value, (draws, lane))) function)) :=
    ENNRealMeasurable.mul
      (finite_weight_measurable (MeasurableMap.comp incrementMeasurable
        (Kernel.pair_left_measurable (source := space) (reference (draws, lane)))))
      (moved.comp (Space.pair_measurable (MeasurableMap.identity _)
        (MeasurableMap.constant _ _ (draws, lane))))
  rw [split, lintegral_laneStep _ _ _ _ (draws lane) outer, drawWeight, ← lintegral_smul _ _ inner]
  refine lintegral_congr _ fun value => ?_
  rw [lintegral_pinnedMove extent proposal proposalFinite increment incrementMeasurable value draws
    lane measurable]
  unfold drawWeight
  rw [← ENNReal.finite_mul_finite, ENNReal.mul_assoc]
  rfl

/-- Propagation is a conditional step when the proposal retains its input
through `parent` and the stage is SeqRN from `source` to `target`. Its lift
draws the marked population at the propagated value's parent and pins the value
at the marked lane (`propagateConditional`). -/
theorem conditional_propagate (extent : Nat) (source : Measure space) (target : Measure result)
    (proposal : Kernel space result) (proposalFinite : Kernel.IsSFinite proposal)
    (increment : α × β → NNReal)
    (incrementMeasurable : MeasurableMap (Space.product space result) weightSpace increment)
    (parent : β → α) (parentMeasurable : MeasurableMap result space parent)
    (retains : ProposalRetains proposal parent parentMeasurable)
    (rn : SeqRN source target proposal increment) :
    ConditionalStep (Lanes.fin (extent + 1)) (Lanes.fin (extent + 1)) source target
      (propagate extent proposal proposalFinite increment incrementMeasurable)
      (fun conditional finite => propagateConditional extent proposal proposalFinite increment
        incrementMeasurable conditional finite parent parentMeasurable) := by
  intro population conditional finite law
  constructor
  · show target.bind (propagateConditional extent proposal proposalFinite increment
        incrementMeasurable conditional finite parent parentMeasurable) =
      extended (Lanes.fin (extent + 1))
        (population.bind (propagate extent proposal proposalFinite increment incrementMeasurable))
    refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
    have moved : ENNRealMeasurable (Space.product result (markedSpace (Fin (extent + 1)) space))
        (fun pair => lintegral (pinnedMove extent proposal proposalFinite increment
          incrementMeasurable pair) function) :=
      Kernel.lintegral_measurable _ measurable
    have joint := pinnedIncrement_measurable extent proposal proposalFinite increment
      incrementMeasurable measurable
    have folded : ENNRealMeasurable result (fun value =>
        lintegral (conditional (parent value)) fun marked =>
          lintegral (pinnedMove extent proposal proposalFinite increment incrementMeasurable
            (value, marked)) function) :=
      Kernel.lintegral_measurable_joint (conditional.precomp parent parentMeasurable)
        (finite.precomp parent parentMeasurable)
        (function := fun value marked => lintegral (pinnedMove extent proposal proposalFinite
          increment incrementMeasurable (value, marked)) function) moved
    have lifted : lintegral (target.bind (propagateConditional extent proposal proposalFinite
        increment incrementMeasurable conditional finite parent parentMeasurable)) function =
        lintegral target fun value => lintegral (conditional (parent value)) fun marked =>
          lintegral (pinnedMove extent proposal proposalFinite increment incrementMeasurable
            (value, marked)) function := by
      rw [Measure.lintegral_bind _ _ measurable]
      exact lintegral_congr _ fun value => lintegral_propagateConditional extent proposal
        proposalFinite increment incrementMeasurable conditional finite parent parentMeasurable
        value measurable
    rw [lifted, ← rn _ folded,
      extended_propagate extent proposal proposalFinite increment incrementMeasurable population
        measurable,
      ← law.disintegrates,
      Measure.lintegral_bind _ _ (joint.comp (readMarked_measurable (Lanes.fin (extent + 1)) space))]
    refine lintegral_congr _ fun point => ?_
    have held : lintegral (conditional point) (fun marked =>
        lintegral (proposal (reference marked)) fun value =>
          ENNReal.mul (ENNReal.finite (increment (reference marked, value)))
            (lintegral (pinnedMove extent proposal proposalFinite increment incrementMeasurable
              (value, marked)) function)) =
        lintegral (conditional point) (fun marked =>
          lintegral (proposal point) fun value =>
            ENNReal.mul (ENNReal.finite (increment (point, value)))
              (lintegral (pinnedMove extent proposal proposalFinite increment incrementMeasurable
                (value, marked)) function)) :=
      lintegral_holdsAt (law.pinned point) joint
    have incrementAt : MeasurableMap result weightSpace (fun value => increment (point, value)) :=
      MeasurableMap.comp incrementMeasurable (Kernel.pair_left_measurable (source := space) point)
    have swapped : lintegral (conditional point) (fun marked =>
        lintegral (proposal point) fun value =>
          ENNReal.mul (ENNReal.finite (increment (point, value)))
            (lintegral (pinnedMove extent proposal proposalFinite increment incrementMeasurable
              (value, marked)) function)) =
        lintegral (proposal point) (fun value =>
          lintegral (conditional point) fun marked =>
            ENNReal.mul (ENNReal.finite (increment (point, value)))
              (lintegral (pinnedMove extent proposal proposalFinite increment incrementMeasurable
                (value, marked)) function)) :=
      lintegral_lintegral_swap (conditional point) (proposal point) (finite.measure point)
        (proposalFinite.measure point)
        (function := fun pair => ENNReal.mul (ENNReal.finite (increment (point, pair.2)))
          (lintegral (pinnedMove extent proposal proposalFinite increment incrementMeasurable
            (pair.2, pair.1)) function))
        (ENNRealMeasurable.mul
          (finite_weight_measurable (MeasurableMap.comp incrementAt (Space.second_measurable _ _)))
          (moved.comp (Space.swap_measurable _ _)))
    have kept : lintegral (proposal point) (fun value =>
        ENNReal.mul (ENNReal.finite (increment (point, value)))
          (lintegral (conditional (parent value)) fun marked =>
            lintegral (pinnedMove extent proposal proposalFinite increment incrementMeasurable
              (value, marked)) function)) =
        lintegral (proposal point) (fun value =>
          ENNReal.mul (ENNReal.finite (increment (point, value)))
            (lintegral (conditional point) fun marked =>
              lintegral (pinnedMove extent proposal proposalFinite increment incrementMeasurable
                (value, marked)) function)) :=
      lintegral_proposalRetains retains point
        (function := fun pair => ENNReal.mul (ENNReal.finite (increment (point, pair.2)))
          (lintegral (conditional pair.1) fun marked =>
            lintegral (pinnedMove extent proposal proposalFinite increment incrementMeasurable
              (pair.2, marked)) function))
        (ENNRealMeasurable.mul
          (finite_weight_measurable (MeasurableMap.comp incrementAt (Space.second_measurable _ _)))
          (Kernel.lintegral_measurable_joint
            (conditional.precomp Prod.fst (Space.first_measurable _ _))
            (finite.precomp Prod.fst (Space.first_measurable _ _))
            (function := fun pair marked => lintegral (pinnedMove extent proposal proposalFinite
              increment incrementMeasurable (pair.2, marked)) function)
            (moved.comp (Space.pair_measurable
              (MeasurableMap.comp (Space.second_measurable _ _) (Space.first_measurable _ _))
              (Space.second_measurable _ _)))))
    rw [held, swapped, kept]
    refine lintegral_congr _ fun value => ?_
    exact (lintegral_smul (conditional point) _
      (moved.comp (Kernel.pair_left_measurable (source := result) value))).symm
  · intro value
    show HoldsAt (Lanes.fin (extent + 1)) value (propagateConditional extent proposal
      proposalFinite increment incrementMeasurable conditional finite parent parentMeasurable value)
    unfold HoldsAt
    refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
    have read := measurable.comp (readMarked_measurable (Lanes.fin (extent + 1)) result)
    have fixed := measurable.comp (Kernel.pair_left_measurable (source := result) value)
    rw [lintegral_map _ _ (readMarked_measurable (Lanes.fin (extent + 1)) result) measurable,
      lintegral_map _ _ (Kernel.pair_left_measurable (source := result) value) measurable,
      lintegral_propagateConditional extent proposal proposalFinite increment incrementMeasurable
        conditional finite parent parentMeasurable value read,
      lintegral_propagateConditional extent proposal proposalFinite increment incrementMeasurable
        conditional finite parent parentMeasurable value fixed]
    refine lintegral_congr _ fun marked => ?_
    rcases marked with ⟨draws, lane⟩
    rw [lintegral_pinnedMove extent proposal proposalFinite increment incrementMeasurable value
        draws lane read,
      lintegral_pinnedMove extent proposal proposalFinite increment incrementMeasurable value
        draws lane fixed]
    refine lintegral_congr _ fun rest => ?_
    simp only [reference, Kernel.laneInsert_self, pinnedValue]


/-! ### Replication -/

/-- A population of `extent + 1` empty lanes, each of weight one. -/
@[expose] noncomputable def emptyPopulation (extent : Nat) : Fin (extent + 1) → Unit × NNReal :=
  fun _ => ((), NNReal.one)

/-- The empty population's marked lanes are a probability: every lane has weight
one. -/
theorem markedLane_empty_probability (extent : Nat) :
    Measure.IsProbability (markedLane (Lanes.fin (extent + 1)) (Space.discrete Unit)
      (emptyPopulation extent)) := by
  refine ⟨?_⟩
  have total := lintegral_const (markedLane (Lanes.fin (extent + 1)) (Space.discrete Unit)
    (emptyPopulation extent)) ENNReal.one
  rw [lintegral_markedLane _ _ (ENNRealMeasurable.constant _ ENNReal.one), ENNReal.one_mul]
    at total
  rw [← total]
  simp only [ENNReal.mul_one]
  exact (Lanes.fin (extent + 1)).average_const ENNReal.one

/-- The empty population's conditional law: its marked lanes, at the one point. -/
@[expose] noncomputable def emptyConditional (extent : Nat) :
    Kernel (Space.discrete Unit) (markedSpace (Fin (extent + 1)) (Space.discrete Unit)) :=
  Kernel.const _ (markedLane (Lanes.fin (extent + 1)) (Space.discrete Unit) (emptyPopulation extent))

noncomputable def emptyConditionalFinite (extent : Nat) :
    Kernel.IsSFinite (emptyConditional extent) :=
  Kernel.IsSFinite.ofMarkov fun _ => markedLane_empty_probability extent

theorem emptyConditional_law (extent : Nat) :
    ConditionalLaw (Lanes.fin (extent + 1))
      (Measure.dirac (populationSpace (Fin (extent + 1)) (Space.discrete Unit))
        (emptyPopulation extent))
      (Measure.dirac (Space.discrete Unit) ()) (emptyConditional extent) :=
  ⟨(Measure.dirac_bind () (emptyConditional extent)).trans
      (Measure.dirac_bind (emptyPopulation extent)
        (markedLane (Lanes.fin (extent + 1)) (Space.discrete Unit))).symm,
    fun _ => rfl⟩

theorem replicate_weight_measurable {weight : β → NNReal}
    (weightMeasurable : MeasurableMap result weightSpace weight) :
    MeasurableMap (Space.product (Space.discrete Unit) result) weightSpace
      (fun pair => weight pair.2) :=
  MeasurableMap.comp weightMeasurable (Space.second_measurable _ _)

/-- Replicate: draw every lane independently from `draw` and weigh it by
`weight`, by propagating the empty population. -/
@[expose] noncomputable def replicate (extent : Nat) (draw : Measure result)
    (drawFinite : Measure.SFinite draw) (weight : β → NNReal)
    (weightMeasurable : MeasurableMap result weightSpace weight) :
    Measure (populationSpace (Fin (extent + 1)) result) :=
  (Measure.dirac (populationSpace (Fin (extent + 1)) (Space.discrete Unit))
      (emptyPopulation extent)).bind
    (propagate extent (Kernel.const (Space.discrete Unit) draw)
      (Kernel.IsSFinite.const _ drawFinite) (fun pair => weight pair.2)
      (replicate_weight_measurable weightMeasurable))

/-- The conditional law of a replicated population: every other lane draws from
`draw`, and the marked lane holds the given value. -/
@[expose] noncomputable def replicateConditional (extent : Nat) (draw : Measure result)
    (drawFinite : Measure.SFinite draw) (weight : β → NNReal)
    (weightMeasurable : MeasurableMap result weightSpace weight) :
    Kernel result (markedSpace (Fin (extent + 1)) result) :=
  propagateConditional extent (Kernel.const (Space.discrete Unit) draw)
    (Kernel.IsSFinite.const _ drawFinite) (fun pair => weight pair.2)
    (replicate_weight_measurable weightMeasurable) (emptyConditional extent)
    (emptyConditionalFinite extent) (fun _ => ()) (MeasurableMap.constant _ _ ())

/-- Replication from the one point is SeqRN onto the draw weighed by `weight`. -/
theorem replicate_seq_rn (draw : Measure result) {weight : β → NNReal}
    (weightMeasurable : MeasurableMap result weightSpace weight) :
    SeqRN (Measure.dirac (Space.discrete Unit) ())
      (draw.withDensity fun value => ENNReal.finite (weight value))
      (Kernel.const (Space.discrete Unit) draw) (fun pair => weight pair.2) := by
  intro function measurable
  rw [lintegral_withDensity _ (finite_weight_measurable weightMeasurable) measurable]
  exact lintegral_dirac (Space.discrete Unit) ()
    (Kernel.lintegral_measurable (Kernel.const (Space.discrete Unit) draw)
      (ENNRealMeasurable.mul (finite_weight_measurable weightMeasurable) measurable))

/-- A replicated population has a conditional law for the draw weighed by
`weight`: the ADH extended target of independent weighted draws. It takes an
s-finite draw and any weight, and no normalization. -/
theorem conditional_replicate (extent : Nat) (draw : Measure result)
    (drawFinite : Measure.SFinite draw) (weight : β → NNReal)
    (weightMeasurable : MeasurableMap result weightSpace weight) :
    ConditionalLaw (Lanes.fin (extent + 1))
      (replicate extent draw drawFinite weight weightMeasurable)
      (draw.withDensity fun value => ENNReal.finite (weight value))
      (replicateConditional extent draw drawFinite weight weightMeasurable) :=
  conditional_propagate extent (Measure.dirac (Space.discrete Unit) ()) _
    (Kernel.const (Space.discrete Unit) draw) (Kernel.IsSFinite.const _ drawFinite)
    (fun pair => weight pair.2) (replicate_weight_measurable weightMeasurable) (fun _ => ())
    (MeasurableMap.constant _ _ ()) (fun _ => rfl) (replicate_seq_rn draw weightMeasurable)
    _ (emptyConditional extent) (emptyConditionalFinite extent) (emptyConditional_law extent)

/-- A properly weighted draw is a replicated draw: weighing the properly
weighted law by its weight coordinate and forgetting the weight gives the
target. So independent properly weighted draws are `replicate` with the properly
weighted law as `draw` and the weight coordinate as `weight`, and the target is
the marked lane's value read through the first coordinate. -/
theorem properlyWeighted_replicate_target {target : Measure space}
    {weighted : Measure (Space.product space weightSpace)}
    (properlyWeighted : ProperlyWeighted target weighted) :
    (weighted.withDensity fun draw => ENNReal.finite draw.2).map Prod.fst
      (draw_value_measurable space) = target :=
  properlyWeighted.change

/-! ### Stages on paths -/

/-- A stage's target on paths: the source's semiproduct with the proposal,
weighed by the increment. -/
@[expose] noncomputable def pathTarget (source : Measure space) (proposal : Kernel space result)
    (proposalFinite : Kernel.IsSFinite proposal) (increment : α × β → NNReal) :
    Measure (Space.product space result) :=
  (source.semiproduct proposal proposalFinite).withDensity fun pair =>
    ENNReal.finite (increment pair)

/-- Extending the path by the proposal is SeqRN onto the path target, with the
increment read at the extended path. -/
theorem seq_rn_path (source : Measure space) (proposal : Kernel space result)
    (proposalFinite : Kernel.IsSFinite proposal) {increment : α × β → NNReal}
    (incrementMeasurable : MeasurableMap (Space.product space result) weightSpace increment) :
    SeqRN source (pathTarget source proposal proposalFinite increment)
      (proposal.attach proposalFinite) (fun pair => increment pair.2) := by
  intro function measurable
  rw [pathTarget, lintegral_withDensity _ (finite_weight_measurable incrementMeasurable) measurable,
    lintegral_semiproduct _ _ _
      (ENNRealMeasurable.mul (finite_weight_measurable incrementMeasurable) measurable)]
  refine lintegral_congr _ fun input => ?_
  rw [Kernel.attach_apply]
  exact lintegral_map _ _ (Kernel.pair_left_measurable (source := space) input)
    (ENNRealMeasurable.mul (finite_weight_measurable incrementMeasurable) measurable)

/-- Extending the path retains the path's prefix. -/
theorem attach_retains (proposal : Kernel space result)
    (proposalFinite : Kernel.IsSFinite proposal) :
    ProposalRetains (proposal.attach proposalFinite) Prod.fst
      (Space.first_measurable space result) := by
  intro input
  rw [Kernel.attach_apply, Measure.map_comp, Measure.map_comp]
  exact Space.pair_measurable (Space.first_measurable _ _) (MeasurableMap.identity _)

/-- The path target's last coordinate is the stage's target. -/
theorem pathTarget_map {source : Measure space} {target : Measure result}
    {proposal : Kernel space result} (proposalFinite : Kernel.IsSFinite proposal)
    {increment : α × β → NNReal}
    (incrementMeasurable : MeasurableMap (Space.product space result) weightSpace increment)
    (rn : SeqRN source target proposal increment) :
    (pathTarget source proposal proposalFinite increment).map Prod.snd
      (Space.second_measurable space result) = target := by
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  have last := measurable.comp (Space.second_measurable space result)
  rw [lintegral_map _ _ (Space.second_measurable space result) measurable, pathTarget,
    lintegral_withDensity _ (finite_weight_measurable incrementMeasurable) last,
    lintegral_semiproduct _ _ _
      (ENNRealMeasurable.mul (finite_weight_measurable incrementMeasurable) last)]
  exact rn function measurable

/-- A SeqRN stage lifted to paths is a conditional step: propagating paths by
the attached proposal carries every conditional law for the source to one for
the path target, whose last coordinate is the stage's target (`pathTarget_map`). -/
theorem conditional_propagate_path (extent : Nat) (source : Measure space)
    (proposal : Kernel space result) (proposalFinite : Kernel.IsSFinite proposal)
    {increment : α × β → NNReal}
    (incrementMeasurable : MeasurableMap (Space.product space result) weightSpace increment) :
    ConditionalStep (Lanes.fin (extent + 1)) (Lanes.fin (extent + 1)) source
      (pathTarget source proposal proposalFinite increment)
      (propagate extent (proposal.attach proposalFinite) (Kernel.IsSFinite.attach proposalFinite)
        (fun pair => increment pair.2)
        (MeasurableMap.comp incrementMeasurable (Space.second_measurable _ _)))
      (fun conditional finite => propagateConditional extent (proposal.attach proposalFinite)
        (Kernel.IsSFinite.attach proposalFinite) (fun pair => increment pair.2)
        (MeasurableMap.comp incrementMeasurable (Space.second_measurable _ _)) conditional finite
        Prod.fst (Space.first_measurable space result)) :=
  conditional_propagate extent source _ _ _ _ _ Prod.fst (Space.first_measurable space result)
    (attach_retains proposal proposalFinite)
    (seq_rn_path source proposal proposalFinite incrementMeasurable)

end

end Problib.Inference
