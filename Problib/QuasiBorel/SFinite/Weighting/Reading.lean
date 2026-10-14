import Problib.QuasiBorel.SFinite.Weighting
import Problib.QuasiBorel.Measurable.StandardBorel

/-!
# Reading counted proper weighting at first order

A measurable reading of a quasi-Borel space `Y` into a measurable space reads
each lane of a population as a first-order weighted draw (`populationRead`).
The reading carries the expected empirical measure of a sampler to the
expected empirical measure of its read population
(`empiricalBarycenter_read`). A sampler properly weighted for `μ` therefore
reads as a population invariant for the read target, Inv_N of
`Problib.Inference.EmpiricalInvariant` (`ProperlyWeightedLaw.empiricalInvariant`).

On the space a standard Borel space generates, the induced measurable
structure is the original one, so reading by the identity loses nothing. There
the counted contract is Inv_N (`properlyWeightedLaw_iff_empiricalInvariant`),
and at count one it is first-order proper weighting of the pair law
(`properlyWeightedLaw_one_iff_properlyWeighted`).
-/

set_option autoImplicit false

namespace Problib.QuasiBorel.SFinite

open Problib.Measure hiding Space
open Problib.Measure.Real (borel)
open Problib.Real (ENNReal NNReal)

universe u v

variable {space : Space.{0, u} realSource} {β : Type v} {firstOrder : Problib.Measure.Space β}
  {read : space.Carrier → β}

/-! ### Reading lanes -/

/-- A lane read as a first-order weighted draw. -/
def laneRead (read : space.Carrier → β) (lane : (Lane space).Carrier) : β × NNReal :=
  (read lane.1, lane.2)

theorem laneRead_measurable (measurable : MeasurableMap space.toMeasurable firstOrder read) :
    MeasurableMap (Lane space).toMeasurable
      (Problib.Measure.Space.product firstOrder Problib.Inference.weightSpace) (laneRead read) := by
  apply Space.measurableMap_iff_random.mpr
  intro _ accepted
  exact Problib.Measure.Space.pair_measurable
    (MeasurableMap.comp measurable (Space.random_measurable accepted.1)) accepted.2

/-- A population read lane by lane as first-order weighted draws. -/
def populationRead (read : space.Carrier → β) {count : Nat}
    (population : (Population space count).Carrier) : Fin count → β × NNReal :=
  fun lane => laneRead read (population lane)

theorem populationRead_measurable (count : Nat)
    (measurable : MeasurableMap space.toMeasurable firstOrder read) :
    MeasurableMap (Population space count).toMeasurable
      (Problib.Inference.populationSpace (Fin count) firstOrder) (populationRead read) := by
  apply Space.measurableMap_iff_random.mpr
  intro _ accepted
  apply Problib.Measure.Space.pi_measurable
  intro lane
  exact Problib.Measure.Space.pair_measurable
    (MeasurableMap.comp measurable (Space.random_measurable (accepted lane).1)) (accepted lane).2

/-- Reading commutes with taking the expected empirical measure. -/
theorem empiricalBarycenter_read {count : Nat} (positive : 0 < count)
    (sampler : Probability.Law (Population space count))
    (measurable : MeasurableMap space.toMeasurable firstOrder read) :
    (empiricalBarycenter count positive sampler).val.map read measurable =
      (sampler.val.val.map (populationRead read) (populationRead_measurable count measurable)).bind
        (Problib.Inference.empirical (lanes count positive) firstOrder) := by
  apply (Measure.eq_iff_lintegral _ _).mpr
  intro function functionMeasurable
  rw [lintegral_map _ _ _ functionMeasurable, Measure.bind_map,
    Measure.lintegral_bind _ _ functionMeasurable]
  refine (lintegral_empiricalBarycenter positive sampler
    (measurableTest (functionMeasurable.comp measurable))).trans ?_
  apply lintegral_congr
  intro population
  rw [Kernel.precomp_apply, Problib.Inference.lintegral_empirical _ _ functionMeasurable]
  rfl

/-- Reading commutes with reweighting a law of weighted pairs. -/
theorem weightedPairs_read (pairs : Probability.Law (Lane space))
    (measurable : MeasurableMap space.toMeasurable firstOrder read) :
    (bind (ofProbability pairs) (weightedLane space)).val.map read measurable =
      Problib.Inference.barycenter
        (pairs.val.val.map (laneRead read) (laneRead_measurable measurable)) := by
  apply (Measure.eq_iff_lintegral _ _).mpr
  intro function functionMeasurable
  rw [lintegral_map _ _ _ functionMeasurable,
    Problib.Inference.lintegral_barycenter _ functionMeasurable,
    lintegral_map _ _ _ (Problib.Inference.weighted_integrand_measurable functionMeasurable),
    bind_val, Measure.lintegral_bind _ _ (functionMeasurable.comp measurable), ofProbability_val]
  apply lintegral_congr
  intro lane
  exact lintegral_weightedLane (measurableTest (functionMeasurable.comp measurable)) lane

/-- A properly weighted sampler reads as a population invariant for the read
target, under any measurable reading. -/
theorem ProperlyWeightedLaw.empiricalInvariant {count : Nat} {positive : 0 < count}
    {target : Law space} {sampler : Probability.Law (Population space count)}
    (proper : ProperlyWeightedLaw count positive target sampler)
    (measurable : MeasurableMap space.toMeasurable firstOrder read) :
    Problib.Inference.EmpiricalInvariant (lanes count positive) (target.val.map read measurable)
      (sampler.val.val.map (populationRead read) (populationRead_measurable count measurable)) where
  probability := (ofProbability_probability sampler).map _ _
  mean := by
    rw [← empiricalBarycenter_read positive sampler measurable]
    exact congrArg (fun law : Law space => law.val.map read measurable) proper

/-! ### Standard Borel spaces -/

/-- On the space a standard Borel space generates, the identity reads the
induced measurable structure as the original one. -/
theorem standardRead (presentation : StandardBorel firstOrder) :
    MeasurableMap (Space.ofMeasurable borel firstOrder).toMeasurable firstOrder
      (fun value => value) := by
  intro set measurable
  rw [Space.toMeasurable_of_standardBorel_real presentation]
  exact measurable

/-- Laws on a standard Borel space are determined by their reading. -/
theorem law_eq_of_standardRead (presentation : StandardBorel firstOrder)
    {left right : Law (Space.ofMeasurable borel firstOrder)}
    (equal : left.val.map (fun value => value) (standardRead presentation) =
      right.val.map (fun value => value) (standardRead presentation)) :
    left = right := by
  apply Law.ext
  apply Measure.ext
  intro set measurable
  have original : firstOrder.Measurable set := by
    rw [← Space.toMeasurable_of_standardBorel_real presentation]
    exact measurable
  have atSet : (left.val.map (fun value => value) (standardRead presentation)) set =
      (right.val.map (fun value => value) (standardRead presentation)) set := by
    rw [equal]
  exact (Measure.map_apply left.val (fun value => value) (standardRead presentation)
    @original).symm.trans (atSet.trans (Measure.map_apply right.val (fun value => value)
      (standardRead presentation) @original))

/-- On a standard Borel space the counted contract is Inv_N. -/
theorem properlyWeightedLaw_iff_empiricalInvariant (presentation : StandardBorel firstOrder)
    {count : Nat} {positive : 0 < count} {target : Law (Space.ofMeasurable borel firstOrder)}
    {sampler : Probability.Law (Population (Space.ofMeasurable borel firstOrder) count)} :
    ProperlyWeightedLaw count positive target sampler ↔
      Problib.Inference.EmpiricalInvariant (lanes count positive)
        (target.val.map (fun value => value) (standardRead presentation))
        (sampler.val.val.map (populationRead fun value => value)
          (populationRead_measurable count (standardRead presentation))) := by
  constructor
  · intro proper
    exact proper.empiricalInvariant (standardRead presentation)
  · intro invariant
    apply law_eq_of_standardRead presentation
    rw [empiricalBarycenter_read positive sampler (standardRead presentation)]
    exact invariant.mean

/-- On a standard Borel space the counted contract at count one is first-order
proper weighting of the pair law. -/
theorem properlyWeightedLaw_one_iff_properlyWeighted (presentation : StandardBorel firstOrder)
    {target : Law (Space.ofMeasurable borel firstOrder)}
    {pairs : Probability.Law (Lane (Space.ofMeasurable borel firstOrder))} :
    ProperlyWeightedLaw 1 Nat.one_pos target
        (Probability.map (singletonPopulation (Space.ofMeasurable borel firstOrder)) pairs) ↔
      Problib.Inference.ProperlyWeighted
        (target.val.map (fun value => value) (standardRead presentation))
        (pairs.val.val.map (laneRead fun value => value)
          (laneRead_measurable (standardRead presentation))) := by
  rw [properlyWeightedLaw_one_iff]
  constructor
  · intro equal
    refine ⟨(ofProbability_probability pairs).map _ _, ?_⟩
    rw [← weightedPairs_read pairs (standardRead presentation), equal]
  · intro proper
    apply law_eq_of_standardRead presentation
    rw [weightedPairs_read pairs (standardRead presentation)]
    exact proper.change

end Problib.QuasiBorel.SFinite
