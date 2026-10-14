import Problib.QuasiBorel.SFinite.Weighting
import Problib.Measure.Integral.Lebesgue.Transport
import Problib.QuasiBorel.Probability.Strength

/-!
# Mapping and binding counted proper weighting

A quasi-Borel morphism `f : Y → Z` maps a population lane by lane, keeping each
lane's weight (`populationMap`). The empirical measure of the mapped population
is the image of the original one (`empirical_populationMap`), so a sampler
properly weighted for `μ` maps to a sampler properly weighted for the image of
`μ`, at every count (`ProperlyWeightedLaw.map`). Nothing about the lanes'
joint law is assumed.

At first order, on measurable spaces, the same statement is
`Problib.Inference.weighted_map`, which holds for every measurable map between
arbitrary measurable spaces and so is not derived from this one.

A step `steps : Y → P(Z × [0, ∞))` extends a weighted pair `(y, v)` by drawing
`(z, w) ~ steps y` and keeping `(z, v w)` (`bindStep`). If the pairs are
properly weighted for `μ` at count one, the extended pairs are properly weighted
for `μ` bound to the steps' barycenters `y ↦ ∫ w δ_z d(steps y)`
(`ProperlyWeightedLaw.bind`). The step sees the context `y` through the
strength of the probability monad, so it may depend on it arbitrarily.
`Problib.Inference.weighted_bind` is the first-order statement on arbitrary
measurable spaces and is likewise kept.
-/

set_option autoImplicit false

namespace Problib.QuasiBorel.SFinite

open Problib.Measure hiding Space
open Problib.Real (ENNReal NNReal)

universe u

variable {source target : Space.{0, u} realSource}

/-- A lane mapped by `f`, keeping its weight. -/
noncomputable def laneMap (function : Hom source target) : Hom (Lane source) (Lane target) :=
  Space.productMap function (Hom.identity finiteWeightSpace)

/-- A population mapped lane by lane. -/
noncomputable def populationMap (function : Hom source target) (count : Nat) :
    Hom (Population source count) (Population target count) :=
  Space.tuple fun lane => Hom.comp (laneMap function) (laneAt source lane)

/-- A lane's weighted Dirac law integrates a measurable function to the
weighted value. -/
private theorem lintegral_weightedLane_function {space : Space.{0, u} realSource}
    {function : space.Carrier → ENNReal} (measurable : ENNRealMeasurable space.toMeasurable function)
    (lane : (Lane space).Carrier) :
    lintegral (weightedLane space lane).val function =
      ENNReal.mul (ENNReal.finite lane.2) (function lane.1) :=
  lintegral_weightedLane (measurableTest measurable) lane

/-- The empirical measure of a mapped population is the image of the
population's empirical measure. -/
theorem empirical_populationMap (function : Hom source target) {count : Nat} (positive : 0 < count)
    (population : (Population source count).Carrier) :
    empirical target count positive (populationMap function count population) =
      map function (empirical source count positive population) := by
  apply Law.ext
  apply (Measure.eq_iff_lintegral _ _).mpr
  intro test measurable
  rw [map_val, lintegral_map _ _ _ measurable, empirical, empirical, lintegral_laneAverage,
    lintegral_laneAverage]
  apply congrArg (ENNReal.mul _)
  apply congrArg
  apply List.map_congr_left
  intro lane _
  simp only [Hom.comp_apply]
  rw [lintegral_weightedLane_function measurable,
    lintegral_weightedLane_function (measurable.comp function.toMeasurable)]
  rfl

/-- Mapping a properly weighted sampler lane by lane is properly weighted for
the image target, at every count. -/
theorem ProperlyWeightedLaw.map {count : Nat} {positive : 0 < count} {law : Law source}
    {sampler : Probability.Law (Population source count)}
    (proper : ProperlyWeightedLaw count positive law sampler) (function : Hom source target) :
    ProperlyWeightedLaw count positive (map function law)
      (Probability.map (populationMap function count) sampler) := by
  rw [ProperlyWeightedLaw, empiricalBarycenter, ofProbability_map, bind_map, ← proper,
    empiricalBarycenter, map_bind]
  apply congrArg (bind (ofProbability sampler))
  apply Hom.ext
  intro population
  exact empirical_populationMap function positive population

/-! ### Binding at count one -/

/-- The product of two finite weights. -/
noncomputable def weightProduct :
    Hom (Space.product finiteWeightSpace finiteWeightSpace) finiteWeightSpace where
  toFun := fun weights => NNReal.mul weights.1 weights.2
  map_random := fun accepted => Problib.Inference.weight_mul_measurable accepted.1 accepted.2

/-- A lane reweighted by an outer weight: `(v, (z, w)) ↦ (z, v w)`. -/
noncomputable def reweightLane (space : Space.{0, u} realSource) :
    Hom (Space.product finiteWeightSpace (Lane space)) (Lane space) :=
  Space.pair
    (Hom.comp (Space.first space finiteWeightSpace) (Space.second finiteWeightSpace (Lane space)))
    (Hom.comp weightProduct
      (Space.pair (Space.first finiteWeightSpace (Lane space))
        (Hom.comp (Space.second space finiteWeightSpace)
          (Space.second finiteWeightSpace (Lane space)))))

/-- Extend a weighted pair `(y, v)` by a step drawn at `y`, multiplying the
weights. -/
noncomputable def bindStep (steps : Hom source (Probability.object (Lane target))) :
    Hom (Lane source) (Probability.object (Lane target)) :=
  Hom.comp (Probability.map (reweightLane target))
    (Hom.comp (Probability.strength finiteWeightSpace (Lane target))
      (Space.pair (Space.second source finiteWeightSpace)
        (Hom.comp steps (Space.first source finiteWeightSpace))))

/-- The law a step is properly weighted for at each context: the barycenter of
its weighted Dirac laws. -/
noncomputable def stepBarycenter (steps : Hom source (Probability.object (Lane target))) :
    Hom source (object target) :=
  Hom.comp (extend (weightedLane target)) (Hom.comp (ofProbabilityHom (Lane target)) steps)

/-- Binding against a kernel scaled by a constant scales the bind. -/
private theorem bind_scale_constant {domain : Space.{0, u} realSource}
    (weight : ENNReal) (law : Law domain) (kernel : Hom domain (object target)) :
    bind law (Hom.comp (scale target) (Space.pair (Hom.constant domain weightSpace weight) kernel)) =
      scale target (weight, bind law kernel) := by
  apply Law.ext
  rw [scale_val, bind_val, bind_val]
  apply Measure.ext
  intro set measurable
  rw [Measure.smul_apply_measurable _ _ @measurable, Measure.bind_apply _ _ @measurable,
    Measure.bind_apply _ _ @measurable,
    ← lintegral_smul _ _ ((toKernel kernel).measurable @measurable)]
  apply congrArg (lintegral law.val)
  funext point
  change (scale target (weight, kernel point)).val set = _
  rw [scale_val, Measure.smul_apply_measurable _ _ @measurable]
  rfl

/-- Extending properly weighted pairs by steps is properly weighted for the
target bound to the steps' barycenters. -/
theorem ProperlyWeightedLaw.bind {law : Law source} {pairs : Probability.Law (Lane source)}
    (proper : ProperlyWeightedLaw 1 Nat.one_pos law (Probability.map (singletonPopulation source) pairs))
    (steps : Hom source (Probability.object (Lane target))) :
    ProperlyWeightedLaw 1 Nat.one_pos (bind law (stepBarycenter steps))
      (Probability.map (singletonPopulation target) (Probability.bind pairs (bindStep steps))) := by
  rw [properlyWeightedLaw_one_iff] at proper ⊢
  rw [ofProbability_bind, bind_assoc, ← proper, bind_assoc]
  apply congrArg (SFinite.bind (ofProbability pairs))
  apply Hom.ext
  intro lane
  change SFinite.bind (ofProbability (bindStep steps lane)) (weightedLane target) =
    SFinite.bind (weightedLane source lane) (stepBarycenter steps)
  have scaled : weightedLane source lane =
      scale source (ENNReal.finite lane.2, pure source lane.1) := rfl
  rw [scaled, ← scale_bind, pure_bind]
  change _ = scale target (ENNReal.finite lane.2,
    SFinite.bind (ofProbability (steps lane.1)) (weightedLane target))
  rw [← bind_scale_constant]
  change SFinite.bind (ofProbability (Probability.map (reweightLane target)
    (Probability.map (Space.pairLeft finiteWeightSpace (Lane target) lane.2) (steps lane.1)))) _ = _
  rw [ofProbability_map, ofProbability_map, bind_map, bind_map]
  apply congrArg (SFinite.bind (ofProbability (steps lane.1)))
  apply Hom.ext
  intro point
  apply Law.ext
  change (weightedPoint target (ENNReal.finite (NNReal.mul lane.2 point.2), point.1)).val =
    (scale target (ENNReal.finite lane.2,
      weightedPoint target (ENNReal.finite point.2, point.1))).val
  rw [scale_val, weightedPoint_val, weightedPoint_val, Measure.smul_smul,
    ENNReal.finite_mul_finite]

end Problib.QuasiBorel.SFinite
