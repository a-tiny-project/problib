module

public import Problib.Inference.PseudoMarginal
public import Problib.Inference.Population
public import Problib.Inference.Resampling
set_option autoImplicit false

/-! Particle marginal Metropolis–Hastings.

PMMH is a pseudo-marginal chain whose estimator is a sequential Monte Carlo
run. It needs no law of its own for invariance: `pseudoMarginalKernel_invariant`
applies to any estimator. It needs two facts about the estimator, and both are
facts about proper weighting, not about how the run was built.

Read at its mean weight, a population whose expected empirical measure is
`γ_θ` is unbiased for `γ_θ`'s mass (`population_unbiased`), so the chain's
parameter marginal is the reference weighted by that mass
(`pseudo_marginal_marginal`). Read at its weight, a weighted draw properly
weighted for `γ_θ` is unbiased in the same way (`properlyWeighted_unbiased`),
and the extended target read at the parameter and the drawn value is the
reference joined with `γ` (`pseudo_marginal_joint`). A lane picked from such a
population is one such draw. -/

namespace Problib.Inference

open Problib.Real Problib.Measure

universe u v

variable {α : Type u} {β : Type v} {space : Space α} {result : Space β}

public section

/-- The weight carried by a weighted draw at a parameter. -/
theorem joinedWeight_measurable (space : Space α) (result : Space β) :
    MeasurableMap (Space.product space (Space.product result weightSpace)) weightSpace
      (fun point : α × (β × NNReal) => point.2.2) :=
  MeasurableMap.comp (Space.second_measurable result weightSpace)
    (Space.second_measurable space (Space.product result weightSpace))

/-- The parameter and the drawn value of a weighted draw at a parameter. -/
theorem joinedValue_measurable (space : Space α) (result : Space β) :
    MeasurableMap (Space.product space (Space.product result weightSpace))
      (Space.product space result) (fun point : α × (β × NNReal) => (point.1, point.2.1)) :=
  Space.pair_measurable (Space.first_measurable space (Space.product result weightSpace))
    (MeasurableMap.comp (Space.first_measurable result weightSpace)
      (Space.second_measurable space (Space.product result weightSpace)))

/-- A weighted sampler properly weighted for `γ_θ` at every parameter, read at
its weight, is unbiased for `γ_θ`'s mass. -/
theorem properlyWeighted_unbiased {inner : Kernel space result}
    {estimator : Kernel space (Space.product result weightSpace)}
    (estimatorFinite : Kernel.IsSFinite estimator)
    (properlyWeighted : ∀ parameter, ProperlyWeighted (inner parameter) (estimator parameter)) :
    UnbiasedEstimate (fun parameter => inner parameter Set.univ)
      (readEstimate estimator estimatorFinite (fun point => point.2.2)
        (joinedWeight_measurable space result)) where
  probability parameter := by
    rw [readEstimate_apply]
    exact (properlyWeighted parameter).probability.map _ _
  mean_eq parameter := by
    rw [readEstimate_apply,
      lintegral_map _ _ _ (finite_weight_measurable (MeasurableMap.identity weightSpace))]
    exact properlyWeighted_mass (properlyWeighted parameter)

/-- A population invariant for `γ_θ` at every parameter, read at its mean
weight, is unbiased for `γ_θ`'s mass. -/
theorem population_unbiased {ι : Type} (lanes : Lanes ι) {inner : Kernel space result}
    {population : Kernel space (populationSpace ι result)}
    (populationFinite : Kernel.IsSFinite population)
    (invariant : ∀ parameter, EmpiricalInvariant lanes (inner parameter) (population parameter)) :
    UnbiasedEstimate (fun parameter => inner parameter Set.univ)
      (readEstimate population populationFinite (fun point => meanWeight lanes point.2)
        (MeasurableMap.comp (meanWeight_measurable lanes result)
          (Space.second_measurable space (populationSpace ι result)))) where
  probability parameter := by
    rw [readEstimate_apply]
    exact (invariant parameter).probability.map _ _
  mean_eq parameter := by
    rw [readEstimate_apply,
      lintegral_map _ _ _ (finite_weight_measurable (MeasurableMap.identity weightSpace))]
    exact empirical_mass_unbiased (invariant parameter)

/-- PMMH's joint marginal. When the estimator draws weighted values properly
weighted for `γ_θ`, the extended target read at the parameter and the drawn
value is the reference joined with `γ`. -/
theorem pseudo_marginal_joint {reference : Measure space} {inner : Kernel space result}
    (innerFinite : Kernel.IsSFinite inner)
    {estimator : Kernel space (Space.product result weightSpace)}
    (estimatorFinite : Kernel.IsSFinite estimator)
    (properlyWeighted : ∀ parameter, ProperlyWeighted (inner parameter) (estimator parameter)) :
    (extendedTarget reference estimator estimatorFinite (fun point => point.2.2)).map
        (fun point => (point.1, point.2.1)) (joinedValue_measurable space result) =
      reference.semiproduct inner innerFinite := by
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  have weightFinite := finite_weight_measurable (joinedWeight_measurable space result)
  have pairMeasurable := measurable.comp (joinedValue_measurable space result)
  rw [lintegral_map _ _ _ measurable, extendedTarget,
    lintegral_withDensity _ weightFinite pairMeasurable,
    lintegral_semiproduct _ _ _ (ENNRealMeasurable.mul weightFinite pairMeasurable),
    lintegral_semiproduct _ _ _ measurable]
  apply lintegral_congr
  intro parameter
  exact (properlyWeighted parameter).lintegral
    (measurable.comp (Kernel.pair_left_measurable (source := space) (target := result) parameter))

end

end Problib.Inference
