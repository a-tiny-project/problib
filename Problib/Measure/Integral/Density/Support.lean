module

public import Problib.Measure.Integral.Density.Zero
public import Problib.Measure.Additive.Map
public import Problib.Measure.Product

set_option autoImplicit false

/-! Absolute continuity from where a density is positive.

A ratio `p/q` of two densities against one base is a density of the target
against the proposal exactly when the target is absolutely continuous with
respect to the proposal. Asking `q` to be nonzero at every point is enough, but
a proposal positive only where the target lives already suffices. The bridges
here read absolute continuity off positivity on such a region, by null-set
arguments alone: no positive lower bound on `q`, no finite mass and no moment.

* `absolutelyContinuous_of_restrict` is the region form: a target dominated by
  the base and living on a region, against a proposal that charges every
  base-positive part of that region.
* `restrict_absolutelyContinuous_withDensity` says when a weighted measure
  charges a region: its density is nonzero almost everywhere there.
* `absolutelyContinuous_of_density_positive_ae` is the density form: the
  proposal's density is nonzero wherever the target puts mass.
* `absolutelyContinuous_of_density_support` is the form for two densities
  against one base: where the target's density is nonzero, so is the
  proposal's, base-almost everywhere.
* `ae_marginal_density_ne_zero` says a joint measure puts no mass where the
  density of its first marginal vanishes.
-/

namespace Problib.Measure.Measure

open Problib.Real

universe u v

variable {alpha : Type u} {space : Space alpha}

/-- A target dominated by the base and living on a region is dominated by any
proposal that charges every base-positive part of the region. The region needs
no measurability: both premises are statements about null sets. -/
public theorem absolutelyContinuous_of_restrict {target reference proposal : Measure space}
    {region : Set alpha} (targetReference : AbsolutelyContinuous target reference)
    (covers : target.AE region)
    (charges : AbsolutelyContinuous (reference.restrict region) proposal) :
    AbsolutelyContinuous target proposal := by
  intro set setMeasurable proposalNull
  have restricted := charges setMeasurable proposalNull
  rw [reference.restrict_apply region setMeasurable] at restricted
  have inside : target.NullSet (Set.inter set region) := targetReference.null restricted
  have covered : target.NullSet (Set.union (Set.inter set region) (Set.complement region)) :=
    NullSet.union inside covers
  apply covered.mono
  intro value member
  classical
  by_cases inRegion : region value
  · exact Or.inl ⟨member, inRegion⟩
  · exact Or.inr inRegion

/-- A weighted measure charges every base-positive part of a region on which its
measurable density is nonzero base-almost everywhere. -/
public theorem restrict_absolutelyContinuous_withDensity {reference : Measure space}
    {density : alpha → ENNReal} (measurable : ENNRealMeasurable space density)
    {region : Set alpha}
    (positive : reference.AE (fun value => region value → density value ≠ ENNReal.zero)) :
    AbsolutelyContinuous (reference.restrict region) (reference.withDensity density) := by
  intro set setMeasurable weightedNull
  rw [reference.restrict_apply region setMeasurable]
  have supportNull := (withDensity_apply_eq_zero_iff measurable setMeasurable).mp weightedNull
  have covered : reference.NullSet (Set.union
      (Set.inter set (fun value => density value ≠ ENNReal.zero))
      (Set.complement (fun value => region value → density value ≠ ENNReal.zero))) :=
    NullSet.union supportNull positive
  apply covered.mono
  intro value member
  classical
  by_cases zero : density value = ENNReal.zero
  · exact Or.inr fun implied => implied member.2 zero
  · exact Or.inl ⟨member.1, zero⟩

/-- A target dominated by the base is dominated by a proposal with a measurable
density against the base, when that density is nonzero target-almost
everywhere. Domination of the target by the base is indispensable: a point
mass is not dominated by a Gaussian, though the Gaussian's density is positive
at the point. -/
public theorem absolutelyContinuous_of_density_positive_ae
    {target reference proposal : Measure space} {density : alpha → ENNReal}
    (targetReference : AbsolutelyContinuous target reference)
    (measurable : ENNRealMeasurable space density)
    (proposalDensity : IsDensity proposal reference density)
    (positive : target.AE (fun value => density value ≠ ENNReal.zero)) :
    AbsolutelyContinuous target proposal := by
  rw [proposalDensity.eq_withDensity]
  exact absolutelyContinuous_of_restrict targetReference positive
    (restrict_absolutelyContinuous_withDensity measurable
      (ae_of_forall fun _ nonzero => nonzero))

/-- Two measures with measurable densities against one base: the first is
dominated by the second when, base-almost everywhere, the second density is
nonzero wherever the first is. -/
public theorem absolutelyContinuous_of_density_support
    {target proposal reference : Measure space} {targetDensity proposalDensity : alpha → ENNReal}
    (targetMeasurable : ENNRealMeasurable space targetDensity)
    (proposalMeasurable : ENNRealMeasurable space proposalDensity)
    (targetIsDensity : IsDensity target reference targetDensity)
    (proposalIsDensity : IsDensity proposal reference proposalDensity)
    (covers : reference.AE (fun value =>
      targetDensity value ≠ ENNReal.zero → proposalDensity value ≠ ENNReal.zero)) :
    AbsolutelyContinuous target proposal := by
  have vanishing : space.Measurable (fun value => proposalDensity value = ENNReal.zero) :=
    proposalMeasurable.eq_set (ENNRealMeasurable.constant space ENNReal.zero)
  have targetNull : target (fun value => proposalDensity value = ENNReal.zero) = ENNReal.zero := by
    rw [targetIsDensity.eq_withDensity]
    apply (withDensity_apply_eq_zero_iff targetMeasurable vanishing).mpr
    exact NullSet.mono covers fun value member implied => implied member.2 member.1
  apply absolutelyContinuous_of_density_positive_ae targetIsDensity.absolutelyContinuous
    proposalMeasurable proposalIsDensity
  apply NullSet.mono targetNull
  intro value failure
  classical
  exact Classical.byContradiction fun nonzero => failure nonzero

variable {delta : Type v} {extra : Space delta}

/-- A joint measure whose first marginal has a measurable density against a
reference puts no mass where that density vanishes: the marginal gives the set
`{q = 0}` the integral of `q` over it, which is zero. -/
public theorem ae_marginal_density_ne_zero {joint : Measure (Space.product space extra)}
    {reference : Measure space} {density : alpha → ENNReal}
    (measurable : ENNRealMeasurable space density)
    (marginal : joint.map Prod.fst (Space.first_measurable space extra) =
      reference.withDensity density) :
    joint.AE (fun pair => density pair.1 ≠ ENNReal.zero) := by
  have vanishing : space.Measurable (fun value => density value = ENNReal.zero) :=
    measurable.eq_set (ENNRealMeasurable.constant space ENNReal.zero)
  have marginalNull : (joint.map Prod.fst (Space.first_measurable space extra))
      (fun value => density value = ENNReal.zero) = ENNReal.zero := by
    rw [marginal]
    apply (withDensity_apply_eq_zero_iff measurable vanishing).mpr
    apply reference.null_empty.mono
    intro value member
    exact member.2 member.1
  rw [map_apply _ _ _ vanishing] at marginalNull
  apply NullSet.mono marginalNull
  intro pair failure
  exact Classical.byContradiction fun nonzero => failure nonzero

end Problib.Measure.Measure
