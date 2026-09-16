module

public import Foundations.Measure.Additive.FiniteReference
public import Foundations.Measure.Decomposition.RadonNikodym.SFinite
public import Foundations.Measure.Decomposition.ZeroInfinity.Properties
public import Foundations.Measure.Integral.Density.Finite

set_option autoImplicit false

namespace Foundations.Measure.Measure

open Foundations.Real

universe u

variable {alpha : Type u} {space : Space alpha}

-- For a density measure against a finite reference, points where the density
-- equals infinity form a greatest zero-infinity set.
private noncomputable def weightedTopZeroInfinity {reference : Measure space}
    (finite : Measure.IsFinite reference) {density : alpha → ENNReal}
    (measurable : ENNRealMeasurable space density) :
    Measure.TopZeroInfinitySet (reference.withDensity density) := by
  let infinity := fun value => density value = ENNReal.top
  have infinityMeasurable : space.Measurable infinity :=
    measurable.eq_set (ENNRealMeasurable.constant space ENNReal.top)
  refine { set := infinity, zeroInfinity := ⟨infinityMeasurable, ?_⟩, greatest := ?_ }
  · intro subset subsetMeasurable included
    rw [reference.withDensity_apply density subsetMeasurable]
    have equal := lintegral_congr_ae
      ((reference.ae_restrict_mem subsetMeasurable).mono (fun _ member => included member))
    change lintegral (reference.restrict subset) density =
      lintegral (reference.restrict subset) (fun _ => ENNReal.top) at equal
    rw [equal, lintegral_const, reference.restrict_apply_univ]
    classical
    by_cases zero : reference subset = ENNReal.zero
    · exact Or.inl (zero ▸ ENNReal.mulZero ENNReal.top)
    · exact Or.inr (ENNReal.topMulOfNeZero zero)
  · intro other otherZeroInfinity
    have null := (otherZeroInfinity.restrict (space.complement infinityMeasurable)).null_of_sigmaFinite
      (withDensity_sigmaFinite_restrict_ne_top finite measurable)
    change ((reference.withDensity density).restrict
      (fun value => density value ≠ ENNReal.top)) other = ENNReal.zero at null
    rw [(reference.withDensity density).restrict_apply _ otherZeroInfinity.measurable] at null
    exact null

-- Pair the greatest zero-infinity set with a sigma-finite cover of its
-- complement for density measures against finite references.
private noncomputable def weightedDecomposition {reference : Measure space}
    (finite : IsFinite reference) {density : alpha → ENNReal}
    (measurable : ENNRealMeasurable space density) :
    (top : TopZeroInfinitySet (reference.withDensity density)) ×
      SigmaFinite ((reference.withDensity density).restrict (Set.complement top.set)) :=
  ⟨weightedTopZeroInfinity finite measurable,
    withDensity_sigmaFinite_restrict_ne_top finite measurable⟩

-- Reconstruct the s-finite target from its finite reference and Radon-Nikodym
-- derivative to transport the zero-infinity decomposition.
private noncomputable def decomposition {target : Measure space} (finite : SFinite target) :
    (top : TopZeroInfinitySet target) × SigmaFinite (target.restrict (Set.complement top.set)) := by
  let reference := FiniteReference.ofSFinite finite
  let derivative := RadonNikodymDerivative.ofSFinite finite
    (SigmaFinite.ofFinite reference.finite) reference.targetContinuous
  have result := weightedDecomposition reference.finite derivative.densityMeasurable
  rw [← derivative.reconstruct_eq] at result
  exact result

/-- Construct a greatest zero-infinity set for any s-finite measure on an
arbitrary measurable space. -/
public noncomputable def TopZeroInfinitySet.ofSFinite {target : Measure space}
    (finite : SFinite target) : TopZeroInfinitySet target :=
  (decomposition finite).1

/-- The restriction of an s-finite measure to the complement of any greatest
zero-infinity set is sigma-finite. -/
public noncomputable def TopZeroInfinitySet.sigmaFinite_complement {target : Measure space}
    (top : TopZeroInfinitySet target) (finite : SFinite target) :
    SigmaFinite (target.restrict (Set.complement top.set)) := by
  let witness := decomposition finite
  have cover := witness.2
  rw [← top.restrict_complement_eq witness.1] at cover
  exact cover

/-- An s-finite measure is sigma-finite if and only if its greatest
zero-infinity set is null. -/
public theorem TopZeroInfinitySet.null_iff_sigmaFinite {target : Measure space}
    (top : TopZeroInfinitySet target) (finite : SFinite target) :
    target.NullSet top.set ↔ Nonempty (SigmaFinite target) := by
  constructor
  · intro null
    have complementNull : target.NullSet (Set.complement (Set.complement top.set)) := by
      rw [Set.complement_complement]
      exact null
    have cover := top.sigmaFinite_complement finite
    rw [target.restrict_eq_self_of_complement_null complementNull] at cover
    exact ⟨cover⟩
  · rintro ⟨cover⟩
    exact top.zeroInfinity.null_of_sigmaFinite cover

end Foundations.Measure.Measure
