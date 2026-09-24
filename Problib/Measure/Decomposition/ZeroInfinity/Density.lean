module

public import Problib.Measure.Decomposition.ZeroInfinity.AbsoluteContinuity
public import Problib.Measure.Integral.Density.Algebra
public import Problib.Measure.Integral.Density.AlmostEverywhere
public import Problib.Measure.Integral.Density.Zero
public import Problib.Measure.Integral.Simple.Induction

set_option autoImplicit false

/-!
# Zero-infinity density preservation

Weighting a measure by an arbitrary measurable extended-nonnegative density
preserves zero-infinity sets without finiteness assumptions.
Provenance follows Matthijs Vákár and Luke Ong,
[arXiv:1810.01837v2](https://arxiv.org/pdf/1810.01837v2), Lemma 4.
-/

namespace Problib.Measure.Measure

open Problib.Real

universe u

variable {alpha : Type u} {space : Space alpha}

/-- Weighting a measure by a measurable density preserves zero-infinity sets
without finiteness assumptions. -/
public theorem IsZeroInfinitySet.withDensity {measure : Measure space} {region : Set alpha}
    (zeroInfinity : Measure.IsZeroInfinitySet measure region)
    {density : alpha → ENNReal} (measurable : ENNRealMeasurable space density) :
    Measure.IsZeroInfinitySet (measure.withDensity density) region := by
  refine ⟨zeroInfinity.measurable, ?_⟩
  intro subset subsetMeasurable included
  apply ENNRealMeasurable.induction
    (motive := fun function =>
      (measure.withDensity function) subset = ENNReal.zero ∨
        (measure.withDensity function) subset = ENNReal.top)
    ?_ ?_ ?_ ?_ measurable
  · rw [measure.withDensity_zero, Measure.zero_apply]
    exact Or.inl rfl
  · intro selection selectionMeasurable value
    rw [measure.withDensity_indicator _ selectionMeasurable,
      (measure.restrict selection).withDensity_const,
      Measure.smul_apply_measurable _ _ subsetMeasurable,
      measure.restrict_apply selection subsetMeasurable]
    rcases zeroInfinity.subsets_zero_or_top
      (space.inter subsetMeasurable selectionMeasurable)
      (fun {_} member => included member.1) with zero | infinite
    · exact Or.inl (zero ▸ ENNReal.mul_zero value)
    · rw [infinite]
      classical
      by_cases valueZero : value = ENNReal.zero
      · exact Or.inl (valueZero ▸ ENNReal.zero_mul ENNReal.top)
      · exact Or.inr (ENNReal.mul_top_of_ne_zero valueZero)
  · intro left right leftMeasurable rightMeasurable leftCase rightCase
    rw [measure.withDensity_add leftMeasurable rightMeasurable,
      Measure.add_apply_measurable _ _ subsetMeasurable]
    rcases leftCase with zero | infinite
    · rw [zero, ENNReal.zero_add]
      exact rightCase
    · exact Or.inr (infinite ▸ ENNReal.top_add _)
  · intro functions functionsMeasurable functionsMonotone cases
    rw [measure.withDensity_iSup_apply functions functionsMeasurable
      (fun stage value => functionsMonotone value stage) subsetMeasurable]
    classical
    by_cases allZero : ∀ index, (measure.withDensity (functions index)) subset = ENNReal.zero
    · apply Or.inl
      apply ENNReal.le_antisymm
      · exact ENNReal.iSup_le (fun index => allZero index ▸ ENNReal.le_refl _)
      · exact ENNReal.zero_le _
    · apply Or.inr
      apply ENNReal.top_le_iff.mp
      apply Classical.byContradiction
      intro notTop
      apply allZero
      intro index
      rcases cases index with zero | infinite
      · exact zero
      · have bound := ENNReal.le_iSup (fun index =>
          (measure.withDensity (functions index)) subset) index
        rw [infinite] at bound
        exact False.elim (notTop bound)

/-- Any measurable density reconstructing a target measure from a reference
measure witnesses zero-infinity absolute continuity. -/
public theorem IsDensity.zeroInfinityAbsolutelyContinuous {target reference : Measure space}
    {density : alpha → ENNReal} (reconstruct : IsDensity target reference density)
    (measurable : ENNRealMeasurable space density) :
    ZeroInfinityAbsolutelyContinuous target reference where
  absolutelyContinuous := reconstruct.absolutelyContinuous
  preserves_zero_infinity := by
    intro region zeroInfinity
    rw [reconstruct.eq_withDensity]
    exact zeroInfinity.withDensity measurable

/-- Weighting the restriction to a zero-infinity set by a measurable density
equals restricting that measure to the density's nonzero support. -/
public theorem IsZeroInfinitySet.withDensity_restrict_eq_restrict_support {measure : Measure space} {region : Set alpha}
    (zeroInfinity : Measure.IsZeroInfinitySet measure region)
    {density : alpha → ENNReal} (measurable : ENNRealMeasurable space density) :
    (measure.restrict region).withDensity density =
      (measure.restrict region).restrict (fun value => density value ≠ ENNReal.zero) := by
  apply Measure.ext
  intro set setMeasurable
  let support := fun value => density value ≠ ENNReal.zero
  have supportMeasurable : space.Measurable support :=
    space.complement (measurable.eq_set (ENNRealMeasurable.constant space ENNReal.zero))
  rw [(measure.restrict region).restrict_apply support setMeasurable]
  have zeroIff := Measure.withDensity_apply_eq_zero_iff measurable setMeasurable
    (reference := measure.restrict region)
  have targetCase : ((measure.restrict region).withDensity density) set = ENNReal.zero ∨
      ((measure.restrict region).withDensity density) set = ENNReal.top := by
    rw [measure.withDensity_restrict density zeroInfinity.measurable,
      (measure.withDensity density).restrict_apply region setMeasurable]
    exact (zeroInfinity.withDensity measurable).subsets_zero_or_top
      (space.inter setMeasurable zeroInfinity.measurable)
      (fun {_} member => member.2)
  rcases targetCase with targetZero | targetTop
  · exact targetZero.trans (zeroIff.mp targetZero).symm
  · have referenceCase : (measure.restrict region) (Set.inter set support) = ENNReal.zero ∨
        (measure.restrict region) (Set.inter set support) = ENNReal.top := by
      rw [measure.restrict_apply region (space.inter setMeasurable supportMeasurable)]
      exact zeroInfinity.subsets_zero_or_top
        (space.inter (space.inter setMeasurable supportMeasurable) zeroInfinity.measurable)
        (fun {_} member => member.2)
    rcases referenceCase with referenceZero | referenceTop
    · exact False.elim (ENNReal.top_ne_finite NNReal.zero
        (targetTop.symm.trans (zeroIff.mpr referenceZero)))
    · exact targetTop.trans referenceTop.symm

end Problib.Measure.Measure
