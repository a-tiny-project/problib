module

public import Foundations.Measure.Decomposition.RadonNikodym.SFinite
public import Foundations.Measure.Decomposition.ZeroInfinity
public import Foundations.Measure.Integral.Density.Zero

set_option autoImplicit false

/-!
# S-finite reference Radon-Nikodym derivatives

Constructs measurable Radon-Nikodym derivatives for s-finite target and
reference measures under zero-infinity absolute continuity.
The proof organization follows Matthijs Vákár and Luke Ong,
[arXiv:1810.01837v2](https://arxiv.org/pdf/1810.01837v2), Theorem 10.

The construction partitions the reference measure into a greatest zero-infinity
set and a sigma-finite complement.
An indicator density handles the zero-infinity set through an equivalent finite
reference measure.
Existing derivation handles the sigma-finite complement.
Piecewise gluing reconstructs the target measure.
-/

namespace Foundations.Measure.Measure.RadonNikodymDerivative

open Foundations.Real

universe u

variable {alpha : Type u} {space : Space alpha}

/-- Every Radon-Nikodym derivative certificate implies zero-infinity absolute
continuity without finiteness assumptions. -/
public theorem zeroInfinityAbsolutelyContinuous {target reference : Measure space}
    (derivative : RadonNikodymDerivative target reference) :
    ZeroInfinityAbsolutelyContinuous target reference :=
  derivative.reconstruct.zeroInfinityAbsolutelyContinuous derivative.densityMeasurable

/-- Constructs a Radon-Nikodym derivative for s-finite target and reference
measures under zero-infinity absolute continuity. -/
public noncomputable def ofSFiniteReference {target reference : Measure space}
    (targetFinite : SFinite target) (referenceFinite : SFinite reference)
    (continuous : ZeroInfinityAbsolutelyContinuous target reference) :
    RadonNikodymDerivative target reference := by
  let top := TopZeroInfinitySet.ofSFinite referenceFinite
  let region := top.set
  have regionMeasurable : space.Measurable region := top.zeroInfinity.measurable
  have targetRegion : IsZeroInfinitySet target region := continuous.preservesZeroInfinity top.zeroInfinity
  let finiteReference := FiniteReference.ofSFinite referenceFinite
  let supportDerivative := RadonNikodymDerivative.ofSFinite targetFinite
    (SigmaFinite.ofFinite finiteReference.finite)
    (AbsolutelyContinuous.trans continuous.absolutelyContinuous finiteReference.targetContinuous)
  let support := fun value => supportDerivative.density value ≠ ENNReal.zero
  have supportMeasurable : space.Measurable support :=
    space.complement (supportDerivative.densityMeasurable.eq_set
      (ENNRealMeasurable.constant space ENNReal.zero))
  let inside := ennrealIndicator support (fun _ => ENNReal.one)
  have insideMeasurable : ENNRealMeasurable space inside :=
    ENNRealMeasurable.indicator supportMeasurable (ENNRealMeasurable.constant space ENNReal.one)
  let outside := RadonNikodymDerivative.ofSFinite
    (targetFinite.restrict (space.complement regionMeasurable))
    (top.sigmaFinite_complement referenceFinite)
    (AbsolutelyContinuous.restrict continuous.absolutelyContinuous (Set.complement region))
  have insideReconstruct : target.restrict region = (reference.restrict region).withDensity inside := by
    rw [reference.withDensity_restrict inside regionMeasurable,
      reference.withDensity_indicator _ supportMeasurable,
      (reference.restrict support).withDensity_one]
    apply Measure.ext
    intro set setMeasurable
    rw [target.restrict_apply region setMeasurable,
      (reference.restrict support).restrict_apply region setMeasurable,
      reference.restrict_apply support (space.inter setMeasurable regionMeasurable)]
    have zeroIff : target (Set.inter set region) = ENNReal.zero ↔
        reference (Set.inter (Set.inter set region) support) = ENNReal.zero := by
      rw [supportDerivative.reconstruct_eq]
      exact (withDensity_apply_eq_zero_iff supportDerivative.densityMeasurable
        (space.inter setMeasurable regionMeasurable)).trans
        ((finiteReference.null_iff _).symm)
    rcases targetRegion.subsets_zero_or_top (space.inter setMeasurable regionMeasurable)
      (fun {_} member => member.2) with targetZero | targetTop
    · exact targetZero.trans (zeroIff.mp targetZero).symm
    · rcases top.zeroInfinity.subsets_zero_or_top
        (space.inter (space.inter setMeasurable regionMeasurable) supportMeasurable)
        (fun {_} member => member.1.2) with referenceZero | referenceTop
      · exact False.elim (ENNReal.topNeFinite NNReal.zero
          (targetTop.symm.trans (zeroIff.mpr referenceZero)))
      · exact targetTop.trans referenceTop.symm
  refine {
    density := ennrealPiecewise region inside outside.density
    densityMeasurable := ENNRealMeasurable.piecewise regionMeasurable insideMeasurable
      outside.densityMeasurable
    reconstruct := ?_
  }
  change target = reference.withDensity (ennrealPiecewise region inside outside.density)
  rw [reference.withDensity_piecewise regionMeasurable insideMeasurable outside.densityMeasurable,
    ← insideReconstruct, ← outside.reconstruct_eq]
  apply Measure.ext
  intro set setMeasurable
  rw [Measure.add_apply_measurable _ _ setMeasurable,
    target.restrict_apply region setMeasurable,
    target.restrict_apply (Set.complement region) setMeasurable]
  exact (target.inter_add_difference set regionMeasurable).symm


/-- For s-finite target and reference measures, existence of a Radon-Nikodym
derivative is equivalent to zero-infinity absolute continuity. -/
public theorem nonempty_iff {target reference : Measure space}
    (targetFinite : SFinite target) (referenceFinite : SFinite reference) :
    Nonempty (RadonNikodymDerivative target reference) ↔
      ZeroInfinityAbsolutelyContinuous target reference :=
  ⟨fun ⟨derivative⟩ => derivative.zeroInfinityAbsolutelyContinuous,
    fun continuous => ⟨ofSFiniteReference targetFinite referenceFinite continuous⟩⟩

end Foundations.Measure.Measure.RadonNikodymDerivative
