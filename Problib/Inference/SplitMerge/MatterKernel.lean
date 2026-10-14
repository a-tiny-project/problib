module

public import Problib.Inference.SplitMerge.Matter
public import Problib.Inference.SplitMerge.Kernel
public import Problib.Measure.Kernel.Scale

set_option autoImplicit false

/-!
# The matter kernel

The four matter families run as split/merge kernels on a state with a fixed
number of clusters, at least two so that reassignment has a pair: patch births
and deaths in any cluster, background births and deaths, reassignment between
two clusters, and the centroid split and merge in any cluster. Each family's
selection draws its index, schedule and draw with a density against its side
references (`SplitMergeSelection`). A fixed mixture of the four
(`matterKernel`) leaves invariant every target with a density against the
matter reference (`matterKernel_invariant`). The density covers the whole
state, so a split's effect on every strength, a reassignment's count change and
the parent density all enter the acceptance through `splitMergeKernel_accept`.
-/

namespace Problib.Inference

open Problib.Real Problib.Measure
open Problib.Real.Construction
open Problib.Measure.Real (Carrier borel)

universe u

public section

variable {P σ : Type u} {parents : Space P} {shapes : Space σ}
  (dimension : Nat) (shapeReference : Measure shapes) (shapeFinite : Measure.SFinite shapeReference)

/-- A birth or death side: the cluster index, the schedule, and `count` new
patches. -/
@[expose] noncomputable def birthSideReference (count : Nat) :
    Measure (Space.product (Space.discrete Nat)
      (Space.product schedulePair (Space.list (patchSpace dimension shapes)))) :=
  Measure.prod Measure.counting
    (Measure.prod positionCounting
      (Measure.listPower (patchReference dimension shapeReference shapeFinite)
        (patchReferenceSFinite dimension shapeReference shapeFinite) count)
      (Measure.SFinite.listPower (patchReferenceSFinite dimension shapeReference shapeFinite)
        count))
    (positionCountingFinite.prod
      (Measure.SFinite.listPower (patchReferenceSFinite dimension shapeReference shapeFinite)
        count))

/-- A background birth or death side: the schedule and `count` new patches. -/
@[expose] noncomputable def backgroundSideReference (count : Nat) :
    Measure (Space.product schedulePair (Space.list (patchSpace dimension shapes))) :=
  Measure.prod positionCounting
    (Measure.listPower (patchReference dimension shapeReference shapeFinite)
      (patchReferenceSFinite dimension shapeReference shapeFinite) count)
    (Measure.SFinite.listPower (patchReferenceSFinite dimension shapeReference shapeFinite)
      count)

/-- A reassignment side: the ordered pair's code and the two positions. -/
@[expose] noncomputable def reassignSideReference :
    Measure (Space.product (Space.discrete Nat) positionPair) :=
  Measure.prod Measure.counting positionPairCounting positionPairCountingFinite

/-- A split side: the cluster index, the schedule and the split's draw. -/
@[expose] noncomputable def splitSideReference :
    Measure (Space.product (Space.discrete Nat)
      (Space.product schedulePair (splitDraw dimension shapes))) :=
  Measure.prod Measure.counting
    (Measure.prod positionCounting (splitDrawReference dimension shapeReference shapeFinite)
      (splitDrawReferenceFinite dimension shapeReference shapeFinite))
    (positionCountingFinite.prod (splitDrawReferenceFinite dimension shapeReference shapeFinite))

/-- A merge side: the cluster index, the schedule and the kept parent shape. -/
@[expose] noncomputable def mergeSideReference :
    Measure (Space.product (Space.discrete Nat) (Space.product schedulePair shapes)) :=
  Measure.prod Measure.counting (Measure.prod positionCounting shapeReference shapeFinite)
    (positionCountingFinite.prod shapeFinite)

/-- The centroid factor is measurable jointly in the state, the cluster index
and the merge auxiliary. -/
theorem patchSplitMergeFactor_measurable
    (fallback : P × List (Carrier × ((Fin dimension → Carrier) × σ)))
    (fallbackPatch : Carrier × ((Fin dimension → Carrier) × σ)) :
    MeasurableMap (Space.product (matterSpace parents (patchSpace dimension shapes))
        (Space.product (Space.discrete Nat) (Space.product schedulePair shapes))) borel
      (patchSplitMergeFactor (parents := parents) (shapes := shapes) dimension fallback
        fallbackPatch) := by
  have indexed : MeasurableMap
      (Space.product (Space.discrete Nat) (Space.product
        (matterSpace parents (patchSpace dimension shapes)) (Space.product schedulePair shapes)))
      borel
      (fun pair => patchSplitFactor dimension fallbackPatch
        (((clusterLens (parents := parents) (patches := patchSpace dimension shapes)
          fallback pair.1).forward pair.2.1).1, pair.2.2)) :=
    MeasurableMap.uncurry_of_countable_first (fun index : Nat => index)
    nat_code_injective
    (source := Space.product (matterSpace parents (patchSpace dimension shapes))
      (Space.product schedulePair shapes)) (target := borel)
    (function := fun index point => patchSplitFactor dimension fallbackPatch
      (((clusterLens (parents := parents) (patches := patchSpace dimension shapes)
        fallback index).forward point.1).1, point.2))
    (fun index => by
      intro set setMeasurable
      exact (MeasurableMap.comp (patchSplitFactor_measurable dimension fallbackPatch)
        (Space.pair_measurable
          (MeasurableMap.comp (Space.first_measurable _ _)
            (MeasurableMap.comp (clusterLens fallback index).forwardMeasurable
              (Space.first_measurable _ _)))
          (Space.second_measurable _ _))) setMeasurable)
  intro set setMeasurable
  exact (MeasurableMap.comp indexed
    (Space.pair_measurable
      (MeasurableMap.comp (Space.first_measurable _ _) (Space.second_measurable _ _))
      (Space.pair_measurable (Space.first_measurable _ _)
        (MeasurableMap.comp (Space.second_measurable _ _) (Space.second_measurable _ _)))))
    setMeasurable

/-- The centroid factor is positive on the split/merge pairing's range. -/
theorem patchSplitMergeFactor_positive
    (fallback : P × List (Carrier × ((Fin dimension → Carrier) × σ)))
    (fallbackPatch : Carrier × ((Fin dimension → Carrier) × σ))
    (point : (List (P × List (Carrier × ((Fin dimension → Carrier) × σ))) ×
        List (Carrier × ((Fin dimension → Carrier) × σ))) ×
      (Nat × ((List Nat × List Nat) × σ)))
    (inside : (patchSplitMerge (parents := parents) dimension shapeReference shapeFinite
      fallback fallbackPatch).pairing.targetDomain point) :
    Dedekind.lt Dedekind.zero
      (patchSplitMergeFactor (parents := parents) (shapes := shapes) dimension fallback
        fallbackPatch point) :=
  patchSplitFactor_positive dimension shapeReference shapeFinite fallbackPatch inside.1.2.1.1.2

variable (parentReference : Measure parents) (parentFinite : Measure.SFinite parentReference)

/-- A fixed mixture of the four matter families. The weights choose patch
birth/death, then background birth/death, then reassignment, and the rest is
the centroid split/merge. -/
@[expose] noncomputable def matterKernel
    (fallback : P × List (Carrier × ((Fin dimension → Carrier) × σ)))
    (fallbackPatch : Carrier × ((Fin dimension → Carrier) × σ))
    (stateDensity : List (P × List (Carrier × ((Fin dimension → Carrier) × σ))) ×
      List (Carrier × ((Fin dimension → Carrier) × σ)) → Carrier)
    (stateDensityMeasurable :
      MeasurableMap (matterSpace parents (patchSpace dimension shapes)) borel stateDensity)
    (births : SplitMergeSelection (matterSpace parents (patchSpace dimension shapes)) _ _
      (birthSideReference dimension shapeReference shapeFinite 1)
      (birthSideReference dimension shapeReference shapeFinite 0))
    (backgrounds : SplitMergeSelection (matterSpace parents (patchSpace dimension shapes)) _ _
      (backgroundSideReference dimension shapeReference shapeFinite 1)
      (backgroundSideReference dimension shapeReference shapeFinite 0))
    (reassignments : SplitMergeSelection (matterSpace parents (patchSpace dimension shapes)) _ _
      reassignSideReference reassignSideReference)
    (splits : SplitMergeSelection (matterSpace parents (patchSpace dimension shapes)) _ _
      (splitSideReference dimension shapeReference shapeFinite)
      (mergeSideReference shapeReference shapeFinite))
    (birthWeight backgroundWeight reassignWeight : NNReal) :
    Kernel (matterSpace parents (patchSpace dimension shapes))
      (matterSpace parents (patchSpace dimension shapes)) :=
  Kernel.mixture birthWeight
    (splitMergeKernel births.kernel births.finite (patchBirthDeath fallback) stateDensity
      births.density (fun _ => Dedekind.one) stateDensityMeasurable births.measurable
      (MeasurableMap.constant _ borel Dedekind.one))
    (Kernel.mixture backgroundWeight
      (splitMergeKernel backgrounds.kernel backgrounds.finite backgroundBirthDeath stateDensity
        backgrounds.density (fun _ => Dedekind.one) stateDensityMeasurable
        backgrounds.measurable (MeasurableMap.constant _ borel Dedekind.one))
      (Kernel.mixture reassignWeight
        (splitMergeKernel reassignments.kernel reassignments.finite (patchReassign fallback)
          stateDensity reassignments.density (fun _ => Dedekind.one) stateDensityMeasurable
          reassignments.measurable (MeasurableMap.constant _ borel Dedekind.one))
        (splitMergeKernel splits.kernel splits.finite
          (patchSplitMerge dimension shapeReference shapeFinite fallback fallbackPatch)
          stateDensity splits.density
          (patchSplitMergeFactor dimension fallback fallbackPatch) stateDensityMeasurable
          splits.measurable (patchSplitMergeFactor_measurable dimension fallback fallbackPatch))))

/-- Every fixed mixture of the four matter families leaves invariant every
target with a density against the matter reference on `count + 2` clusters,
whatever the selections, as long as they have densities. -/
theorem matterKernel_invariant
    (fallback : P × List (Carrier × ((Fin dimension → Carrier) × σ)))
    (fallbackPatch : Carrier × ((Fin dimension → Carrier) × σ)) (count : Nat)
    {stateDensity : List (P × List (Carrier × ((Fin dimension → Carrier) × σ))) ×
      List (Carrier × ((Fin dimension → Carrier) × σ)) → Carrier}
    (stateDensityMeasurable :
      MeasurableMap (matterSpace parents (patchSpace dimension shapes)) borel stateDensity)
    (stateNonnegative : ∀ state, Dedekind.le Dedekind.zero (stateDensity state))
    (target : Measure (matterSpace parents (patchSpace dimension shapes)))
    (targetDensity : target =
      (matterReference parentReference parentFinite
        (patchReference dimension shapeReference shapeFinite)
        (patchReferenceSFinite dimension shapeReference shapeFinite) (count + 1 + 1)).withDensity
        (fun state => ENNReal.ofReal (stateDensity state)))
    (births : SplitMergeSelection (matterSpace parents (patchSpace dimension shapes)) _ _
      (birthSideReference dimension shapeReference shapeFinite 1)
      (birthSideReference dimension shapeReference shapeFinite 0))
    (backgrounds : SplitMergeSelection (matterSpace parents (patchSpace dimension shapes)) _ _
      (backgroundSideReference dimension shapeReference shapeFinite 1)
      (backgroundSideReference dimension shapeReference shapeFinite 0))
    (reassignments : SplitMergeSelection (matterSpace parents (patchSpace dimension shapes)) _ _
      reassignSideReference reassignSideReference)
    (splits : SplitMergeSelection (matterSpace parents (patchSpace dimension shapes)) _ _
      (splitSideReference dimension shapeReference shapeFinite)
      (mergeSideReference shapeReference shapeFinite))
    {birthWeight backgroundWeight reassignWeight : NNReal}
    (birthBounded : NNReal.le birthWeight NNReal.one)
    (backgroundBounded : NNReal.le backgroundWeight NNReal.one)
    (reassignBounded : NNReal.le reassignWeight NNReal.one) :
    KernelInvariant target
      (matterKernel dimension shapeReference shapeFinite fallback fallbackPatch stateDensity
        stateDensityMeasurable births backgrounds reassignments splits birthWeight
        backgroundWeight reassignWeight) := by
  unfold matterKernel
  refine invariant_mixture target birthWeight birthBounded ?_
    (invariant_mixture target backgroundWeight backgroundBounded ?_
      (invariant_mixture target reassignWeight reassignBounded ?_ ?_))
  · exact splitMergeKernel_invariant (selectionDensityMeasurable := births.measurable)
      (factorMeasurable := MeasurableMap.constant _ borel Dedekind.one) _ _ target
      targetDensity stateNonnegative births.markov births.represents births.nonnegative
      (patchBirthDeath_reference_change parentReference parentFinite
        (patchReference dimension shapeReference shapeFinite)
        (patchReferenceSFinite dimension shapeReference shapeFinite) fallback (count + 1))
      (fun _ _ => Dedekind.one_positive)
  · exact splitMergeKernel_invariant (selectionDensityMeasurable := backgrounds.measurable)
      (factorMeasurable := MeasurableMap.constant _ borel Dedekind.one) _ _ target
      targetDensity stateNonnegative backgrounds.markov backgrounds.represents
      backgrounds.nonnegative
      (backgroundBirthDeath_reference_change parentReference parentFinite
        (patchReference dimension shapeReference shapeFinite)
        (patchReferenceSFinite dimension shapeReference shapeFinite) (count + 1 + 1))
      (fun _ _ => Dedekind.one_positive)
  · exact splitMergeKernel_invariant (selectionDensityMeasurable := reassignments.measurable)
      (factorMeasurable := MeasurableMap.constant _ borel Dedekind.one) _ _ target
      targetDensity stateNonnegative reassignments.markov reassignments.represents
      reassignments.nonnegative
      (patchReassign_reference_change parentReference parentFinite
        (patchReference dimension shapeReference shapeFinite)
        (patchReferenceSFinite dimension shapeReference shapeFinite) fallback count)
      (fun _ _ => Dedekind.one_positive)
  · exact splitMergeKernel_invariant (selectionDensityMeasurable := splits.measurable)
      (factorMeasurable := patchSplitMergeFactor_measurable dimension fallback fallbackPatch)
      _ _ target targetDensity stateNonnegative splits.markov splits.represents
      splits.nonnegative
      (patchSplitMerge_reference_change dimension shapeReference shapeFinite parentReference
        parentFinite fallback fallbackPatch (count + 1))
      (patchSplitMergeFactor_positive dimension shapeReference shapeFinite fallback
        fallbackPatch)

/-! Each family alone is a `splitMergeKernel` fed its L2a reference change. -/

example
    (fallback : P × List (Carrier × ((Fin dimension → Carrier) × σ))) (count : Nat)
    {stateDensity : List (P × List (Carrier × ((Fin dimension → Carrier) × σ))) ×
      List (Carrier × ((Fin dimension → Carrier) × σ)) → Carrier}
    (stateDensityMeasurable :
      MeasurableMap (matterSpace parents (patchSpace dimension shapes)) borel stateDensity)
    (stateNonnegative : ∀ state, Dedekind.le Dedekind.zero (stateDensity state))
    (target : Measure (matterSpace parents (patchSpace dimension shapes)))
    (targetDensity : target =
      (matterReference parentReference parentFinite
        (patchReference dimension shapeReference shapeFinite)
        (patchReferenceSFinite dimension shapeReference shapeFinite) (count + 1 + 1)).withDensity
        (fun state => ENNReal.ofReal (stateDensity state)))
    (births : SplitMergeSelection (matterSpace parents (patchSpace dimension shapes)) _ _
      (birthSideReference dimension shapeReference shapeFinite 1)
      (birthSideReference dimension shapeReference shapeFinite 0)) :
    KernelInvariant target
      (splitMergeKernel births.kernel births.finite (patchBirthDeath fallback) stateDensity
        births.density (fun _ => Dedekind.one) stateDensityMeasurable births.measurable
        (MeasurableMap.constant _ borel Dedekind.one)) :=
  splitMergeKernel_invariant _ _ target targetDensity stateNonnegative births.markov
    births.represents births.nonnegative
    (patchBirthDeath_reference_change parentReference parentFinite
      (patchReference dimension shapeReference shapeFinite)
      (patchReferenceSFinite dimension shapeReference shapeFinite) fallback (count + 1))
    (fun _ _ => Dedekind.one_positive)

example
    (count : Nat)
    {stateDensity : List (P × List (Carrier × ((Fin dimension → Carrier) × σ))) ×
      List (Carrier × ((Fin dimension → Carrier) × σ)) → Carrier}
    (stateDensityMeasurable :
      MeasurableMap (matterSpace parents (patchSpace dimension shapes)) borel stateDensity)
    (stateNonnegative : ∀ state, Dedekind.le Dedekind.zero (stateDensity state))
    (target : Measure (matterSpace parents (patchSpace dimension shapes)))
    (targetDensity : target =
      (matterReference parentReference parentFinite
        (patchReference dimension shapeReference shapeFinite)
        (patchReferenceSFinite dimension shapeReference shapeFinite) (count + 1 + 1)).withDensity
        (fun state => ENNReal.ofReal (stateDensity state)))
    (backgrounds : SplitMergeSelection (matterSpace parents (patchSpace dimension shapes)) _ _
      (backgroundSideReference dimension shapeReference shapeFinite 1)
      (backgroundSideReference dimension shapeReference shapeFinite 0)) :
    KernelInvariant target
      (splitMergeKernel backgrounds.kernel backgrounds.finite backgroundBirthDeath stateDensity
        backgrounds.density (fun _ => Dedekind.one) stateDensityMeasurable
        backgrounds.measurable (MeasurableMap.constant _ borel Dedekind.one)) :=
  splitMergeKernel_invariant _ _ target targetDensity stateNonnegative backgrounds.markov
    backgrounds.represents backgrounds.nonnegative
    (backgroundBirthDeath_reference_change parentReference parentFinite
      (patchReference dimension shapeReference shapeFinite)
      (patchReferenceSFinite dimension shapeReference shapeFinite) (count + 1 + 1))
    (fun _ _ => Dedekind.one_positive)

example
    (fallback : P × List (Carrier × ((Fin dimension → Carrier) × σ))) (count : Nat)
    {stateDensity : List (P × List (Carrier × ((Fin dimension → Carrier) × σ))) ×
      List (Carrier × ((Fin dimension → Carrier) × σ)) → Carrier}
    (stateDensityMeasurable :
      MeasurableMap (matterSpace parents (patchSpace dimension shapes)) borel stateDensity)
    (stateNonnegative : ∀ state, Dedekind.le Dedekind.zero (stateDensity state))
    (target : Measure (matterSpace parents (patchSpace dimension shapes)))
    (targetDensity : target =
      (matterReference parentReference parentFinite
        (patchReference dimension shapeReference shapeFinite)
        (patchReferenceSFinite dimension shapeReference shapeFinite) (count + 1 + 1)).withDensity
        (fun state => ENNReal.ofReal (stateDensity state)))
    (reassignments : SplitMergeSelection (matterSpace parents (patchSpace dimension shapes)) _ _
      reassignSideReference reassignSideReference) :
    KernelInvariant target
      (splitMergeKernel reassignments.kernel reassignments.finite (patchReassign fallback)
        stateDensity reassignments.density (fun _ => Dedekind.one) stateDensityMeasurable
        reassignments.measurable (MeasurableMap.constant _ borel Dedekind.one)) :=
  splitMergeKernel_invariant _ _ target targetDensity stateNonnegative reassignments.markov
    reassignments.represents reassignments.nonnegative
    (patchReassign_reference_change parentReference parentFinite
      (patchReference dimension shapeReference shapeFinite)
      (patchReferenceSFinite dimension shapeReference shapeFinite) fallback count)
    (fun _ _ => Dedekind.one_positive)

example
    (fallback : P × List (Carrier × ((Fin dimension → Carrier) × σ))) (count : Nat)
    {stateDensity : List (P × List (Carrier × ((Fin dimension → Carrier) × σ))) ×
      List (Carrier × ((Fin dimension → Carrier) × σ)) → Carrier}
    (stateDensityMeasurable :
      MeasurableMap (matterSpace parents (patchSpace dimension shapes)) borel stateDensity)
    (stateNonnegative : ∀ state, Dedekind.le Dedekind.zero (stateDensity state))
    (target : Measure (matterSpace parents (patchSpace dimension shapes)))
    (targetDensity : target =
      (matterReference parentReference parentFinite
        (patchReference dimension shapeReference shapeFinite)
        (patchReferenceSFinite dimension shapeReference shapeFinite) (count + 1 + 1)).withDensity
        (fun state => ENNReal.ofReal (stateDensity state)))
    (fallbackPatch : Carrier × ((Fin dimension → Carrier) × σ))
    (splits : SplitMergeSelection (matterSpace parents (patchSpace dimension shapes)) _ _
      (splitSideReference dimension shapeReference shapeFinite)
      (mergeSideReference shapeReference shapeFinite)) :
    KernelInvariant target
      (splitMergeKernel splits.kernel splits.finite
        (patchSplitMerge dimension shapeReference shapeFinite fallback fallbackPatch)
        stateDensity splits.density (patchSplitMergeFactor dimension fallback fallbackPatch)
        stateDensityMeasurable splits.measurable
        (patchSplitMergeFactor_measurable dimension fallback fallbackPatch)) :=
  splitMergeKernel_invariant _ _ target targetDensity stateNonnegative splits.markov
    splits.represents splits.nonnegative
    (patchSplitMerge_reference_change dimension shapeReference shapeFinite parentReference
      parentFinite fallback fallbackPatch (count + 1))
    (patchSplitMergeFactor_positive dimension shapeReference shapeFinite fallback fallbackPatch)

end
end Problib.Inference
