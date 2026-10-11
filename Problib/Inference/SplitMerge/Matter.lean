module

public import Problib.Inference.SplitMerge.Replace
public import Problib.Inference.SplitMerge.Lift
public import Problib.Inference.SplitMerge.Transfer
public import Problib.Inference.SplitMerge.OneTwo
public import Problib.Inference.SplitMerge.Centroid
public import Problib.Countable.Bijection

set_option autoImplicit false

/-!
# The free-matter configuration

The state holds object clusters in label order, each a parent with its
patches, and the background patches (`matterSpace`). The reference is the
ordered iid power of a fixed number of clusters, each a parent under its
reference beside a labelled configuration of patches, and a labelled
configuration of background patches (`matterReference`). Labelled
configurations weigh every count by one, so no factorial enters.

A lens brings one cluster's patches to the front (`clusterLens`), and another
brings the background forward (`backgroundLens`). Both preserve reference.
The moves run a birth of one patch through them (`patchBirth`), indexed by
cluster (`patchBirthDeath`) and on the background (`backgroundBirthDeath`).
Every one changes reference by one. A lens onto two clusters' patches
(`pairLens`) carries a transfer between them, indexed by the ordered pair's
code (`patchReassign`), also with factor one. The centroid split of one patch
into two runs in any cluster (`patchSplitMerge`), with the centroid Jacobian
at the merged pair (`patchSplitMergeFactor`).
-/

namespace Problib.Inference

open Problib.Real Problib.Measure
open Problib.Real.Construction
open Problib.Measure.Real (Carrier borel volume volumeSFinite volumePi volumePiSFinite)

universe u

public section

variable {P Q : Type u}

/-- One cluster: a parent and its patches. -/
abbrev clusterSpace (parents : Space P) (patches : Space Q) : Space (P × List Q) :=
  Space.product parents (Space.list patches)

/-- The clusters in label order, and the background patches. -/
abbrev matterSpace (parents : Space P) (patches : Space Q) :
    Space (List (P × List Q) × List Q) :=
  Space.product (Space.list (clusterSpace parents patches)) (Space.list patches)

/-- What stays beside one cluster's patches: its parent, the other clusters
and the background. -/
abbrev clusterRest (parents : Space P) (patches : Space Q) :
    Space (P × (List (P × List Q) × List Q)) :=
  Space.product parents (matterSpace parents patches)

variable {parents : Space P} {patches : Space Q}

section Reference

variable (parentReference : Measure parents) (parentFinite : Measure.SFinite parentReference)
  (patchReference : Measure patches) (patchFinite : Measure.SFinite patchReference)

/-- Patches under the labelled configuration reference. -/
@[expose] noncomputable def patchConfiguration : Measure (Space.list patches) :=
  configurationReference patchReference patchFinite labelled

noncomputable def patchConfigurationFinite :
    Measure.SFinite (patchConfiguration patchReference patchFinite) :=
  Measure.SFinite.configurationReference patchReference patchFinite labelled

/-- A parent under its reference, beside its patches. -/
@[expose] noncomputable def clusterReference :
    Measure (clusterSpace parents patches) :=
  Measure.prod parentReference (patchConfiguration patchReference patchFinite)
    (patchConfigurationFinite patchReference patchFinite)

noncomputable def clusterReferenceFinite :
    Measure.SFinite (clusterReference parentReference patchReference patchFinite) :=
  parentFinite.prod (patchConfigurationFinite patchReference patchFinite)

/-- A fixed number of clusters, each under the cluster reference, beside the
background patches. -/
@[expose] noncomputable def matterReference (clusterCount : Nat) :
    Measure (matterSpace parents patches) :=
  Measure.prod
    (Measure.listPower (clusterReference parentReference patchReference patchFinite)
      (clusterReferenceFinite parentReference parentFinite patchReference patchFinite)
      clusterCount)
    (patchConfiguration patchReference patchFinite)
    (patchConfigurationFinite patchReference patchFinite)

noncomputable def matterReferenceFinite (clusterCount : Nat) :
    Measure.SFinite
      (matterReference parentReference parentFinite patchReference patchFinite clusterCount) :=
  (Measure.SFinite.listPower
    (clusterReferenceFinite parentReference parentFinite patchReference patchFinite)
    clusterCount).prod (patchConfigurationFinite patchReference patchFinite)

end Reference

/-- Move a cluster's patches to the front: `(((p, qs), others), background)`
goes to `(qs, (p, (others, background)))`. -/
@[expose] def clusterReshape (parents : Space P) (patches : Space Q) :
    MeasurableEquivalence
      (Space.product
        (Space.product (clusterSpace parents patches)
          (Space.list (clusterSpace parents patches)))
        (Space.list patches))
      (Space.product (Space.list patches) (clusterRest parents patches)) :=
  (MeasurableEquivalence.associate _ _ _).trans
    (((MeasurableEquivalence.swap parents (Space.list patches)).product
        (MeasurableEquivalence.identity (matterSpace parents patches))).trans
      (MeasurableEquivalence.associate _ _ _))

/-- Cluster `index`'s patches, beside its parent, the other clusters and the
background. The fallback cluster lies outside the domain. -/
@[expose] def clusterLens (fallback : P × List Q) (index : Nat) :
    MeasurablePartialEquivalence (matterSpace parents patches)
      (Space.product (Space.list patches) (clusterRest parents patches)) :=
  ((frontLens (clusterSpace parents patches) fallback index).productRight
      (Space.list patches)).trans
    (MeasurablePartialEquivalence.ofEquivalence (clusterReshape parents patches))

/-- The background patches, beside the clusters. -/
@[expose] def backgroundLens :
    MeasurablePartialEquivalence (matterSpace parents patches)
      (Space.product (Space.list patches)
        (Space.list (clusterSpace parents patches))) :=
  MeasurablePartialEquivalence.ofEquivalence (MeasurableEquivalence.swap _ _)

/-- A birth of one patch: the born patch rides on the split side as a list of
length one, and the pairing sets it among the inserted entries. -/
@[expose] def patchBirth (patches : Space Q) :
    SplitMergeMove (Space.list patches)
      (Space.product schedulePair (Space.list patches))
      (Space.product schedulePair (Space.list patches)) :=
  SplitMergeMove.replace 0 1
    (MeasurablePartialEquivalence.ofEquivalence (MeasurableEquivalence.swap _ _))

/-- Natural numbers code themselves. -/
theorem nat_code_injective : Function.Injective (fun index : Nat => index) :=
  fun _ _ same => same

/-- A birth or death of one patch in any cluster. The auxiliary carries the
cluster index. -/
@[expose] def patchBirthDeath (fallback : P × List Q) :
    SplitMergeMove (matterSpace parents patches)
      (Space.product (Space.discrete Nat) (Space.product schedulePair (Space.list patches)))
      (Space.product (Space.discrete Nat)
        (Space.product schedulePair (Space.list patches))) :=
  SplitMergeMove.indexed (fun index : Nat => index) nat_code_injective
    (fun index => (patchBirth patches).along (clusterLens fallback index))

/-- A birth or death of one background patch. -/
@[expose] def backgroundBirthDeath :
    SplitMergeMove (matterSpace parents patches)
      (Space.product schedulePair (Space.list patches))
      (Space.product schedulePair (Space.list patches)) :=
  (patchBirth patches).along backgroundLens

section Change

variable (parentReference : Measure parents) (parentFinite : Measure.SFinite parentReference)
  (patchReference : Measure patches) (patchFinite : Measure.SFinite patchReference)

/-- Labelled coefficients give ratio one. -/
theorem coefficientRatio_labelled (removed inserted length : Nat) :
    NNReal.toReal (coefficientRatio labelled removed inserted length) = Dedekind.one := by
  unfold coefficientRatio labelled
  rw [NNReal.toReal_div, NNReal.toReal_one, Dedekind.div_eq_mul_inverse, Dedekind.inverse_one,
    Dedekind.mul_one]

/-- The cluster lens preserves reference: cluster `index`'s patches, beside its
parent, the other clusters and the background, under their references. -/
theorem clusterLens_reference_change (fallback : P × List Q) (count index : Nat) :
    (clusterLens (parents := parents) (patches := patches)
      fallback index).ReferenceChange
      (matterReference parentReference parentFinite patchReference patchFinite (count + 1))
      (Measure.prod (patchConfiguration patchReference patchFinite)
        (Measure.prod parentReference
          (matterReference parentReference parentFinite patchReference patchFinite count)
          (matterReferenceFinite parentReference parentFinite patchReference patchFinite count))
        (parentFinite.prod
          (matterReferenceFinite parentReference parentFinite patchReference patchFinite count)))
      (fun _ => Dedekind.one) := by
  let patchesFinite := patchConfigurationFinite patchReference patchFinite
  let clustersFinite := Measure.SFinite.listPower
    (clusterReferenceFinite parentReference parentFinite patchReference patchFinite) count
  have front := frontLens_reference_change
    (clusterReference parentReference patchReference patchFinite)
    (clusterReferenceFinite parentReference parentFinite patchReference patchFinite)
    fallback count index
  have moved := MeasurablePartialEquivalence.reference_change_productRight
    (patchConfiguration patchReference patchFinite) patchesFinite
    (MeasurableMap.constant _ borel Dedekind.one) front
  exact MeasurePreserving.reference_change_after
    ((MeasurePreserving.associate (clusterReference parentReference patchReference patchFinite)
        (Measure.listPower (clusterReference parentReference patchReference patchFinite)
          (clusterReferenceFinite parentReference parentFinite patchReference patchFinite)
          count)
        (patchConfiguration patchReference patchFinite) clustersFinite patchesFinite).trans
      ((MeasurePreserving.product (clustersFinite.prod patchesFinite)
          (clustersFinite.prod patchesFinite)
          (MeasurePreserving.swap parentReference (patchConfiguration patchReference patchFinite)
            parentFinite patchesFinite)
          (MeasurePreserving.refl
            (matterReference parentReference parentFinite patchReference patchFinite count))).trans
        (MeasurePreserving.associate (patchConfiguration patchReference patchFinite)
          parentReference
          (matterReference parentReference parentFinite patchReference patchFinite count)
          parentFinite (clustersFinite.prod patchesFinite))))
    (MeasurableMap.constant _ borel Dedekind.one) moved
    (fun _ _ => Dedekind.le_of_lt Dedekind.one_positive)

/-- A patch birth changes reference by one: the pairing preserves reference,
and labelled coefficients give ratio one. -/
theorem patchBirth_reference_change :
    (patchBirth patches).pairing.ReferenceChange
      (Measure.prod (patchConfiguration patchReference patchFinite)
        (Measure.prod positionCounting (Measure.listPower patchReference patchFinite 1)
          (Measure.SFinite.listPower patchFinite 1))
        (positionCountingFinite.prod (Measure.SFinite.listPower patchFinite 1)))
      (Measure.prod (patchConfiguration patchReference patchFinite)
        (Measure.prod positionCounting (Measure.listPower patchReference patchFinite 0)
          (Measure.SFinite.listPower patchFinite 0))
        (positionCountingFinite.prod (Measure.SFinite.listPower patchFinite 0)))
      (fun _ => Dedekind.one) := by
  have unitNonnegative : Dedekind.le Dedekind.zero Dedekind.one :=
    Dedekind.le_of_lt Dedekind.one_positive
  have replaced := SplitMergeMove.replace_reference_change patchReference patchFinite
    (coefficient := labelled) (fun _ => NNReal.one_ne_zero) 0 1
    (Measure.listPower patchReference patchFinite 1) (Measure.SFinite.listPower patchFinite 1)
    (Measure.listPower patchReference patchFinite 0) (Measure.SFinite.listPower patchFinite 0)
    (MeasurableMap.constant _ borel Dedekind.one) (fun _ _ => unitNonnegative)
    (MeasurePreserving.swap (Measure.listPower patchReference patchFinite 0)
      (Measure.listPower patchReference patchFinite 1) (Measure.SFinite.listPower patchFinite 0)
      (Measure.SFinite.listPower patchFinite 1)).reference_change
  refine MeasurablePartialEquivalence.reference_change_congr (fun point _ => ?_) replaced
  show Dedekind.mul Dedekind.one (NNReal.toReal (coefficientRatio labelled 0 1 point.1.length)) =
    Dedekind.one
  rw [coefficientRatio_labelled, Dedekind.mul_one]

/-- A patch birth or death in any cluster changes reference by one. The
cluster index takes the counting reference. -/
theorem patchBirthDeath_reference_change (fallback : P × List Q) (count : Nat) :
    (patchBirthDeath (parents := parents) (patches := patches)
      fallback).pairing.ReferenceChange
      (Measure.prod
        (matterReference parentReference parentFinite patchReference patchFinite (count + 1))
        (Measure.prod Measure.counting
          (Measure.prod positionCounting (Measure.listPower patchReference patchFinite 1)
            (Measure.SFinite.listPower patchFinite 1))
          (positionCountingFinite.prod (Measure.SFinite.listPower patchFinite 1)))
        (Measure.countingSigmaFinite.toSFinite.prod
          (positionCountingFinite.prod (Measure.SFinite.listPower patchFinite 1))))
      (Measure.prod
        (matterReference parentReference parentFinite patchReference patchFinite (count + 1))
        (Measure.prod Measure.counting
          (Measure.prod positionCounting (Measure.listPower patchReference patchFinite 0)
            (Measure.SFinite.listPower patchFinite 0))
          (positionCountingFinite.prod (Measure.SFinite.listPower patchFinite 0)))
        (Measure.countingSigmaFinite.toSFinite.prod
          (positionCountingFinite.prod (Measure.SFinite.listPower patchFinite 0))))
      (fun _ => Dedekind.one) := by
  have unitNonnegative : Dedekind.le Dedekind.zero Dedekind.one :=
    Dedekind.le_of_lt Dedekind.one_positive
  exact SplitMergeMove.indexed_reference_change (fun index : Nat => index) nat_code_injective
    (fun index => (patchBirth patches).along (clusterLens fallback index))
    (matterReferenceFinite parentReference parentFinite patchReference patchFinite (count + 1))
    Measure.counting Measure.countingSigmaFinite.toSFinite
    (positionCountingFinite.prod (Measure.SFinite.listPower patchFinite 1))
    (positionCountingFinite.prod (Measure.SFinite.listPower patchFinite 0))
    (factor := fun _ _ => Dedekind.one) (fun _ => MeasurableMap.constant _ borel _)
    (fun _ _ _ => unitNonnegative)
    (fun index => SplitMergeMove.along_reference_change (patchBirth patches)
      (parentFinite.prod
        (matterReferenceFinite parentReference parentFinite patchReference patchFinite count))
      (positionCountingFinite.prod (Measure.SFinite.listPower patchFinite 1))
      (positionCountingFinite.prod (Measure.SFinite.listPower patchFinite 0))
      (clusterLens_reference_change parentReference parentFinite patchReference patchFinite
        fallback count index)
      (MeasurableMap.constant _ borel _) (fun _ _ => unitNonnegative)
      (patchBirth_reference_change patchReference patchFinite))

/-- A birth or death of one background patch changes reference by one. -/
theorem backgroundBirthDeath_reference_change (count : Nat) :
    (backgroundBirthDeath (parents := parents)
      (patches := patches)).pairing.ReferenceChange
      (Measure.prod (matterReference parentReference parentFinite patchReference patchFinite count)
        (Measure.prod positionCounting (Measure.listPower patchReference patchFinite 1)
          (Measure.SFinite.listPower patchFinite 1))
        (positionCountingFinite.prod (Measure.SFinite.listPower patchFinite 1)))
      (Measure.prod (matterReference parentReference parentFinite patchReference patchFinite count)
        (Measure.prod positionCounting (Measure.listPower patchReference patchFinite 0)
          (Measure.SFinite.listPower patchFinite 0))
        (positionCountingFinite.prod (Measure.SFinite.listPower patchFinite 0)))
      (fun _ => Dedekind.one) := by
  have clustersFinite := Measure.SFinite.listPower
    (clusterReferenceFinite parentReference parentFinite patchReference patchFinite) count
  exact SplitMergeMove.along_reference_change (patchBirth patches) clustersFinite
    (positionCountingFinite.prod (Measure.SFinite.listPower patchFinite 1))
    (positionCountingFinite.prod (Measure.SFinite.listPower patchFinite 0))
    (MeasurePreserving.swap
      (Measure.listPower (clusterReference parentReference patchReference patchFinite)
        (clusterReferenceFinite parentReference parentFinite patchReference patchFinite) count)
      (patchConfiguration patchReference patchFinite) clustersFinite
      (patchConfigurationFinite patchReference patchFinite)).reference_change
    (MeasurableMap.constant _ borel _)
    (fun _ _ => Dedekind.le_of_lt Dedekind.one_positive)
    (patchBirth_reference_change patchReference patchFinite)

end Change

/-- What stays beside two clusters' patches: both parents, the other clusters
and the background. -/
abbrev pairRest (parents : Space P) (patches : Space Q) :
    Space (P × (P × (List (P × List Q) × List Q))) :=
  Space.product parents (clusterRest parents patches)

/-- Cluster `first`'s patches and, among the clusters that remain, cluster
`second`'s patches, beside both parents, the rest and the background. -/
@[expose] def pairLens (fallback : P × List Q) (first second : Nat) :
    MeasurablePartialEquivalence (matterSpace parents patches)
      (Space.product (Space.product (Space.list patches) (Space.list patches))
        (pairRest parents patches)) :=
  (clusterLens fallback first).trans
    (((((clusterLens fallback second).productLeft parents).trans
          (MeasurablePartialEquivalence.ofEquivalence
            (MeasurableEquivalence.commuteLeft parents (Space.list patches)
              (clusterRest parents patches)))).productLeft (Space.list patches)).trans
      (MeasurablePartialEquivalence.ofEquivalence
        (MeasurableEquivalence.associate (Space.list patches) (Space.list patches)
          (pairRest parents patches)).symm))

/-- Move one patch between two clusters. The auxiliary carries the code of the
ordered pair of clusters, and the two positions. -/
@[expose] def patchReassign (fallback : P × List Q) :
    SplitMergeMove (matterSpace parents patches)
      (Space.product (Space.discrete Nat) positionPair)
      (Space.product (Space.discrete Nat) positionPair) :=
  SplitMergeMove.indexed (fun index : Nat => index) nat_code_injective
    (fun index => (SplitMergeMove.transfer patches).along
      (pairLens fallback (Countable.Pair.decode index).1 (Countable.Pair.decode index).2))

section Centroid

variable {σ : Type u} {shapes : Space σ} (dimension : Nat) (shapeReference : Measure shapes)
  (shapeFinite : Measure.SFinite shapeReference)

/-- The centroid split of one patch into two, or the merge back. -/
@[expose] noncomputable def patchSplit
    (fallbackPatch : Carrier × ((Fin dimension → Carrier) × σ)) :
    SplitMergeMove (Space.list (patchSpace dimension shapes))
      (Space.product schedulePair (splitDraw dimension shapes))
      (Space.product schedulePair shapes) :=
  SplitMergeMove.replace 1 2
    (oneTwoPairing fallbackPatch (centroidPairing dimension shapeReference shapeFinite))

/-- The centroid split in any cluster. The auxiliary carries the cluster
index. -/
@[expose] noncomputable def patchSplitMerge {parents : Space P}
    (fallback : P × List (Carrier × ((Fin dimension → Carrier) × σ)))
    (fallbackPatch : Carrier × ((Fin dimension → Carrier) × σ)) :
    SplitMergeMove (matterSpace parents (patchSpace dimension shapes))
      (Space.product (Space.discrete Nat)
        (Space.product schedulePair (splitDraw dimension shapes)))
      (Space.product (Space.discrete Nat) (Space.product schedulePair shapes)) :=
  SplitMergeMove.indexed (fun index : Nat => index) nat_code_injective
    (fun index => (patchSplit dimension shapeReference shapeFinite fallbackPatch).along
      (clusterLens fallback index))

/-- The centroid Jacobian at a cluster's merged pair: the leading pair of the
paired entries, beside the kept shape. -/
@[expose] noncomputable def patchSplitFactor
    (fallbackPatch : Carrier × ((Fin dimension → Carrier) × σ))
    (point : List (Carrier × ((Fin dimension → Carrier) × σ)) ×
      ((List Nat × List Nat) × σ)) :
    Carrier :=
  centroidJacobian dimension
    (leadingPair fallbackPatch (pairedElements point.2.1.1 (point.1, point.2.2)).1,
      (pairedElements point.2.1.1 (point.1, point.2.2)).2)

/-- The centroid Jacobian at the merged pair of the indexed cluster. -/
@[expose] noncomputable def patchSplitMergeFactor
    (fallback : P × List (Carrier × ((Fin dimension → Carrier) × σ)))
    (fallbackPatch : Carrier × ((Fin dimension → Carrier) × σ))
    (point : (List (P × List (Carrier × ((Fin dimension → Carrier) × σ))) ×
        List (Carrier × ((Fin dimension → Carrier) × σ))) ×
      (Nat × ((List Nat × List Nat) × σ))) :
    Carrier :=
  patchSplitFactor dimension fallbackPatch
    (((clusterLens (parents := parents) (patches := patchSpace dimension shapes)
      fallback point.2.1).forward point.1).1, point.2.2)

end Centroid

section PairChange

variable (parentReference : Measure parents) (parentFinite : Measure.SFinite parentReference)
  (patchReference : Measure patches) (patchFinite : Measure.SFinite patchReference)

/-- The pair lens preserves reference: two clusters' patches, beside both
parents and the rest, under their references. -/
theorem pairLens_reference_change (fallback : P × List Q) (count first second : Nat) :
    (pairLens (parents := parents) (patches := patches) fallback first second).ReferenceChange
      (matterReference parentReference parentFinite patchReference patchFinite (count + 1 + 1))
      (Measure.prod
        (Measure.prod (patchConfiguration patchReference patchFinite)
          (patchConfiguration patchReference patchFinite)
          (patchConfigurationFinite patchReference patchFinite))
        (Measure.prod parentReference
          (Measure.prod parentReference
            (matterReference parentReference parentFinite patchReference patchFinite count)
            (matterReferenceFinite parentReference parentFinite patchReference patchFinite count))
          (parentFinite.prod
            (matterReferenceFinite parentReference parentFinite patchReference patchFinite count)))
        (parentFinite.prod (parentFinite.prod
          (matterReferenceFinite parentReference parentFinite patchReference patchFinite count))))
      (fun _ => Dedekind.one) := by
  have unitNonnegative : Dedekind.le Dedekind.zero Dedekind.one :=
    Dedekind.le_of_lt Dedekind.one_positive
  let patchesFinite := patchConfigurationFinite patchReference patchFinite
  let restFinite := parentFinite.prod
    (matterReferenceFinite parentReference parentFinite patchReference patchFinite count)
  have outer := clusterLens_reference_change parentReference parentFinite patchReference
    patchFinite fallback (count + 1) first
  have inner := MeasurablePartialEquivalence.reference_change_productLeft parentReference
    (matterReferenceFinite parentReference parentFinite patchReference patchFinite (count + 1))
    (patchesFinite.prod restFinite) (MeasurableMap.constant _ borel Dedekind.one)
    (clusterLens_reference_change parentReference parentFinite patchReference patchFinite
      fallback count second)
  have innerMoved := MeasurePreserving.reference_change_after
    (MeasurePreserving.commuteLeft parentReference
      (patchConfiguration patchReference patchFinite)
      (Measure.prod parentReference
        (matterReference parentReference parentFinite patchReference patchFinite count)
        (matterReferenceFinite parentReference parentFinite patchReference patchFinite count))
      parentFinite patchesFinite restFinite)
    (MeasurableMap.constant _ borel Dedekind.one) inner (fun _ _ => unitNonnegative)
  have middle := MeasurablePartialEquivalence.reference_change_productLeft
    (patchConfiguration patchReference patchFinite)
    (parentFinite.prod
      (matterReferenceFinite parentReference parentFinite patchReference patchFinite (count + 1)))
    (patchesFinite.prod (parentFinite.prod restFinite))
    (MeasurableMap.constant _ borel Dedekind.one) innerMoved
  have regrouped := MeasurePreserving.reference_change_after
    (MeasurePreserving.associate (patchConfiguration patchReference patchFinite)
      (patchConfiguration patchReference patchFinite)
      (Measure.prod parentReference
        (Measure.prod parentReference
          (matterReference parentReference parentFinite patchReference patchFinite count)
          (matterReferenceFinite parentReference parentFinite patchReference patchFinite count))
        restFinite)
      patchesFinite (parentFinite.prod restFinite)).symm
    (MeasurableMap.constant _ borel Dedekind.one) middle (fun _ _ => unitNonnegative)
  exact MeasurablePartialEquivalence.reference_change_congr
    (fun _ _ => Dedekind.mul_one Dedekind.one)
    (MeasurablePartialEquivalence.reference_change_trans
      (MeasurableMap.constant _ borel Dedekind.one)
      (MeasurableMap.constant _ borel Dedekind.one) outer regrouped
      (fun _ _ => unitNonnegative) (fun _ _ => unitNonnegative))

/-- Moving a patch between two clusters changes reference by one. The pair
code takes the counting reference, and each position the counting reference. -/
theorem patchReassign_reference_change (fallback : P × List Q) (count : Nat) :
    (patchReassign (parents := parents) (patches := patches)
      fallback).pairing.ReferenceChange
      (Measure.prod
        (matterReference parentReference parentFinite patchReference patchFinite (count + 1 + 1))
        (Measure.prod Measure.counting positionPairCounting positionPairCountingFinite)
        (Measure.countingSigmaFinite.toSFinite.prod positionPairCountingFinite))
      (Measure.prod
        (matterReference parentReference parentFinite patchReference patchFinite (count + 1 + 1))
        (Measure.prod Measure.counting positionPairCounting positionPairCountingFinite)
        (Measure.countingSigmaFinite.toSFinite.prod positionPairCountingFinite))
      (fun _ => Dedekind.one) := by
  have unitNonnegative : Dedekind.le Dedekind.zero Dedekind.one :=
    Dedekind.le_of_lt Dedekind.one_positive
  have transferring := MeasurablePartialEquivalence.reference_change_congr
    (fun point _ => by
      show Dedekind.mul (NNReal.toReal (coefficientRatio labelled 1 0 point.1.1.length))
        (NNReal.toReal (coefficientRatio labelled 0 1 point.1.2.length)) = Dedekind.one
      rw [coefficientRatio_labelled, coefficientRatio_labelled, Dedekind.mul_one])
    (SplitMergeMove.transfer_reference_change patchReference patchFinite
      (first := labelled) (second := labelled) (fun _ => NNReal.one_ne_zero)
      (fun _ => NNReal.one_ne_zero))
  exact SplitMergeMove.indexed_reference_change (fun index : Nat => index) nat_code_injective
    (fun index => (SplitMergeMove.transfer patches).along
      (pairLens fallback (Countable.Pair.decode index).1 (Countable.Pair.decode index).2))
    (matterReferenceFinite parentReference parentFinite patchReference patchFinite
      (count + 1 + 1))
    Measure.counting Measure.countingSigmaFinite.toSFinite
    positionPairCountingFinite positionPairCountingFinite
    (factor := fun _ _ => Dedekind.one) (fun _ => MeasurableMap.constant _ borel _)
    (fun _ _ _ => unitNonnegative)
    (fun index => SplitMergeMove.along_reference_change (SplitMergeMove.transfer patches)
      (parentFinite.prod (parentFinite.prod
        (matterReferenceFinite parentReference parentFinite patchReference patchFinite count)))
      positionPairCountingFinite positionPairCountingFinite
      (pairLens_reference_change parentReference parentFinite patchReference patchFinite
        fallback count (Countable.Pair.decode index).1 (Countable.Pair.decode index).2)
      (MeasurableMap.constant _ borel _) (fun _ _ => unitNonnegative) transferring)

end PairChange

section CentroidChange

variable {σ : Type u} {shapes : Space σ} (dimension : Nat) (shapeReference : Measure shapes)
  (shapeFinite : Measure.SFinite shapeReference)
  (parentReference : Measure parents) (parentFinite : Measure.SFinite parentReference)

/-- The split's draw reference: a fraction and a mean offset under volume, and
two child shapes. -/
@[expose] noncomputable def splitDrawReference : Measure (splitDraw dimension shapes) :=
  Measure.prod (Measure.prod volume (volumePi dimension) (volumePiSFinite dimension))
    (Measure.prod shapeReference shapeReference shapeFinite) (shapeFinite.prod shapeFinite)

noncomputable def splitDrawReferenceFinite :
    Measure.SFinite (splitDrawReference dimension shapeReference shapeFinite) :=
  (volumeSFinite.prod (volumePiSFinite dimension)).prod (shapeFinite.prod shapeFinite)

theorem patchSplitFactor_measurable
    (fallbackPatch : Carrier × ((Fin dimension → Carrier) × σ)) :
    MeasurableMap
      (Space.product (Space.list (patchSpace dimension shapes))
        (Space.product schedulePair shapes)) borel
      (patchSplitFactor dimension fallbackPatch) := by
  have leading : MeasurableMap
      (Space.product (Space.list (patchSpace dimension shapes)) shapes) borel
      (fun value => centroidJacobian dimension (leadingPair fallbackPatch value.1, value.2)) := by
    intro set setMeasurable
    exact (MeasurableMap.comp (centroidJacobian_measurable dimension)
      (Space.pair_measurable
        (MeasurableMap.comp (leadingPair_measurable _ fallbackPatch)
          (Space.first_measurable _ _))
        (Space.second_measurable _ _))) setMeasurable
  have joint : MeasurableMap
      (Space.product schedulePair
        (Space.product (Space.list (patchSpace dimension shapes)) shapes)) borel
      (fun input => centroidJacobian dimension
        (leadingPair fallbackPatch (pairedElements input.1.1 input.2).1,
          (pairedElements input.1.1 input.2).2)) := schedules_uncurry_measurable
    (function := fun schedules value =>
      centroidJacobian dimension
        (leadingPair fallbackPatch (pairedElements schedules.1 value).1,
          (pairedElements schedules.1 value).2))
    (fun schedules => MeasurableMap.comp leading (pairedElements_measurable schedules.1))
  intro set setMeasurable
  exact (MeasurableMap.comp joint
    (Space.pair_measurable
      (MeasurableMap.comp (Space.first_measurable _ _) (Space.second_measurable _ _))
      (Space.pair_measurable (Space.first_measurable _ _)
        (MeasurableMap.comp (Space.second_measurable _ _) (Space.second_measurable _ _)))))
    setMeasurable

/-- On the merge side of the patch split, the centroid Jacobian at the merged
pair is nonnegative. -/
theorem patchSplitFactor_nonnegative
    (fallbackPatch : Carrier × ((Fin dimension → Carrier) × σ))
    {point : List (Carrier × ((Fin dimension → Carrier) × σ)) ×
      ((List Nat × List Nat) × σ)}
    (inside : (patchSplit dimension shapeReference shapeFinite
      fallbackPatch).pairing.targetDomain point) :
    Dedekind.le Dedekind.zero (patchSplitFactor dimension fallbackPatch point) := by
  have paired : (oneTwoPairing fallbackPatch
      (centroidPairing dimension shapeReference shapeFinite)).targetDomain
      (pairedElements point.2.1.1.reverse.reverse (point.1, point.2.2)) :=
    replaceAt_target_paired inside.2.1.2
  rw [List.reverse_reverse] at paired
  exact centroidJacobian_nonnegative dimension shapeReference shapeFinite
    (oneTwoPairing_target_leading paired)

theorem patchSplitFactor_positive
    (fallbackPatch : Carrier × ((Fin dimension → Carrier) × σ))
    {point : List (Carrier × ((Fin dimension → Carrier) × σ)) ×
      ((List Nat × List Nat) × σ)}
    (inside : (patchSplit dimension shapeReference shapeFinite
      fallbackPatch).pairing.targetDomain point) :
    Dedekind.lt Dedekind.zero (patchSplitFactor dimension fallbackPatch point) := by
  have paired : (oneTwoPairing fallbackPatch
      (centroidPairing dimension shapeReference shapeFinite)).targetDomain
      (pairedElements point.2.1.1.reverse.reverse (point.1, point.2.2)) :=
    replaceAt_target_paired inside.2.1.2
  rw [List.reverse_reverse] at paired
  exact centroidJacobian_positive dimension shapeReference shapeFinite
    (oneTwoPairing_target_leading paired)

/-- The centroid split of one patch changes reference by the centroid Jacobian
at the merged pair. -/
theorem patchSplit_reference_change
    (fallbackPatch : Carrier × ((Fin dimension → Carrier) × σ)) :
    (patchSplit dimension shapeReference shapeFinite fallbackPatch).pairing.ReferenceChange
      (Measure.prod
        (patchConfiguration (patchReference dimension shapeReference shapeFinite)
          (patchReferenceSFinite dimension shapeReference shapeFinite))
        (Measure.prod positionCounting (splitDrawReference dimension shapeReference shapeFinite)
          (splitDrawReferenceFinite dimension shapeReference shapeFinite))
        (positionCountingFinite.prod
          (splitDrawReferenceFinite dimension shapeReference shapeFinite)))
      (Measure.prod
        (patchConfiguration (patchReference dimension shapeReference shapeFinite)
          (patchReferenceSFinite dimension shapeReference shapeFinite))
        (Measure.prod positionCounting shapeReference shapeFinite)
        (positionCountingFinite.prod shapeFinite))
      (patchSplitFactor dimension fallbackPatch) := by
  have oneTwoMeasurable : MeasurableMap
      (Space.product (Space.list (patchSpace dimension shapes)) shapes) borel
      (fun value => centroidJacobian dimension (leadingPair fallbackPatch value.1, value.2)) := by
    intro set setMeasurable
    exact (MeasurableMap.comp (centroidJacobian_measurable dimension)
      (Space.pair_measurable
        (MeasurableMap.comp (leadingPair_measurable _ fallbackPatch)
          (Space.first_measurable _ _))
        (Space.second_measurable _ _))) setMeasurable
  have listed := oneTwoPairing_reference_change
    (patchReference dimension shapeReference shapeFinite)
    (patchReferenceSFinite dimension shapeReference shapeFinite) fallbackPatch
    (splitDrawReferenceFinite dimension shapeReference shapeFinite) shapeFinite
    (centroidJacobian_measurable dimension)
    (fun _ inside => centroidJacobian_nonnegative dimension shapeReference shapeFinite inside)
    (centroidPairing_reference_change dimension shapeReference shapeFinite)
  have replaced := SplitMergeMove.replace_reference_change
    (patchReference dimension shapeReference shapeFinite)
    (patchReferenceSFinite dimension shapeReference shapeFinite)
    (coefficient := labelled) (fun _ => NNReal.one_ne_zero) 1 2
    (splitDrawReference dimension shapeReference shapeFinite)
    (splitDrawReferenceFinite dimension shapeReference shapeFinite)
    shapeReference shapeFinite oneTwoMeasurable
    (fun _ inside => centroidJacobian_nonnegative dimension shapeReference shapeFinite
      (oneTwoPairing_target_leading inside))
    listed
  refine MeasurablePartialEquivalence.reference_change_congr (fun point _ => ?_) replaced
  show Dedekind.mul
      (centroidJacobian dimension
        (leadingPair fallbackPatch (pairedElements point.2.1.1 (point.1, point.2.2)).1,
          (pairedElements point.2.1.1 (point.1, point.2.2)).2))
      (NNReal.toReal (coefficientRatio labelled 1 2 point.1.length)) = _
  rw [coefficientRatio_labelled, Dedekind.mul_one]
  rfl

/-- The centroid split in any cluster changes reference by the centroid
Jacobian at the indexed cluster's merged pair. -/
theorem patchSplitMerge_reference_change
    (fallback : P × List (Carrier × ((Fin dimension → Carrier) × σ)))
    (fallbackPatch : Carrier × ((Fin dimension → Carrier) × σ)) (count : Nat) :
    (patchSplitMerge (parents := parents) dimension shapeReference shapeFinite fallback
      fallbackPatch).pairing.ReferenceChange
      (Measure.prod
        (matterReference parentReference parentFinite
          (patchReference dimension shapeReference shapeFinite)
          (patchReferenceSFinite dimension shapeReference shapeFinite) (count + 1))
        (Measure.prod Measure.counting
          (Measure.prod positionCounting (splitDrawReference dimension shapeReference shapeFinite)
            (splitDrawReferenceFinite dimension shapeReference shapeFinite))
          (positionCountingFinite.prod
            (splitDrawReferenceFinite dimension shapeReference shapeFinite)))
        (Measure.countingSigmaFinite.toSFinite.prod (positionCountingFinite.prod
          (splitDrawReferenceFinite dimension shapeReference shapeFinite))))
      (Measure.prod
        (matterReference parentReference parentFinite
          (patchReference dimension shapeReference shapeFinite)
          (patchReferenceSFinite dimension shapeReference shapeFinite) (count + 1))
        (Measure.prod Measure.counting
          (Measure.prod positionCounting shapeReference shapeFinite)
          (positionCountingFinite.prod shapeFinite))
        (Measure.countingSigmaFinite.toSFinite.prod (positionCountingFinite.prod shapeFinite)))
      (patchSplitMergeFactor (parents := parents) (shapes := shapes) dimension fallback
        fallbackPatch) := by
  have factorMeasurable : MeasurableMap
      (Space.product (Space.list (patchSpace dimension shapes))
        (Space.product schedulePair shapes)) borel
      (patchSplitFactor dimension fallbackPatch) :=
    patchSplitFactor_measurable dimension fallbackPatch
  exact SplitMergeMove.indexed_reference_change (fun index : Nat => index) nat_code_injective
    (fun index => (patchSplit dimension shapeReference shapeFinite fallbackPatch).along
      (clusterLens fallback index))
    (matterReferenceFinite parentReference parentFinite
      (patchReference dimension shapeReference shapeFinite)
      (patchReferenceSFinite dimension shapeReference shapeFinite) (count + 1))
    Measure.counting Measure.countingSigmaFinite.toSFinite
    (positionCountingFinite.prod (splitDrawReferenceFinite dimension shapeReference shapeFinite))
    (positionCountingFinite.prod shapeFinite)
    (factor := fun index point => patchSplitFactor dimension fallbackPatch
      (((clusterLens (parents := parents) (patches := patchSpace dimension shapes)
        fallback index).forward point.1).1, point.2))
    (fun index => by
      intro set setMeasurable
      exact (MeasurableMap.comp factorMeasurable
        (Space.pair_measurable
          (MeasurableMap.comp (Space.first_measurable _ _)
            (MeasurableMap.comp (clusterLens fallback index).forwardMeasurable
              (Space.first_measurable _ _)))
          (Space.second_measurable _ _))) setMeasurable)
    (fun _ _ inside => patchSplitFactor_nonnegative dimension shapeReference shapeFinite
      fallbackPatch inside.1.1.2)
    (fun index => SplitMergeMove.along_reference_change
      (patchSplit dimension shapeReference shapeFinite fallbackPatch)
      (parentFinite.prod
        (matterReferenceFinite parentReference parentFinite
          (patchReference dimension shapeReference shapeFinite)
          (patchReferenceSFinite dimension shapeReference shapeFinite) count))
      (positionCountingFinite.prod (splitDrawReferenceFinite dimension shapeReference shapeFinite))
      (positionCountingFinite.prod shapeFinite)
      (clusterLens_reference_change parentReference parentFinite
        (patchReference dimension shapeReference shapeFinite)
        (patchReferenceSFinite dimension shapeReference shapeFinite) fallback count index)
      (patchSplitFactor_measurable dimension fallbackPatch)
      (fun _ inside => patchSplitFactor_nonnegative dimension shapeReference shapeFinite
        fallbackPatch inside)
      (patchSplit_reference_change dimension shapeReference shapeFinite fallbackPatch))

end CentroidChange

end
end Problib.Inference
