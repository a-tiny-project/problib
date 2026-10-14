module

public import Problib.Inference.SplitMerge.Move
public import Problib.Measure.Equivalence.Fibred
public import Problib.Measure.Product.Countable

set_option autoImplicit false

/-!
# Lifting split/merge moves

A move on a focused part of the state runs on the whole state through a lens
onto the focus and the rest (`SplitMergeMove.along`). When the lens preserves
reference, the lifted move changes reference by the move's factor, read at the
focus (`SplitMergeMove.along_reference_change`).

A countable family of moves runs as one move whose auxiliary carries the
index, which the pairing keeps (`SplitMergeMove.indexed`). It changes
reference by each member's factor, read at the index
(`SplitMergeMove.indexed_reference_change`).
-/

namespace Problib.Inference

open Problib.Real Problib.Measure
open Problib.Real.Construction
open Problib.Measure.Real (Carrier borel measurable_mul)

public section

universe u v w x y

variable {X : Type u} {A : Type v} {B : Type w} {F : Type x} {R : Type y}
  {space : Space X} {splitAux : Space A} {mergeAux : Space B}
  {focus : Space F} {rest : Space R}

/-- Run a move on a focused part through a lens onto the focus and the rest.
The auxiliary sits beside the focus while the move runs. -/
@[expose] def SplitMergeMove.along (move : SplitMergeMove focus splitAux mergeAux)
    (lens : MeasurablePartialEquivalence space (Space.product focus rest)) :
    SplitMergeMove space splitAux mergeAux where
  pairing := (lens.productRight splitAux).trans
    ((MeasurablePartialEquivalence.ofEquivalence
        (MeasurableEquivalence.commuteRight focus rest splitAux)).trans
      ((move.pairing.productRight rest).trans
        ((MeasurablePartialEquivalence.ofEquivalence
            (MeasurableEquivalence.commuteRight focus mergeAux rest)).trans
          (lens.productRight mergeAux).symm)))

/-- Through a reference-preserving lens, the lifted move changes reference by
the move's factor at the focus and the merge auxiliary. -/
theorem SplitMergeMove.along_reference_change (move : SplitMergeMove focus splitAux mergeAux)
    {lens : MeasurablePartialEquivalence space (Space.product focus rest)}
    {state : Measure space} {focusReference : Measure focus} {restReference : Measure rest}
    (restFinite : Measure.SFinite restReference)
    {splitReference : Measure splitAux} (splitFinite : Measure.SFinite splitReference)
    {mergeReference : Measure mergeAux} (mergeFinite : Measure.SFinite mergeReference)
    (preserves : lens.ReferenceChange state
      (Measure.prod focusReference restReference restFinite) (fun _ => Dedekind.one))
    {factor : F × B → Carrier}
    (factorMeasurable : MeasurableMap (Space.product focus mergeAux) borel factor)
    (factorNonnegative : ∀ value, move.pairing.targetDomain value →
      Dedekind.le Dedekind.zero (factor value))
    (change : move.pairing.ReferenceChange
      (Measure.prod focusReference splitReference splitFinite)
      (Measure.prod focusReference mergeReference mergeFinite) factor) :
    (move.along lens).pairing.ReferenceChange
      (Measure.prod state splitReference splitFinite)
      (Measure.prod state mergeReference mergeFinite)
      (fun point => factor ((lens.forward point.1).1, point.2)) := by
  have unitNonnegative : Dedekind.le Dedekind.zero Dedekind.one :=
    Dedekind.le_of_lt Dedekind.one_positive
  have lensSplit := MeasurablePartialEquivalence.reference_change_productRight splitReference
    splitFinite (MeasurableMap.constant _ borel Dedekind.one) preserves
  have lensMerge := MeasurablePartialEquivalence.reference_change_productRight mergeReference
    mergeFinite (MeasurableMap.constant _ borel Dedekind.one) preserves
  have unlens := MeasurablePartialEquivalence.reference_change_symm
    (MeasurableMap.constant _ borel Dedekind.one) lensMerge
    (fun _ _ => Dedekind.one_positive)
  have leaving := MeasurePreserving.reference_change_before
    (MeasurePreserving.commuteRight focusReference mergeReference restReference mergeFinite
      restFinite)
    (MeasurableMap.constant _ borel _) unlens
    (fun _ _ => by
      show Dedekind.le Dedekind.zero (Dedekind.inverse Dedekind.one)
      rw [Dedekind.inverse_one]
      exact unitNonnegative)
  have moved := MeasurablePartialEquivalence.reference_change_productRight restReference
    restFinite factorMeasurable change
  have running := MeasurablePartialEquivalence.reference_change_trans
    (MeasurableMap.comp factorMeasurable (Space.first_measurable _ _))
    (MeasurableMap.constant _ borel _) moved leaving
    (fun value inside => factorNonnegative _ inside)
    (fun _ _ => by
      show Dedekind.le Dedekind.zero (Dedekind.inverse Dedekind.one)
      rw [Dedekind.inverse_one]
      exact unitNonnegative)
  have runningMeasurable : MeasurableMap (Space.product space mergeAux) borel
      (fun value => Dedekind.mul (Dedekind.inverse Dedekind.one)
        (factor (((MeasurablePartialEquivalence.ofEquivalence
          (MeasurableEquivalence.commuteRight focus mergeAux rest)).trans
          (lens.productRight mergeAux).symm).inverse value).1)) :=
    measurable_mul (MeasurableMap.constant _ borel _)
      (MeasurableMap.comp factorMeasurable (MeasurableMap.comp (Space.first_measurable _ _)
        ((MeasurablePartialEquivalence.ofEquivalence
          (MeasurableEquivalence.commuteRight focus mergeAux rest)).trans
          (lens.productRight mergeAux).symm).inverseMeasurable))
  have runningNonnegative : ∀ value,
      ((move.pairing.productRight rest).trans
        ((MeasurablePartialEquivalence.ofEquivalence
          (MeasurableEquivalence.commuteRight focus mergeAux rest)).trans
          (lens.productRight mergeAux).symm)).targetDomain value →
      Dedekind.le Dedekind.zero (Dedekind.mul (Dedekind.inverse Dedekind.one)
        (factor (((MeasurablePartialEquivalence.ofEquivalence
          (MeasurableEquivalence.commuteRight focus mergeAux rest)).trans
          (lens.productRight mergeAux).symm).inverse value).1)) := by
    intro value inside
    rw [Dedekind.inverse_one, Dedekind.one_mul]
    exact factorNonnegative _ inside.2
  have entering := MeasurePreserving.reference_change_before
    (MeasurePreserving.commuteRight focusReference restReference splitReference restFinite
      splitFinite)
    runningMeasurable running runningNonnegative
  have whole := MeasurablePartialEquivalence.reference_change_trans
    (MeasurableMap.constant _ borel _) runningMeasurable lensSplit entering
    (fun _ _ => unitNonnegative) (fun value inside => runningNonnegative value inside.1)
  refine MeasurablePartialEquivalence.reference_change_congr (fun point _ => ?_) whole
  show Dedekind.mul (Dedekind.mul (Dedekind.inverse Dedekind.one)
      (factor ((lens.forward point.1).1, point.2))) Dedekind.one = _
  rw [Dedekind.inverse_one, Dedekind.one_mul, Dedekind.mul_one]

/-- A countable family of moves as one move. The auxiliary carries the index,
and the pairing keeps it. -/
@[expose] def SplitMergeMove.indexed {ι : Type x} (code : ι → Nat)
    (injective : Function.Injective code) (moves : ι → SplitMergeMove space splitAux mergeAux) :
    SplitMergeMove space (Space.product (Space.discrete ι) splitAux)
      (Space.product (Space.discrete ι) mergeAux) where
  pairing := (MeasurablePartialEquivalence.ofEquivalence
      (MeasurableEquivalence.commuteLeft space (Space.discrete ι) splitAux)).trans
    ((MeasurablePartialEquivalence.fibred (Space.discrete ι)
        (fun index => (moves index).pairing)
        (MeasurableMap.set_uncurry_of_countable_first code injective
          (sets := fun index => (moves index).pairing.sourceDomain)
          (fun index => (moves index).pairing.sourceMeasurable))
        (MeasurableMap.set_uncurry_of_countable_first code injective
          (sets := fun index => (moves index).pairing.targetDomain)
          (fun index => (moves index).pairing.targetMeasurable))
        (MeasurableMap.uncurry_of_countable_first code injective
          (function := fun index => (moves index).pairing.forward)
          (fun index => (moves index).pairing.forwardMeasurable))
        (MeasurableMap.uncurry_of_countable_first code injective
          (function := fun index => (moves index).pairing.inverse)
          (fun index => (moves index).pairing.inverseMeasurable))).trans
      (MeasurablePartialEquivalence.ofEquivalence
        (MeasurableEquivalence.commuteLeft (Space.discrete ι) space mergeAux)))

/-- The indexed move changes reference by each member's factor, read at the
index the merge side carries. -/
theorem SplitMergeMove.indexed_reference_change {ι : Type x} (code : ι → Nat)
    (injective : Function.Injective code) (moves : ι → SplitMergeMove space splitAux mergeAux)
    {state : Measure space} (stateFinite : Measure.SFinite state)
    (indexReference : Measure (Space.discrete ι)) (indexFinite : Measure.SFinite indexReference)
    {splitReference : Measure splitAux} (splitFinite : Measure.SFinite splitReference)
    {mergeReference : Measure mergeAux} (mergeFinite : Measure.SFinite mergeReference)
    {factor : ι → X × B → Carrier}
    (factorMeasurable : ∀ index,
      MeasurableMap (Space.product space mergeAux) borel (factor index))
    (factorNonnegative : ∀ index value, (moves index).pairing.targetDomain value →
      Dedekind.le Dedekind.zero (factor index value))
    (change : ∀ index, (moves index).pairing.ReferenceChange
      (Measure.prod state splitReference splitFinite)
      (Measure.prod state mergeReference mergeFinite) (factor index)) :
    (SplitMergeMove.indexed code injective moves).pairing.ReferenceChange
      (Measure.prod state (Measure.prod indexReference splitReference splitFinite)
        (indexFinite.prod splitFinite))
      (Measure.prod state (Measure.prod indexReference mergeReference mergeFinite)
        (indexFinite.prod mergeFinite))
      (fun point => factor point.2.1 (point.1, point.2.2)) := by
  have jointMeasurable : MeasurableMap
      (Space.product (Space.discrete ι) (Space.product space mergeAux)) borel
      (fun point => factor point.1 point.2) :=
    MeasurableMap.uncurry_of_countable_first code injective factorMeasurable
  have fibre := MeasurablePartialEquivalence.reference_change_fibred (Space.discrete ι)
    (MeasurableMap.set_uncurry_of_countable_first code injective
      (sets := fun index => (moves index).pairing.sourceDomain)
      (fun index => (moves index).pairing.sourceMeasurable))
    (MeasurableMap.set_uncurry_of_countable_first code injective
      (sets := fun index => (moves index).pairing.targetDomain)
      (fun index => (moves index).pairing.targetMeasurable))
    (MeasurableMap.uncurry_of_countable_first code injective
      (function := fun index => (moves index).pairing.forward)
      (fun index => (moves index).pairing.forwardMeasurable))
    (MeasurableMap.uncurry_of_countable_first code injective
      (function := fun index => (moves index).pairing.inverse)
      (fun index => (moves index).pairing.inverseMeasurable))
    indexReference (stateFinite.prod splitFinite) (stateFinite.prod mergeFinite)
    jointMeasurable change
  have leaving := MeasurePreserving.reference_change_after
    (MeasurePreserving.commuteLeft indexReference state mergeReference indexFinite
      stateFinite mergeFinite)
    jointMeasurable fibre (fun point inside => factorNonnegative point.1 point.2 inside)
  exact MeasurePreserving.reference_change_before
    (MeasurePreserving.commuteLeft state indexReference splitReference stateFinite
      indexFinite splitFinite)
    (MeasurableMap.comp jointMeasurable
      (MeasurableEquivalence.commuteLeft (Space.discrete ι) space mergeAux).inverse_measurable)
    leaving (fun point inside => factorNonnegative _ _ inside.2)

end
end Problib.Inference
