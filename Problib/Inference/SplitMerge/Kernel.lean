module

public import Problib.Inference.SplitMerge.Move
public import Problib.Inference.Involutive.Reference
public import Problib.Measure.Kernel.Product.Density
public import Problib.Measure.Kernel.Measurable
public import Problib.Measure.Integral.Lebesgue.Extensionality
public import Problib.Measure.Real.Order
public import Problib.Inference.MetropolisHastings.Support

set_option autoImplicit false

/-!
# The split/merge kernel

A selection kernel draws a side and its auxiliary. The move's involution
proposes, and the strict test on Green's density accepts
(`splitMergeKernel`). The extended target is the whole-state density times the
selection density against the extended reference, which the involution changes
by the move's Jacobian. So the kernel leaves the target invariant
(`splitMergeKernel_invariant`), its acceptance compares the extended mass with
the Jacobian times the mass at the image (`splitMergeKernel_accept`), and it
never proposes into zero target density from a supported state
(`splitMergeKernel_stays_in_support`). No model family appears in the
hypotheses.
-/

namespace Problib.Inference

open Problib.Real Problib.Measure
open Problib.Real.Construction
open Problib.Measure.Real (Carrier borel ofReal_measurable ofReal_mul measurable_mul
  measurable_eq)

universe u v w

variable {X : Type u} {A : Type v} {B : Type w}
  {space : Space X} {splitAux : Space A} {mergeAux : Space B}

public section

/-- The split-side reference on split auxiliaries and the merge-side reference
on merge auxiliaries. -/
@[expose] noncomputable def auxiliaryReference (splitReference : Measure splitAux)
    (mergeReference : Measure mergeAux) : Measure (Space.sum splitAux mergeAux) :=
  Measure.add (splitReference.map Sum.inl (MeasurableMap.inl _ _))
    (mergeReference.map Sum.inr (MeasurableMap.inr _ _))

noncomputable def auxiliaryReferenceFinite {splitReference : Measure splitAux}
    {mergeReference : Measure mergeAux} (splitFinite : Measure.SFinite splitReference)
    (mergeFinite : Measure.SFinite mergeReference) :
    Measure.SFinite (auxiliaryReference splitReference mergeReference) :=
  (splitFinite.map _ (MeasurableMap.inl _ _)).add (mergeFinite.map _ (MeasurableMap.inr _ _))

/-- The extended reference of product sides is the product of the state
reference and the auxiliary reference. -/
theorem extendedReference_prod (state : Measure space)
    {splitReference : Measure splitAux} (splitFinite : Measure.SFinite splitReference)
    {mergeReference : Measure mergeAux} (mergeFinite : Measure.SFinite mergeReference) :
    SplitMergeMove.extendedReference (Measure.prod state splitReference splitFinite)
        (Measure.prod state mergeReference mergeFinite) =
      Measure.prod state (auxiliaryReference splitReference mergeReference)
        (auxiliaryReferenceFinite splitFinite mergeFinite) := by
  refine (Measure.eq_iff_lintegral _ _).mpr fun function functionMeasurable => ?_
  have splitMeasurable : ENNRealMeasurable (Space.product space splitAux)
      (fun point : X × A => function (point.1, Sum.inl point.2)) :=
    functionMeasurable.comp (Space.pair_measurable (Space.first_measurable _ _)
      (MeasurableMap.comp (MeasurableMap.inl _ _) (Space.second_measurable _ _)))
  have mergeMeasurable : ENNRealMeasurable (Space.product space mergeAux)
      (fun point : X × B => function (point.1, Sum.inr point.2)) :=
    functionMeasurable.comp (Space.pair_measurable (Space.first_measurable _ _)
      (MeasurableMap.comp (MeasurableMap.inr _ _) (Space.second_measurable _ _)))
  have splitInner : ENNRealMeasurable space
      (fun input => lintegral splitReference (fun value => function (input, Sum.inl value))) :=
    Kernel.lintegral_measurable_joint (Kernel.const space splitReference)
      (Kernel.IsSFinite.const space splitFinite)
      (function := fun input value => function (input, Sum.inl value)) splitMeasurable
  have mergeInner : ENNRealMeasurable space
      (fun input => lintegral mergeReference (fun value => function (input, Sum.inr value))) :=
    Kernel.lintegral_measurable_joint (Kernel.const space mergeReference)
      (Kernel.IsSFinite.const space mergeFinite)
      (function := fun input value => function (input, Sum.inr value)) mergeMeasurable
  have sides : lintegral (SplitMergeMove.extendedReference
        (Measure.prod state splitReference splitFinite)
        (Measure.prod state mergeReference mergeFinite)) function =
      ENNReal.add
        (lintegral state (fun input =>
          lintegral splitReference (fun value => function (input, Sum.inl value))))
        (lintegral state (fun input =>
          lintegral mergeReference (fun value => function (input, Sum.inr value)))) := by
    unfold SplitMergeMove.extendedReference SplitMergeMove.sideReference
    rw [lintegral_map _ _ _ functionMeasurable, lintegral_add_measure,
      lintegral_map _ _ _
        (functionMeasurable.comp (sumDistribution space splitAux mergeAux).inverse_measurable),
      lintegral_map _ _ _
        (functionMeasurable.comp (sumDistribution space splitAux mergeAux).inverse_measurable)]
    change ENNReal.add
        (lintegral (Measure.prod state splitReference splitFinite)
          (fun point => function (point.1, Sum.inl point.2)))
        (lintegral (Measure.prod state mergeReference mergeFinite)
          (fun point => function (point.1, Sum.inr point.2))) = _
    rw [lintegral_prod _ _ _ splitMeasurable, lintegral_prod _ _ _ mergeMeasurable]
    all_goals first
      | exact MeasurableMap.inl _ _
      | exact MeasurableMap.inr _ _
      | exact (sumDistribution space splitAux mergeAux).inverse_measurable
  rw [sides, lintegral_prod _ _ _ functionMeasurable, ← lintegral_add _ splitInner mergeInner]
  apply lintegral_congr
  intro input
  unfold auxiliaryReference
  rw [lintegral_add_measure,
    lintegral_map _ _ _ (functionMeasurable.comp (Kernel.pair_left_measurable input)),
    lintegral_map _ _ _ (functionMeasurable.comp (Kernel.pair_left_measurable input))]

/-- A Markov selection of a side and its auxiliary, with a density against the
auxiliary reference. -/
public structure SplitMergeSelection (space : Space X) (splitAux : Space A)
    (mergeAux : Space B) (splitReference : Measure splitAux)
    (mergeReference : Measure mergeAux) where
  kernel : Kernel space (Space.sum splitAux mergeAux)
  finite : Kernel.IsSFinite kernel
  markov : ∀ input, Measure.IsProbability (kernel input)
  density : X × Sum A B → Carrier
  measurable :
    MeasurableMap (Space.product space (Space.sum splitAux mergeAux)) borel density
  nonnegative : ∀ point, Dedekind.le Dedekind.zero (density point)
  represents : ∀ input, kernel input =
    (auxiliaryReference splitReference mergeReference).withDensity
      (fun value => ENNReal.ofReal (density (input, value)))

/-- The extended mass: the whole-state density times the selection density. -/
@[expose] noncomputable def splitMergeMass (stateDensity : X → Carrier)
    (selectionDensity : X × Sum A B → Carrier) (point : X × Sum A B) : Carrier :=
  Dedekind.mul (stateDensity point.1) (selectionDensity point)

theorem splitMergeMass_measurable {stateDensity : X → Carrier}
    {selectionDensity : X × Sum A B → Carrier}
    (stateDensityMeasurable : MeasurableMap space borel stateDensity)
    (selectionDensityMeasurable :
      MeasurableMap (Space.product space (Space.sum splitAux mergeAux)) borel selectionDensity) :
    MeasurableMap (Space.product space (Space.sum splitAux mergeAux)) borel
      (splitMergeMass stateDensity selectionDensity) :=
  measurable_mul (MeasurableMap.comp stateDensityMeasurable (Space.first_measurable _ _))
    selectionDensityMeasurable

/-- Draw a side and its auxiliary, propose through the move's involution, and
accept by the strict test on Green's density. -/
@[expose] noncomputable def splitMergeKernel
    (selection : Kernel space (Space.sum splitAux mergeAux))
    (selectionFinite : Kernel.IsSFinite selection)
    (move : SplitMergeMove space splitAux mergeAux)
    (stateDensity : X → Carrier) (selectionDensity : X × Sum A B → Carrier)
    (factor : X × B → Carrier)
    (stateDensityMeasurable : MeasurableMap space borel stateDensity)
    (selectionDensityMeasurable :
      MeasurableMap (Space.product space (Space.sum splitAux mergeAux)) borel selectionDensity)
    (factorMeasurable : MeasurableMap (Space.product space mergeAux) borel factor) :
    Kernel space space :=
  involutiveKernel selection selectionFinite move.involution move.involution_measurable
    (involutiveAccept move.involution
      (greenDensity (move.jacobian factor) (splitMergeMass stateDensity selectionDensity)))
    (involutiveAccept_measurable move.involution move.involution_measurable
      (greenDensity_measurable (move.jacobian_measurable factorMeasurable)
        (splitMergeMass_measurable stateDensityMeasurable selectionDensityMeasurable)))

section Statements

variable {selection : Kernel space (Space.sum splitAux mergeAux)}
  {selectionFinite : Kernel.IsSFinite selection}
  {move : SplitMergeMove space splitAux mergeAux}
  {stateDensity : X → Carrier} {selectionDensity : X × Sum A B → Carrier}
  {factor : X × B → Carrier}
  {stateDensityMeasurable : MeasurableMap space borel stateDensity}
  {selectionDensityMeasurable :
    MeasurableMap (Space.product space (Space.sum splitAux mergeAux)) borel selectionDensity}
  {factorMeasurable : MeasurableMap (Space.product space mergeAux) borel factor}

/-- The split/merge kernel leaves invariant every target with a density
against the state reference, for a selection with densities against the
auxiliary reference and a pairing that changes reference by a positive factor. -/
theorem splitMergeKernel_invariant
    {state : Measure space}
    {splitReference : Measure splitAux} (splitFinite : Measure.SFinite splitReference)
    {mergeReference : Measure mergeAux} (mergeFinite : Measure.SFinite mergeReference)
    (target : Measure space)
    (targetDensity : target = state.withDensity (fun input => ENNReal.ofReal (stateDensity input)))
    (stateNonnegative : ∀ input, Dedekind.le Dedekind.zero (stateDensity input))
    (selectionMarkov : ∀ input, Measure.IsProbability (selection input))
    (selectionRepresents : ∀ input, selection input =
      (auxiliaryReference splitReference mergeReference).withDensity
        (fun value => ENNReal.ofReal (selectionDensity (input, value))))
    (selectionNonnegative : ∀ point, Dedekind.le Dedekind.zero (selectionDensity point))
    (change : move.pairing.ReferenceChange (Measure.prod state splitReference splitFinite)
      (Measure.prod state mergeReference mergeFinite) factor)
    (factorPositive : ∀ point, move.pairing.targetDomain point →
      Dedekind.lt Dedekind.zero (factor point)) :
    KernelInvariant target
      (splitMergeKernel selection selectionFinite move stateDensity selectionDensity factor
        stateDensityMeasurable selectionDensityMeasurable factorMeasurable) := by
  let reference := SplitMergeMove.extendedReference
    (Measure.prod state splitReference splitFinite) (Measure.prod state mergeReference mergeFinite)
  have massMeasurable : MeasurableMap (Space.product space (Space.sum splitAux mergeAux)) borel
      (splitMergeMass stateDensity selectionDensity) :=
    splitMergeMass_measurable stateDensityMeasurable selectionDensityMeasurable
  have massNonnegative : ∀ point, Dedekind.le Dedekind.zero
      (splitMergeMass stateDensity selectionDensity point) := fun point =>
    Dedekind.mul_nonnegative (stateNonnegative point.1) (selectionNonnegative point)
  have stateWeight : ENNRealMeasurable space
      (fun input => ENNReal.ofReal (stateDensity input)) :=
    ENNRealMeasurable.comp (map := ENNReal.ofReal) ofReal_measurable stateDensityMeasurable
  have selectionWeight : ENNRealMeasurable (Space.product space (Space.sum splitAux mergeAux))
      (fun point => ENNReal.ofReal (selectionDensity point)) :=
    ENNRealMeasurable.comp (map := ENNReal.ofReal) ofReal_measurable selectionDensityMeasurable
  have joint : target.semiproduct selection selectionFinite =
      reference.withDensity
        (fun point => ENNReal.ofReal (splitMergeMass stateDensity selectionDensity point)) := by
    rw [targetDensity, Measure.semiproduct_withDensity_prod state stateWeight
      (auxiliaryReference splitReference mergeReference)
      (auxiliaryReferenceFinite splitFinite mergeFinite) selection selectionFinite
      selectionWeight selectionRepresents]
    change _ = (SplitMergeMove.extendedReference
      (Measure.prod state splitReference splitFinite)
      (Measure.prod state mergeReference mergeFinite)).withDensity _
    rw [extendedReference_prod state splitFinite mergeFinite]
    refine congrArg _ (funext fun point => ?_)
    unfold splitMergeMass
    rw [ofReal_mul (stateNonnegative point.1) (selectionNonnegative point), ENNReal.mul_comm]
  have represents := joint.trans (greenDensity_represents reference move.involution_measurable
    (move.jacobian_measurable factorMeasurable) massMeasurable
    (fun point => Dedekind.le_of_lt (move.jacobian_positive factorPositive point))
    massNonnegative (move.involution_reference_change factorMeasurable change factorPositive))
  exact involutive_invariant_of_reference target selection selectionFinite selectionMarkov
    move.involution move.involution_measurable move.involution_involutive _
    (symmetrized_map_involution reference move.involution move.involution_measurable
      move.involution_involutive)
    (greenDensity_measurable (move.jacobian_measurable factorMeasurable) massMeasurable)
    represents

/-- The acceptance compares the extended mass at a point with the Jacobian
times the extended mass at its image: the whole-state target ratio, the
reverse over the forward selection, and the Jacobian. -/
theorem splitMergeKernel_accept
    (factorPositive : ∀ point, move.pairing.targetDomain point →
      Dedekind.lt Dedekind.zero (factor point))
    (point : X × Sum A B) :
    involutiveAccept move.involution
        (greenDensity (move.jacobian factor) (splitMergeMass stateDensity selectionDensity))
        point =
      metropolisAccept (fun weight : Carrier => weight)
        (splitMergeMass stateDensity selectionDensity point,
          Dedekind.mul (move.jacobian factor point)
            (splitMergeMass stateDensity selectionDensity (move.involution point))) :=
  involutiveAccept_greenDensity point
    (Dedekind.le_of_lt (move.jacobian_positive factorPositive point))
    (move.jacobian_reciprocal factorPositive point)

/-- From a state of positive target density, the kernel puts no mass on
states of zero target density. -/
theorem splitMergeKernel_stays_in_support
    (stateNonnegative : ∀ input, Dedekind.le Dedekind.zero (stateDensity input))
    (selectionNonnegative : ∀ point, Dedekind.le Dedekind.zero (selectionDensity point))
    (factorPositive : ∀ point, move.pairing.targetDomain point →
      Dedekind.lt Dedekind.zero (factor point))
    {input : X} (positive : Dedekind.lt Dedekind.zero (stateDensity input)) :
    splitMergeKernel selection selectionFinite move stateDensity selectionDensity factor
        stateDensityMeasurable selectionDensityMeasurable factorMeasurable input
        (fun output => stateDensity output = Dedekind.zero) = ENNReal.zero := by
  have regionMeasurable : space.Measurable (fun output => stateDensity output = Dedekind.zero) :=
    measurable_eq stateDensityMeasurable (MeasurableMap.constant _ borel Dedekind.zero)
  have indicatorMeasurable : ENNRealMeasurable space
      (ennrealIndicator (fun output => stateDensity output = Dedekind.zero)
        fun _ => ENNReal.one) :=
    ENNRealMeasurable.indicator regionMeasurable (ENNRealMeasurable.constant _ _)
  rw [apply_eq_lintegral_indicator _ regionMeasurable]
  unfold splitMergeKernel
  rw [lintegral_involutiveKernel _ _ _ _ _ _ input indicatorMeasurable]
  have outside : ¬ stateDensity input = Dedekind.zero := fun vanished =>
    Dedekind.lt_irrefl _ (vanished ▸ positive)
  refine (lintegral_congr _ fun drawn => ?_).trans (lintegral_zero _)
  have stay : ennrealIndicator (fun output => stateDensity output = Dedekind.zero)
      (fun _ => ENNReal.one) input = ENNReal.zero := by
    unfold ennrealIndicator ennrealPiecewise
    rw [ite_eq_right outside]
  rw [stay, ENNReal.mul_zero]
  by_cases landed : stateDensity (move.involution (input, drawn)).1 = Dedekind.zero
  · have rejected : involutiveAccept move.involution
        (greenDensity (move.jacobian factor) (splitMergeMass stateDensity selectionDensity))
        (input, drawn) = ENNReal.zero := by
      rw [splitMergeKernel_accept factorPositive]
      apply metropolisAccept_eq_zero
      · exact Dedekind.mul_nonnegative (stateNonnegative input)
          (selectionNonnegative (input, drawn))
      · change Dedekind.le (Dedekind.mul (move.jacobian factor (input, drawn))
          (Dedekind.mul (stateDensity (move.involution (input, drawn)).1)
            (selectionDensity (move.involution (input, drawn))))) Dedekind.zero
        rw [landed, Dedekind.zero_mul, Dedekind.mul_zero]
        exact Dedekind.le_refl _
    rw [rejected, ENNReal.zero_mul, ENNReal.add_zero]
  · have missed : ennrealIndicator (fun output => stateDensity output = Dedekind.zero)
        (fun _ => ENNReal.one) (move.involution (input, drawn)).1 = ENNReal.zero := by
      unfold ennrealIndicator ennrealPiecewise
      rw [ite_eq_right landed]
    rw [missed, ENNReal.mul_zero, ENNReal.add_zero]

end Statements

end
end Problib.Inference
