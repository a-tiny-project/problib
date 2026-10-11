module

public import Problib.Measure.Equivalence.Partial
public import Problib.Measure.Space.SumProduct
public import Problib.Measure.Real.Arithmetic

set_option autoImplicit false

/-!
# Split/merge moves

Green's dimension matching pairs split-side extended states `(x, a)` with
merge-side states `(x', b)` through a measurable partial equivalence. The
involution acts on a state with an auxiliary from `A ⊕ B`. A split-side
point in the pairing's domain goes to the merge side by the pairing, a
merge-side point in its range comes back by the inverse, and every other point
is fixed. The merge side keeps what the split consumed, so the map is an
involution by construction.

The involution changes the extended reference by a density, its Jacobian. On
the merge side in the range, the Jacobian is the pairing's reference-change
factor. On the split side in the domain, it is the reciprocal factor read at
the forward image. Elsewhere it is one. The Jacobian at a point and at its
image multiply to one.

The measure algebra runs on the distributed sides `(X × A) ⊕ (X × B)`, where
each summand carries one of the pairing's two references, and transports to
`X × (A ⊕ B)` by `sumDistribution`.
-/

namespace Problib.Inference

open Problib.Real Problib.Measure
open Problib.Real.Construction
open Problib.Measure.Real (Carrier borel ofReal_measurable ofReal_mul_ofReal_inverse
  inverse_measurable measurable_piecewise)
open Classical

public section

universe u v w

variable {X : Type u} {A : Type v} {B : Type w}
  {space : Space X} {splitAux : Space A} {mergeAux : Space B}

/-- Distribute a state over the two sides of its auxiliary. -/
@[expose] public def sumDistribution (space : Space X) (splitAux : Space A)
    (mergeAux : Space B) :
    MeasurableEquivalence (Space.product space (Space.sum splitAux mergeAux))
      (Space.sum (Space.product space splitAux) (Space.product space mergeAux)) where
  forward := fun point =>
    Sum.elim (fun split => Sum.inl (point.1, split))
      (fun merge => Sum.inr (point.1, merge)) point.2
  inverse := Sum.elim (fun point => (point.1, Sum.inl point.2))
    (fun point => (point.1, Sum.inr point.2))
  inverse_forward := by
    rintro ⟨state, split | merge⟩ <;> rfl
  forward_inverse := by
    rintro (⟨state, split⟩ | ⟨state, merge⟩) <;> rfl
  forward_measurable := by
    have swapped : MeasurableMap (Space.product space (Space.sum splitAux mergeAux))
        (Space.product (Space.sum splitAux mergeAux) space)
        (fun point => (point.2, point.1)) :=
      Space.swap_measurable space (Space.sum splitAux mergeAux)
    have distributed : MeasurableMap (Space.product (Space.sum splitAux mergeAux) space)
        (Space.sum (Space.product splitAux space) (Space.product mergeAux space))
        (fun input => Sum.elim (fun value => Sum.inl (value, input.2))
          (fun value => Sum.inr (value, input.2)) input.1) :=
      Space.distribute_sum_measurable splitAux mergeAux space
    have regrouped : MeasurableMap
        (Space.sum (Space.product splitAux space) (Space.product mergeAux space))
        (Space.sum (Space.product space splitAux) (Space.product space mergeAux))
        (Sum.elim (fun pair : A × X => Sum.inl (pair.2, pair.1))
          (fun pair : B × X => Sum.inr (pair.2, pair.1))) :=
      MeasurableMap.sum_elim
        (MeasurableMap.comp (MeasurableMap.inl _ _) (Space.swap_measurable _ _))
        (MeasurableMap.comp (MeasurableMap.inr _ _) (Space.swap_measurable _ _))
    have composite : MeasurableMap (Space.product space (Space.sum splitAux mergeAux))
        (Space.sum (Space.product space splitAux) (Space.product space mergeAux))
        (fun point : X × Sum A B =>
          Sum.elim (fun pair : A × X => Sum.inl (pair.2, pair.1))
            (fun pair : B × X => Sum.inr (pair.2, pair.1))
            (Sum.elim (fun value => Sum.inl (value, (point.2, point.1).2))
              (fun value => Sum.inr (value, (point.2, point.1).2)) (point.2, point.1).1)) :=
      MeasurableMap.comp regrouped (MeasurableMap.comp distributed swapped)
    have equal : (fun point : X × Sum A B =>
        Sum.elim (fun split => (Sum.inl (point.1, split) : Sum (X × A) (X × B)))
          (fun merge => Sum.inr (point.1, merge)) point.2) =
        (fun point : X × Sum A B =>
          Sum.elim (fun pair : A × X => Sum.inl (pair.2, pair.1))
            (fun pair : B × X => Sum.inr (pair.2, pair.1))
            (Sum.elim (fun value => Sum.inl (value, (point.2, point.1).2))
              (fun value => Sum.inr (value, (point.2, point.1).2)) (point.2, point.1).1)) := by
      funext point
      rcases point with ⟨state, split | merge⟩ <;> rfl
    rw [equal]
    exact @composite
  inverse_measurable := MeasurableMap.sum_elim
    (Space.pair_measurable (Space.first_measurable _ _)
      (MeasurableMap.comp (MeasurableMap.inl _ _) (Space.second_measurable _ _)))
    (Space.pair_measurable (Space.first_measurable _ _)
      (MeasurableMap.comp (MeasurableMap.inr _ _) (Space.second_measurable _ _)))

private theorem ite_measurable {α : Type u} {β : Type v}
    {source : Space α} {target : Space β} {region : Set α}
    (regionMeasurable : source.Measurable region) {first second : α → β}
    (firstMeasurable : MeasurableMap source target first)
    (secondMeasurable : MeasurableMap source target second) :
    MeasurableMap source target
      (fun value => if region value then first value else second value) := by
  intro set setMeasurable
  have equal : Set.preimage
      (fun value => if region value then first value else second value) set =
      Set.union (Set.inter region (Set.preimage first set))
        (Set.inter (Set.complement region) (Set.preimage second set)) := by
    apply Set.ext
    intro value
    by_cases member : region value <;>
      simp [Set.preimage, Set.union, Set.inter, Set.complement, member]
  rw [equal]
  exact source.union (source.inter regionMeasurable (firstMeasurable setMeasurable))
    (source.inter (source.complement regionMeasurable) (secondMeasurable setMeasurable))

private theorem withDensity_add_measure {α : Type u} {source : Space α}
    (left right : Measure source) (density : α → ENNReal) :
    (Measure.add left right).withDensity density =
      Measure.add (left.withDensity density) (right.withDensity density) := by
  apply Measure.ext
  intro set setMeasurable
  rw [Measure.withDensity_apply _ _ setMeasurable,
    Measure.add_apply_measurable _ _ setMeasurable,
    Measure.withDensity_apply _ _ setMeasurable,
    Measure.withDensity_apply _ _ setMeasurable,
    Measure.restrict_add _ _ setMeasurable, lintegral_add_measure]

private theorem map_split {α : Type u} {β : Type v} {source : Space α}
    {target : Space β} (measure : Measure source) {region : Set α}
    (regionMeasurable : source.Measurable region) (function : α → β)
    (functionMeasurable : MeasurableMap source target function) :
    measure.map function functionMeasurable =
      Measure.add ((measure.restrict region).map function functionMeasurable)
        ((measure.restrict (Set.complement region)).map function
          functionMeasurable) := by
  rw [← Measure.map_add, Measure.restrict_add_complement measure regionMeasurable]

private theorem withDensity_split {α : Type u} {source : Space α}
    (measure : Measure source) {region : Set α}
    (regionMeasurable : source.Measurable region) (density : α → ENNReal) :
    measure.withDensity density =
      Measure.add ((measure.restrict region).withDensity density)
        ((measure.restrict (Set.complement region)).withDensity density) := by
  rw [← withDensity_add_measure,
    Measure.restrict_add_complement measure regionMeasurable]

private theorem add_exchange {α : Type u} {source : Space α}
    (first second third fourth : Measure source) :
    Measure.add (Measure.add first second) (Measure.add third fourth) =
      Measure.add (Measure.add third second) (Measure.add first fourth) := by
  rw [Measure.add_comm first second, Measure.add_assoc, ← Measure.add_assoc first third fourth,
    Measure.add_comm first third, Measure.add_assoc third first fourth,
    ← Measure.add_assoc second third, Measure.add_comm second third]

/-- Green's dimension matching: split-side extended states paired with
merge-side ones. -/
public structure SplitMergeMove (space : Space X) (splitAux : Space A)
    (mergeAux : Space B) where
  pairing : MeasurablePartialEquivalence (Space.product space splitAux)
    (Space.product space mergeAux)

namespace SplitMergeMove

variable (move : SplitMergeMove space splitAux mergeAux)

/-- The involution on the distributed sides. A split-side point in the
pairing's domain crosses by the pairing, a merge-side point in its range
crosses back by the inverse, and every other point stays. -/
@[expose] public noncomputable def sideInvolution :
    Sum (X × A) (X × B) → Sum (X × A) (X × B) :=
  Sum.elim
    (fun point => if move.pairing.sourceDomain point then
      Sum.inr (move.pairing.forward point) else Sum.inl point)
    (fun point => if move.pairing.targetDomain point then
      Sum.inl (move.pairing.inverse point) else Sum.inr point)

/-- The split side goes to the merge side by the pairing and comes back by its
inverse. Points outside both domains are fixed. -/
@[expose] public noncomputable def involution (point : X × Sum A B) :
    X × Sum A B :=
  (sumDistribution space splitAux mergeAux).inverse
    (move.sideInvolution ((sumDistribution space splitAux mergeAux).forward point))

public theorem sideInvolution_involutive (point : Sum (X × A) (X × B)) :
    move.sideInvolution (move.sideInvolution point) = point := by
  rcases point with point | point
  · by_cases member : move.pairing.sourceDomain point
    · have crossed := move.pairing.forward_mem point member
      simp only [sideInvolution, Sum.elim_inl, Sum.elim_inr, ite_eq_left member,
        ite_eq_left crossed, move.pairing.inverse_forward point member]
    · simp only [sideInvolution, Sum.elim_inl, ite_eq_right member]
  · by_cases member : move.pairing.targetDomain point
    · have crossed := move.pairing.inverse_mem point member
      simp only [sideInvolution, Sum.elim_inl, Sum.elim_inr, ite_eq_left member,
        ite_eq_left crossed, move.pairing.forward_inverse point member]
    · simp only [sideInvolution, Sum.elim_inr, ite_eq_right member]

public theorem involution_involutive (point : X × Sum A B) :
    move.involution (move.involution point) = point := by
  unfold involution
  rw [(sumDistribution space splitAux mergeAux).forward_inverse,
    move.sideInvolution_involutive,
    (sumDistribution space splitAux mergeAux).inverse_forward]

public theorem sideInvolution_measurable :
    MeasurableMap (Space.sum (Space.product space splitAux) (Space.product space mergeAux))
      (Space.sum (Space.product space splitAux) (Space.product space mergeAux))
      move.sideInvolution :=
  MeasurableMap.sum_elim
    (ite_measurable move.pairing.sourceMeasurable
      (MeasurableMap.comp (MeasurableMap.inr _ _) move.pairing.forwardMeasurable)
      (MeasurableMap.inl _ _))
    (ite_measurable move.pairing.targetMeasurable
      (MeasurableMap.comp (MeasurableMap.inl _ _) move.pairing.inverseMeasurable)
      (MeasurableMap.inr _ _))

public theorem involution_measurable :
    MeasurableMap (Space.product space (Space.sum splitAux mergeAux))
      (Space.product space (Space.sum splitAux mergeAux)) move.involution :=
  MeasurableMap.comp (sumDistribution space splitAux mergeAux).inverse_measurable
    (MeasurableMap.comp move.sideInvolution_measurable
      (sumDistribution space splitAux mergeAux).forward_measurable)

/-- The split side and the merge side, each on its own summand. -/
@[expose] public noncomputable def sideReference
    (splitSide : Measure (Space.product space splitAux))
    (mergeSide : Measure (Space.product space mergeAux)) :
    Measure (Space.sum (Space.product space splitAux) (Space.product space mergeAux)) :=
  Measure.add (splitSide.map Sum.inl (MeasurableMap.inl _ _))
    (mergeSide.map Sum.inr (MeasurableMap.inr _ _))

/-- The extended reference: the split-side reference on split auxiliaries and
the merge-side reference on merge auxiliaries. -/
@[expose] public noncomputable def extendedReference
    (splitSide : Measure (Space.product space splitAux))
    (mergeSide : Measure (Space.product space mergeAux)) :
    Measure (Space.product space (Space.sum splitAux mergeAux)) :=
  (sideReference splitSide mergeSide).map
    (sumDistribution space splitAux mergeAux).inverse
    (sumDistribution space splitAux mergeAux).inverse_measurable

/-- The Jacobian on the distributed sides. -/
@[expose] public noncomputable def sideJacobian (factor : X × B → Carrier) :
    Sum (X × A) (X × B) → Carrier :=
  Sum.elim
    (fun point => if move.pairing.sourceDomain point then
      Dedekind.inverse (factor (move.pairing.forward point)) else Dedekind.one)
    (fun point => if move.pairing.targetDomain point then factor point
      else Dedekind.one)

/-- Merge side in the range: the factor. Split side in the domain: its
reciprocal at the forward image. Elsewhere: one. -/
@[expose] public noncomputable def jacobian (factor : X × B → Carrier)
    (point : X × Sum A B) : Carrier :=
  move.sideJacobian factor ((sumDistribution space splitAux mergeAux).forward point)

public theorem sideJacobian_measurable {factor : X × B → Carrier}
    (factorMeasurable : MeasurableMap (Space.product space mergeAux) borel factor) :
    MeasurableMap (Space.sum (Space.product space splitAux) (Space.product space mergeAux))
      borel (move.sideJacobian factor) :=
  MeasurableMap.sum_elim
    (measurable_piecewise move.pairing.sourceMeasurable
      (MeasurableMap.comp inverse_measurable
        (MeasurableMap.comp factorMeasurable move.pairing.forwardMeasurable))
      (MeasurableMap.constant _ _ _))
    (measurable_piecewise move.pairing.targetMeasurable factorMeasurable
      (MeasurableMap.constant _ _ _))

public theorem jacobian_measurable {factor : X × B → Carrier}
    (factorMeasurable : MeasurableMap (Space.product space mergeAux) borel factor) :
    MeasurableMap (Space.product space (Space.sum splitAux mergeAux)) borel
      (move.jacobian factor) :=
  MeasurableMap.comp (move.sideJacobian_measurable factorMeasurable)
    (sumDistribution space splitAux mergeAux).forward_measurable

public theorem sideJacobian_reciprocal {factor : X × B → Carrier}
    (positive : ∀ point, move.pairing.targetDomain point →
      Dedekind.lt Dedekind.zero (factor point))
    (point : Sum (X × A) (X × B)) :
    Dedekind.mul (move.sideJacobian factor (move.sideInvolution point))
      (move.sideJacobian factor point) = Dedekind.one := by
  rcases point with point | point
  · by_cases member : move.pairing.sourceDomain point
    · have crossed := move.pairing.forward_mem point member
      simp only [sideInvolution, sideJacobian, Sum.elim_inl, Sum.elim_inr,
        ite_eq_left member, ite_eq_left crossed]
      exact Dedekind.mul_inverse_cancel_of_positive (positive _ crossed)
    · simp only [sideInvolution, sideJacobian, Sum.elim_inl, ite_eq_right member]
      exact Dedekind.mul_one _
  · by_cases member : move.pairing.targetDomain point
    · have crossed := move.pairing.inverse_mem point member
      simp only [sideInvolution, sideJacobian, Sum.elim_inl, Sum.elim_inr,
        ite_eq_left member, ite_eq_left crossed, move.pairing.forward_inverse point member]
      rw [Dedekind.mul_comm]
      exact Dedekind.mul_inverse_cancel_of_positive (positive _ member)
    · simp only [sideInvolution, sideJacobian, Sum.elim_inr, ite_eq_right member]
      exact Dedekind.mul_one _

/-- The Jacobian is positive when the factor is positive on the pairing's
range. -/
public theorem jacobian_positive {factor : X × B → Carrier}
    (positive : ∀ point, move.pairing.targetDomain point →
      Dedekind.lt Dedekind.zero (factor point))
    (point : X × Sum A B) :
    Dedekind.lt Dedekind.zero (move.jacobian factor point) := by
  unfold jacobian
  rcases (sumDistribution space splitAux mergeAux).forward point with side | side
  · by_cases member : move.pairing.sourceDomain side
    · simp only [sideJacobian, Sum.elim_inl, ite_eq_left member]
      exact Dedekind.inverse_of_positive_positive
        (positive _ (move.pairing.forward_mem side member))
    · simp only [sideJacobian, Sum.elim_inl, ite_eq_right member]
      exact Dedekind.one_positive
  · by_cases member : move.pairing.targetDomain side
    · simp only [sideJacobian, Sum.elim_inr, ite_eq_left member]
      exact positive side member
    · simp only [sideJacobian, Sum.elim_inr, ite_eq_right member]
      exact Dedekind.one_positive

/-- The Jacobian at a point and at its image are reciprocal. -/
public theorem jacobian_reciprocal {factor : X × B → Carrier}
    (positive : ∀ point, move.pairing.targetDomain point →
      Dedekind.lt Dedekind.zero (factor point))
    (point : X × Sum A B) :
    Dedekind.mul (move.jacobian factor (move.involution point))
      (move.jacobian factor point) = Dedekind.one := by
  unfold jacobian involution
  rw [(sumDistribution space splitAux mergeAux).forward_inverse]
  exact move.sideJacobian_reciprocal positive _

/-- The involution changes the distributed reference by the side Jacobian. -/
public theorem sideInvolution_reference_change
    {splitSide : Measure (Space.product space splitAux)}
    {mergeSide : Measure (Space.product space mergeAux)}
    {factor : X × B → Carrier}
    (factorMeasurable : MeasurableMap (Space.product space mergeAux) borel factor)
    (change : move.pairing.ReferenceChange splitSide mergeSide factor)
    (positive : ∀ point, move.pairing.targetDomain point →
      Dedekind.lt Dedekind.zero (factor point)) :
    (sideReference splitSide mergeSide).map move.sideInvolution
        move.sideInvolution_measurable =
      (sideReference splitSide mergeSide).withDensity
        (fun point => ENNReal.ofReal (move.sideJacobian factor point)) := by
  have returned := MeasurablePartialEquivalence.reference_change_symm
    factorMeasurable change positive
  unfold MeasurablePartialEquivalence.ReferenceChange at change returned
  change (mergeSide.restrict move.pairing.targetDomain).map move.pairing.inverse
      move.pairing.inverseMeasurable =
    (splitSide.restrict move.pairing.sourceDomain).withDensity
      (fun point => ENNReal.ofReal
        (Dedekind.inverse (factor (move.pairing.forward point)))) at returned
  let sides := Space.sum (Space.product space splitAux) (Space.product space mergeAux)
  have jacobianWeight : ENNRealMeasurable sides
      (fun point => ENNReal.ofReal (move.sideJacobian factor point)) :=
    ENNRealMeasurable.comp (map := ENNReal.ofReal) ofReal_measurable
      (move.sideJacobian_measurable factorMeasurable)
  have splitWeight : ENNRealMeasurable (Space.product space splitAux)
      (fun point => ENNReal.ofReal (move.sideJacobian factor (Sum.inl point))) :=
    ENNRealMeasurable.comp
      (map := fun point => ENNReal.ofReal (move.sideJacobian factor point))
      jacobianWeight (MeasurableMap.inl _ _)
  have mergeWeight : ENNRealMeasurable (Space.product space mergeAux)
      (fun point => ENNReal.ofReal (move.sideJacobian factor (Sum.inr point))) :=
    ENNRealMeasurable.comp
      (map := fun point => ENNReal.ofReal (move.sideJacobian factor point))
      jacobianWeight (MeasurableMap.inr _ _)
  have splitStep : MeasurableMap (Space.product space splitAux) sides
      (fun point => move.sideInvolution (Sum.inl point)) :=
    MeasurableMap.comp move.sideInvolution_measurable (MeasurableMap.inl _ _)
  have mergeStep : MeasurableMap (Space.product space mergeAux) sides
      (fun point => move.sideInvolution (Sum.inr point)) :=
    MeasurableMap.comp move.sideInvolution_measurable (MeasurableMap.inr _ _)
  have crossing : MeasurableMap (Space.product space splitAux) sides
      (fun point => Sum.inr (move.pairing.forward point)) :=
    MeasurableMap.comp (MeasurableMap.inr _ _) move.pairing.forwardMeasurable
  have returning : MeasurableMap (Space.product space mergeAux) sides
      (fun point => Sum.inl (move.pairing.inverse point)) :=
    MeasurableMap.comp (MeasurableMap.inl _ _) move.pairing.inverseMeasurable
  -- Left side: push each summand through the involution, one domain at a time.
  have splitCrossed :
      (splitSide.restrict move.pairing.sourceDomain).map
          (fun point => move.sideInvolution (Sum.inl point)) splitStep =
        ((mergeSide.restrict move.pairing.targetDomain).withDensity
          (fun point => ENNReal.ofReal (factor point))).map Sum.inr
          (MeasurableMap.inr _ _) := by
    rw [Measure.map_congr_on _
        (Measure.ae_restrict_mem splitSide move.pairing.sourceMeasurable)
        splitStep crossing
        (fun point member => by
          simp only [sideInvolution, Sum.elim_inl, ite_eq_left member]),
      ← Measure.map_comp _ move.pairing.forward Sum.inr
        move.pairing.forwardMeasurable (MeasurableMap.inr _ _), change]
  have splitStays :
      (splitSide.restrict (Set.complement move.pairing.sourceDomain)).map
          (fun point => move.sideInvolution (Sum.inl point)) splitStep =
        (splitSide.restrict (Set.complement move.pairing.sourceDomain)).map
          Sum.inl (MeasurableMap.inl _ _) :=
    Measure.map_congr_on _
      (Measure.ae_restrict_mem splitSide
        ((Space.product space splitAux).complement move.pairing.sourceMeasurable))
      splitStep (MeasurableMap.inl _ _)
      (fun point member => by
        simp only [sideInvolution, Sum.elim_inl, ite_eq_right member])
  have mergeCrossed :
      (mergeSide.restrict move.pairing.targetDomain).map
          (fun point => move.sideInvolution (Sum.inr point)) mergeStep =
        ((splitSide.restrict move.pairing.sourceDomain).withDensity
          (fun point => ENNReal.ofReal
            (Dedekind.inverse (factor (move.pairing.forward point))))).map Sum.inl
          (MeasurableMap.inl _ _) := by
    rw [Measure.map_congr_on _
        (Measure.ae_restrict_mem mergeSide move.pairing.targetMeasurable)
        mergeStep returning
        (fun point member => by
          simp only [sideInvolution, Sum.elim_inr, ite_eq_left member]),
      ← Measure.map_comp _ move.pairing.inverse Sum.inl
        move.pairing.inverseMeasurable (MeasurableMap.inl _ _), returned]
  have mergeStays :
      (mergeSide.restrict (Set.complement move.pairing.targetDomain)).map
          (fun point => move.sideInvolution (Sum.inr point)) mergeStep =
        (mergeSide.restrict (Set.complement move.pairing.targetDomain)).map
          Sum.inr (MeasurableMap.inr _ _) :=
    Measure.map_congr_on _
      (Measure.ae_restrict_mem mergeSide
        ((Space.product space mergeAux).complement move.pairing.targetMeasurable))
      mergeStep (MeasurableMap.inr _ _)
      (fun point member => by
        simp only [sideInvolution, Sum.elim_inr, ite_eq_right member])
  -- Right side: split each summand's density along the same domains.
  have splitInside :
      (splitSide.restrict move.pairing.sourceDomain).withDensity
          (fun point => ENNReal.ofReal (move.sideJacobian factor (Sum.inl point))) =
        (splitSide.restrict move.pairing.sourceDomain).withDensity
          (fun point => ENNReal.ofReal
            (Dedekind.inverse (factor (move.pairing.forward point)))) := by
    apply Measure.withDensity_congr_ae
    apply (Measure.ae_restrict_mem splitSide move.pairing.sourceMeasurable).mono
    intro point member
    simp only [sideJacobian, Sum.elim_inl, ite_eq_left member]
  have splitOutside :
      (splitSide.restrict (Set.complement move.pairing.sourceDomain)).withDensity
          (fun point => ENNReal.ofReal (move.sideJacobian factor (Sum.inl point))) =
        splitSide.restrict (Set.complement move.pairing.sourceDomain) := by
    have unit : (splitSide.restrict (Set.complement move.pairing.sourceDomain)).withDensity
        (fun point => ENNReal.ofReal (move.sideJacobian factor (Sum.inl point))) =
        (splitSide.restrict (Set.complement move.pairing.sourceDomain)).withDensity
          (fun _ => ENNReal.one) := by
      apply Measure.withDensity_congr_ae
      apply (Measure.ae_restrict_mem splitSide
        ((Space.product space splitAux).complement move.pairing.sourceMeasurable)).mono
      intro point member
      simp only [sideJacobian, Sum.elim_inl, ite_eq_right member]
      exact ENNReal.ofReal_one
    rw [unit, Measure.withDensity_one]
  have mergeInside :
      (mergeSide.restrict move.pairing.targetDomain).withDensity
          (fun point => ENNReal.ofReal (move.sideJacobian factor (Sum.inr point))) =
        (mergeSide.restrict move.pairing.targetDomain).withDensity
          (fun point => ENNReal.ofReal (factor point)) := by
    apply Measure.withDensity_congr_ae
    apply (Measure.ae_restrict_mem mergeSide move.pairing.targetMeasurable).mono
    intro point member
    simp only [sideJacobian, Sum.elim_inr, ite_eq_left member]
  have mergeOutside :
      (mergeSide.restrict (Set.complement move.pairing.targetDomain)).withDensity
          (fun point => ENNReal.ofReal (move.sideJacobian factor (Sum.inr point))) =
        mergeSide.restrict (Set.complement move.pairing.targetDomain) := by
    have unit : (mergeSide.restrict (Set.complement move.pairing.targetDomain)).withDensity
        (fun point => ENNReal.ofReal (move.sideJacobian factor (Sum.inr point))) =
        (mergeSide.restrict (Set.complement move.pairing.targetDomain)).withDensity
          (fun _ => ENNReal.one) := by
      apply Measure.withDensity_congr_ae
      apply (Measure.ae_restrict_mem mergeSide
        ((Space.product space mergeAux).complement move.pairing.targetMeasurable)).mono
      intro point member
      simp only [sideJacobian, Sum.elim_inr, ite_eq_right member]
      exact ENNReal.ofReal_one
    rw [unit, Measure.withDensity_one]
  unfold sideReference
  rw [Measure.map_add,
    Measure.map_comp _ Sum.inl move.sideInvolution (MeasurableMap.inl _ _)
      move.sideInvolution_measurable,
    Measure.map_comp _ Sum.inr move.sideInvolution (MeasurableMap.inr _ _)
      move.sideInvolution_measurable,
    map_split splitSide move.pairing.sourceMeasurable _ splitStep,
    map_split mergeSide move.pairing.targetMeasurable _ mergeStep,
    splitCrossed, splitStays, mergeCrossed, mergeStays,
    withDensity_add_measure,
    ← Measure.map_withDensity splitSide Sum.inl (MeasurableMap.inl _ _) jacobianWeight,
    ← Measure.map_withDensity mergeSide Sum.inr (MeasurableMap.inr _ _) jacobianWeight,
    withDensity_split splitSide move.pairing.sourceMeasurable,
    withDensity_split mergeSide move.pairing.targetMeasurable,
    splitInside, splitOutside, mergeInside, mergeOutside,
    Measure.map_add, Measure.map_add]
  exact add_exchange _ _ _ _

/-- The involution changes the extended reference by the Jacobian. -/
public theorem involution_reference_change
    {splitSide : Measure (Space.product space splitAux)}
    {mergeSide : Measure (Space.product space mergeAux)}
    {factor : X × B → Carrier}
    (factorMeasurable : MeasurableMap (Space.product space mergeAux) borel factor)
    (change : move.pairing.ReferenceChange splitSide mergeSide factor)
    (positive : ∀ point, move.pairing.targetDomain point →
      Dedekind.lt Dedekind.zero (factor point)) :
    (extendedReference splitSide mergeSide).map move.involution
        move.involution_measurable =
      (extendedReference splitSide mergeSide).withDensity
        (fun point => ENNReal.ofReal (move.jacobian factor point)) := by
  let distribution := sumDistribution space splitAux mergeAux
  have jacobianWeight : ENNRealMeasurable
      (Space.product space (Space.sum splitAux mergeAux))
      (fun point => ENNReal.ofReal (move.jacobian factor point)) :=
    ENNRealMeasurable.comp (map := ENNReal.ofReal) ofReal_measurable
      (move.jacobian_measurable factorMeasurable)
  have sideStep : MeasurableMap
      (Space.sum (Space.product space splitAux) (Space.product space mergeAux))
      (Space.product space (Space.sum splitAux mergeAux))
      (fun point => distribution.inverse (move.sideInvolution point)) :=
    MeasurableMap.comp distribution.inverse_measurable move.sideInvolution_measurable
  have throughSides :
      (sideReference splitSide mergeSide).map
          (fun point => move.involution (distribution.inverse point))
          (MeasurableMap.comp move.involution_measurable
            distribution.inverse_measurable) =
        (sideReference splitSide mergeSide).map
          (fun point => distribution.inverse (move.sideInvolution point)) sideStep :=
    Measure.map_congr_function _ _ sideStep (funext fun point => by
      change distribution.inverse (move.sideInvolution
        (distribution.forward (distribution.inverse point))) = _
      rw [distribution.forward_inverse])
  have sameDensity :
      (fun point => ENNReal.ofReal (move.sideJacobian factor point)) =
        (fun point => ENNReal.ofReal (move.jacobian factor (distribution.inverse point))) := by
    funext point
    change _ = ENNReal.ofReal (move.sideJacobian factor
      (distribution.forward (distribution.inverse point)))
    rw [distribution.forward_inverse]
  unfold extendedReference
  rw [Measure.map_comp _ distribution.inverse move.involution distribution.inverse_measurable
      move.involution_measurable, throughSides,
    ← Measure.map_comp _ move.sideInvolution distribution.inverse
      move.sideInvolution_measurable distribution.inverse_measurable,
    move.sideInvolution_reference_change factorMeasurable change positive,
    sameDensity, Measure.map_withDensity _ distribution.inverse
      distribution.inverse_measurable jacobianWeight]

end SplitMergeMove

end
end Problib.Inference
