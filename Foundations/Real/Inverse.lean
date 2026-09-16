module

public import Foundations.Real.Construction.Dedekind.Inverse

set_option autoImplicit false

/-
Copyright (c) 2026 Si-Qi Liu.
Licensed under the MIT License.

Adapted from Tautology/RealBasic/ModuleBackend/Dedekind/Inv.lean at
commit 261012c7540673d59a4015371b7618b7573d43da.

Tiny exposes the sealed selected-carrier reciprocal through explicit
operations and laws rather than typeclass instances.
-/

namespace Foundations.Real.Construction.Dedekind

public theorem ltIrrefl (value : selection.Carrier) : ¬lt value value := by
  intro strict
  exact strict.right strict.left

public theorem negZero : neg zero = zero :=
  Foundations.Algebra.AdditiveCommutativeGroupLaws.negZero
    additive.group

public theorem negNeg (value : selection.Carrier) : neg (neg value) = value :=
  Foundations.Algebra.AdditiveCommutativeGroupLaws.negNeg
    additive.group value

public theorem negPositiveOfNegative {value : selection.Carrier}
    (negative : lt value zero) : lt zero (neg value) := by
  unfold lt at negative ⊢
  constructor
  · rw [← negZero]
    exact negLeNegIff.mpr negative.left
  · intro nonpositive
    have reversed := negLeNegIff.mpr nonpositive
    apply negative.right
    simpa only [negZero, negNeg] using reversed

@[expose] public noncomputable def positiveInverse
    (value : selection.Carrier) (positive : lt zero value) :
    selection.Carrier :=
  Classical.choose (Cut.existsSelectedPositiveInverse value positive)

public theorem positiveInverseNonnegative (value : selection.Carrier)
    (positive : lt zero value) : le zero (positiveInverse value positive) :=
  (Classical.choose_spec
    (Cut.existsSelectedPositiveInverse value positive)).left

public theorem mulPositiveInverse (value : selection.Carrier)
    (positive : lt zero value) :
    mul value (positiveInverse value positive) = one :=
  (Classical.choose_spec
    (Cut.existsSelectedPositiveInverse value positive)).right

@[expose] public noncomputable def inverse
    (value : selection.Carrier) : selection.Carrier := by
  classical
  exact if positive : lt zero value then
    positiveInverse value positive
  else if negative : lt value zero then
    neg (positiveInverse (neg value) (negPositiveOfNegative negative))
  else
    zero

public theorem inverseOfPositive {value : selection.Carrier}
    (positive : lt zero value) :
    inverse value = positiveInverse value positive := by
  classical
  unfold inverse
  simp only [dif_pos positive]

public theorem inverseOfNegative {value : selection.Carrier}
    (negative : lt value zero) :
    inverse value =
      neg (positiveInverse (neg value) (negPositiveOfNegative negative)) := by
  classical
  unfold inverse
  have notPositive : ¬lt zero value := by
    intro positive
    exact negative.right positive.left
  simp only [dif_neg notPositive, dif_pos negative]

public theorem inverseOfNotPositiveOfNotNegative
    {value : selection.Carrier}
    (notPositive : ¬lt zero value) (notNegative : ¬lt value zero) :
    inverse value = zero := by
  classical
  unfold inverse
  simp only [dif_neg notPositive, dif_neg notNegative]

public theorem inverseZero : inverse zero = zero := by
  apply inverseOfNotPositiveOfNotNegative
  · exact ltIrrefl zero
  · exact ltIrrefl zero

public theorem mulInverseCancelOfPositive {value : selection.Carrier}
    (positive : lt zero value) : mul value (inverse value) = one := by
  rw [inverseOfPositive positive]
  exact mulPositiveInverse value positive

public theorem mulInverseCancelOfNegative {value : selection.Carrier}
    (negative : lt value zero) : mul value (inverse value) = one := by
  rw [inverseOfNegative negative]
  have positive := negPositiveOfNegative negative
  calc
    mul value (neg (positiveInverse (neg value) positive)) =
        mul (neg (neg value))
          (neg (positiveInverse (neg value) positive)) := by
      rw [negNeg]
    _ = mul (neg value) (positiveInverse (neg value) positive) :=
      multiplicativeSelection.ring.negMulNeg _ _
    _ = one := mulPositiveInverse (neg value) positive

public theorem negativeOrPositiveOfNonzero {value : selection.Carrier}
    (nonzero : value ≠ zero) : lt value zero ∨ lt zero value := by
  rcases leTotal value zero with nonpositive | nonnegative
  · by_cases reverse : le zero value
    · exact False.elim (nonzero (leAntisymm nonpositive reverse))
    · exact Or.inl ⟨nonpositive, reverse⟩
  · by_cases reverse : le value zero
    · exact False.elim (nonzero (leAntisymm reverse nonnegative))
    · exact Or.inr ⟨nonnegative, reverse⟩

public theorem mulInverseCancel {value : selection.Carrier}
    (nonzero : value ≠ zero) : mul value (inverse value) = one := by
  rcases negativeOrPositiveOfNonzero nonzero with negative | positive
  · exact mulInverseCancelOfNegative negative
  · exact mulInverseCancelOfPositive positive

public theorem inverseMulCancel {value : selection.Carrier}
    (nonzero : value ≠ zero) : mul (inverse value) value = one := by
  rw [mulComm]
  exact mulInverseCancel nonzero

public theorem oneNeZero : one ≠ zero := by
  intro equal
  apply (show (1 : Rat) ≠ 0 by decide)
  apply ofRatInjective
  rw [ofRatOne, ofRatZero, equal]

public theorem inverseNonzero {value : selection.Carrier}
    (nonzero : value ≠ zero) : inverse value ≠ zero := by
  intro inverseZeroEqual
  have identity := mulInverseCancel nonzero
  rw [inverseZeroEqual] at identity
  apply oneNeZero
  calc
    one = mul value zero := identity.symm
    _ = zero := multiplicativeSelection.ring.mulZero value

public theorem mulEqZeroIff {left right : selection.Carrier} :
    mul left right = zero ↔ left = zero ∨ right = zero := by
  constructor
  · intro productZero
    by_cases leftZero : left = zero
    · exact Or.inl leftZero
    · apply Or.inr
      calc
        right = mul one right :=
          (multiplicativeSelection.ring.multiplicative.oneMul right).symm
        _ = mul (mul (inverse left) left) right := by
          rw [inverseMulCancel leftZero]
        _ = mul (inverse left) (mul left right) :=
          multiplicativeSelection.ring.multiplicative.mul_assoc _ _ _
        _ = mul (inverse left) zero := by rw [productZero]
        _ = zero := multiplicativeSelection.ring.mulZero _
  · rintro (leftZero | rightZero)
    · rw [leftZero]
      exact multiplicativeSelection.ring.zeroMul right
    · rw [rightZero]
      exact multiplicativeSelection.ring.mulZero left

public theorem mulPositive {left right : selection.Carrier}
    (leftPositive : lt zero left) (rightPositive : lt zero right) :
    lt zero (mul left right) := by
  constructor
  · exact mulNonnegative leftPositive.left rightPositive.left
  · intro productNonpositive
    have productZero := leAntisymm productNonpositive
      (mulNonnegative leftPositive.left rightPositive.left)
    rcases (mulEqZeroIff.mp productZero) with leftZero | rightZero
    · subst left
      exact (ltIrrefl zero) leftPositive
    · subst right
      exact (ltIrrefl zero) rightPositive

public theorem positiveIffNonnegativeAndNonzero
    {value : selection.Carrier} :
    lt zero value ↔ le zero value ∧ value ≠ zero := by
  constructor
  · intro positive
    refine ⟨positive.left, ?_⟩
    intro equal
    subst value
    exact ltIrrefl zero positive
  · rintro ⟨nonnegative, nonzero⟩
    refine ⟨nonnegative, ?_⟩
    intro nonpositive
    exact nonzero (leAntisymm nonpositive nonnegative)

public theorem positiveInversePositive (value : selection.Carrier)
    (positive : lt zero value) :
    lt zero (positiveInverse value positive) := by
  apply positiveIffNonnegativeAndNonzero.mpr
  refine ⟨positiveInverseNonnegative value positive, ?_⟩
  intro equal
  have identity := mulPositiveInverse value positive
  rw [equal] at identity
  apply oneNeZero
  calc
    one = mul value zero := identity.symm
    _ = zero := multiplicativeSelection.ring.mulZero value

public theorem inverseOfPositivePositive {value : selection.Carrier}
    (positive : lt zero value) : lt zero (inverse value) := by
  rw [inverseOfPositive positive]
  exact positiveInversePositive value positive

public theorem inverseNonnegative {value : selection.Carrier}
    (nonnegative : le zero value) : le zero (inverse value) := by
  by_cases equal : value = zero
  · subst value
    rw [inverseZero]
    exact leRefl zero
  · exact (inverseOfPositivePositive
      (positiveIffNonnegativeAndNonzero.mpr ⟨nonnegative, equal⟩)).left

public theorem mulLeftCancelOfNonzero {factor left right : selection.Carrier}
    (factorNonzero : factor ≠ zero)
    (equal : mul factor left = mul factor right) : left = right := by
  calc
    left = mul one left :=
      (multiplicativeSelection.ring.multiplicative.oneMul left).symm
    _ = mul (mul (inverse factor) factor) left := by
      rw [inverseMulCancel factorNonzero]
    _ = mul (inverse factor) (mul factor left) :=
      multiplicativeSelection.ring.multiplicative.mul_assoc _ _ _
    _ = mul (inverse factor) (mul factor right) := by rw [equal]
    _ = mul (mul (inverse factor) factor) right :=
      (multiplicativeSelection.ring.multiplicative.mul_assoc _ _ _).symm
    _ = mul one right := by rw [inverseMulCancel factorNonzero]
    _ = right := multiplicativeSelection.ring.multiplicative.oneMul right

public theorem mulRightCancelOfNonzero {factor left right : selection.Carrier}
    (factorNonzero : factor ≠ zero)
    (equal : mul left factor = mul right factor) : left = right := by
  apply mulLeftCancelOfNonzero factorNonzero
  rw [mulComm factor left, mulComm factor right]
  exact equal

public theorem inverseInverse (value : selection.Carrier) :
    inverse (inverse value) = value := by
  by_cases zeroValue : value = zero
  · subst value
    rw [inverseZero, inverseZero]
  · apply mulLeftCancelOfNonzero (inverseNonzero zeroValue)
    rw [mulInverseCancel (inverseNonzero zeroValue),
      inverseMulCancel zeroValue]

public theorem mulLtMulPositiveRight {left right factor : selection.Carrier}
    (less : lt left right) (factorPositive : lt zero factor) :
    lt (mul left factor) (mul right factor) := by
  constructor
  · exact mulLeMulNonnegativeRight less.left factorPositive.left
  · intro reverse
    have inverseNonnegative : le zero (inverse factor) :=
      (inverseOfPositivePositive factorPositive).left
    have restored := mulLeMulNonnegativeRight reverse inverseNonnegative
    apply less.right
    simpa only [mulAssoc, mulInverseCancelOfPositive factorPositive,
      mulOne] using restored

public theorem mulLtMulPositiveLeft {left right factor : selection.Carrier}
    (less : lt left right) (factorPositive : lt zero factor) :
    lt (mul factor left) (mul factor right) := by
  rw [mulComm factor left, mulComm factor right]
  exact mulLtMulPositiveRight less factorPositive

public theorem inverseLtInverseOfPositive {left right : selection.Carrier}
    (leftPositive : lt zero left) (rightPositive : lt zero right)
    (less : lt left right) : lt (inverse right) (inverse left) := by
  have rightInversePositive := inverseOfPositivePositive rightPositive
  have first := mulLtMulPositiveRight less rightInversePositive
  have leftNonzero := positiveIffNonnegativeAndNonzero.mp leftPositive |>.right
  have rightNonzero := positiveIffNonnegativeAndNonzero.mp rightPositive |>.right
  have belowOne : lt (mul left (inverse right)) one := by
    simpa only [mulInverseCancel rightNonzero] using first
  have scaled := mulLtMulPositiveLeft belowOne
    (inverseOfPositivePositive leftPositive)
  simpa only [← mulAssoc, inverseMulCancel leftNonzero,
    mulComm one, mulOne] using scaled

/-- Reciprocal order reversal for positive elements.
Positivity of the right element is derived from positivity of the left
element and the order relation. -/
public theorem inverseLeInverseOfPositive {left right : selection.Carrier}
    (leftPositive : lt zero left) (included : le left right) :
    le (inverse right) (inverse left) := by
  by_cases equal : left = right
  · rw [equal]
    exact leRefl _
  · have strict : lt left right :=
      ⟨included, fun reverse => equal (leAntisymm included reverse)⟩
    have rightPositive : lt zero right :=
      ⟨leTrans leftPositive.left included,
        fun nonpositive => leftPositive.right (leTrans included nonpositive)⟩
    exact (inverseLtInverseOfPositive leftPositive rightPositive strict).left

@[expose] public noncomputable def div
    (left right : selection.Carrier) : selection.Carrier :=
  mul left (inverse right)

public theorem divEqMulInverse (left right : selection.Carrier) :
    div left right = mul left (inverse right) :=
  rfl

public theorem divNonnegative {left right : selection.Carrier}
    (leftNonnegative : le zero left) (rightNonnegative : le zero right) :
    le zero (div left right) :=
  mulNonnegative leftNonnegative (inverseNonnegative rightNonnegative)

public theorem divPositive {left right : selection.Carrier}
    (leftPositive : lt zero left) (rightPositive : lt zero right) :
    lt zero (div left right) :=
  mulPositive leftPositive (inverseOfPositivePositive rightPositive)

/-- Order reversal for division with a nonnegative numerator and positive lower
denominator. -/
public theorem divLeDivOfPositive {numerator left right : selection.Carrier}
    (numeratorNonnegative : le zero numerator)
    (leftPositive : lt zero left) (included : le left right) :
    le (div numerator right) (div numerator left) :=
  mulLeMulNonnegativeLeft
    (inverseLeInverseOfPositive leftPositive included) numeratorNonnegative

/-- Strict order reversal for division with a positive numerator and positive
lower denominator. -/
public theorem divLtDivOfPositive {numerator left right : selection.Carrier}
    (numeratorPositive : lt zero numerator)
    (leftPositive : lt zero left) (less : lt left right) :
    lt (div numerator right) (div numerator left) := by
  have rightPositive : lt zero right :=
    ⟨leTrans leftPositive.left less.left,
      fun nonpositive => leftPositive.right (leTrans less.left nonpositive)⟩
  exact mulLtMulPositiveLeft
    (inverseLtInverseOfPositive leftPositive rightPositive less) numeratorPositive

public theorem divMulCancel (left : selection.Carrier)
    {right : selection.Carrier} (rightNonzero : right ≠ zero) :
    mul (div left right) right = left := by
  unfold div
  rw [mulAssoc, inverseMulCancel rightNonzero, mulOne]

public theorem mulDivCancel (left : selection.Carrier)
    {right : selection.Carrier} (rightNonzero : right ≠ zero) :
    mul right (div left right) = left := by
  rw [mulComm]
  exact divMulCancel left rightNonzero

public theorem divSelf {value : selection.Carrier}
    (nonzero : value ≠ zero) : div value value = one :=
  mulInverseCancel nonzero

public theorem inverseEqDivOne (value : selection.Carrier) :
    inverse value = div one value := by
  unfold div
  symm
  calc
    mul one (inverse value) = mul (inverse value) one := mulComm _ _
    _ = inverse value := mulOne _

public theorem inverseOne : inverse one = one := by
  have identity := mulInverseCancel (value := one) oneNeZero
  simpa only [mulComm one (inverse one), mulOne] using identity

public theorem divOne (value : selection.Carrier) : div value one = value := by
  rw [divEqMulInverse, inverseOne, mulOne]

public theorem zeroDiv (value : selection.Carrier) : div zero value = zero :=
  multiplicativeSelection.ring.zeroMul (inverse value)

/-- Division by zero evaluates to zero by reciprocal definition. -/
public theorem divZero (value : selection.Carrier) : div value zero = zero := by
  rw [divEqMulInverse, inverseZero]
  exact multiplicativeSelection.ring.mulZero value

/-- Iterated division cancellation requiring only a nonzero numerator.
The cancellation holds at a zero denominator because division by zero vanishes. -/
public theorem divDivCancel (numerator denominator : selection.Carrier)
    (numeratorNonzero : numerator ≠ zero) :
    div numerator (div numerator denominator) = denominator := by
  by_cases denominatorZero : denominator = zero
  · subst denominator
    rw [divZero, divZero]
  · have quotientNonzero : div numerator denominator ≠ zero := by
      intro quotientZero
      have cancellation := divMulCancel numerator denominatorZero
      rw [quotientZero] at cancellation
      have vanished : mul zero denominator = zero :=
        multiplicativeSelection.ring.zeroMul denominator
      exact numeratorNonzero (cancellation.symm.trans vanished)
    apply mulRightCancelOfNonzero quotientNonzero
    rw [divMulCancel numerator quotientNonzero,
      mulDivCancel numerator denominatorZero]

end Foundations.Real.Construction.Dedekind
