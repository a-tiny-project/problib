module

public import Problib.Real.Construction.Dedekind.Inverse

set_option autoImplicit false

/-
Copyright (c) 2026 Si-Qi Liu.
Licensed under the MIT License.

Adapted from Tautology/RealBasic/ModuleBackend/Dedekind/Inv.lean at
commit 261012c7540673d59a4015371b7618b7573d43da.

Tiny exposes the sealed selected-carrier reciprocal through explicit
operations and laws rather than typeclass instances.
-/

namespace Problib.Real.Construction.Dedekind

public theorem lt_irrefl (value : selection.Carrier) : ¬lt value value := by
  intro strict
  exact strict.right strict.left

public theorem neg_zero : neg zero = zero :=
  Problib.Algebra.AdditiveCommutativeGroupLaws.neg_zero
    additive.group

public theorem neg_neg (value : selection.Carrier) : neg (neg value) = value :=
  Problib.Algebra.AdditiveCommutativeGroupLaws.neg_neg
    additive.group value

public theorem neg_positive_of_negative {value : selection.Carrier}
    (negative : lt value zero) : lt zero (neg value) := by
  unfold lt at negative ⊢
  constructor
  · rw [← neg_zero]
    exact neg_le_neg_iff.mpr negative.left
  · intro nonpositive
    have reversed := neg_le_neg_iff.mpr nonpositive
    apply negative.right
    simpa only [neg_zero, neg_neg] using reversed

@[expose] public noncomputable def positiveInverse
    (value : selection.Carrier) (positive : lt zero value) :
    selection.Carrier :=
  Classical.choose (Cut.exists_selected_positive_inverse value positive)

public theorem positiveInverse_nonnegative (value : selection.Carrier)
    (positive : lt zero value) : le zero (positiveInverse value positive) :=
  (Classical.choose_spec
    (Cut.exists_selected_positive_inverse value positive)).left

public theorem mul_positiveInverse (value : selection.Carrier)
    (positive : lt zero value) :
    mul value (positiveInverse value positive) = one :=
  (Classical.choose_spec
    (Cut.exists_selected_positive_inverse value positive)).right

@[expose] public noncomputable def inverse
    (value : selection.Carrier) : selection.Carrier := by
  classical
  exact if positive : lt zero value then
    positiveInverse value positive
  else if negative : lt value zero then
    neg (positiveInverse (neg value) (neg_positive_of_negative negative))
  else
    zero

public theorem inverse_of_positive {value : selection.Carrier}
    (positive : lt zero value) :
    inverse value = positiveInverse value positive := by
  classical
  unfold inverse
  simp only [dif_pos positive]

public theorem inverse_of_negative {value : selection.Carrier}
    (negative : lt value zero) :
    inverse value =
      neg (positiveInverse (neg value) (neg_positive_of_negative negative)) := by
  classical
  unfold inverse
  have notPositive : ¬lt zero value := by
    intro positive
    exact negative.right positive.left
  simp only [dif_neg notPositive, dif_pos negative]

public theorem inverse_of_not_positive_of_not_negative
    {value : selection.Carrier}
    (notPositive : ¬lt zero value) (notNegative : ¬lt value zero) :
    inverse value = zero := by
  classical
  unfold inverse
  simp only [dif_neg notPositive, dif_neg notNegative]

public theorem inverse_zero : inverse zero = zero := by
  apply inverse_of_not_positive_of_not_negative
  · exact lt_irrefl zero
  · exact lt_irrefl zero

public theorem mul_inverse_cancel_of_positive {value : selection.Carrier}
    (positive : lt zero value) : mul value (inverse value) = one := by
  rw [inverse_of_positive positive]
  exact mul_positiveInverse value positive

public theorem mul_inverse_cancel_of_negative {value : selection.Carrier}
    (negative : lt value zero) : mul value (inverse value) = one := by
  rw [inverse_of_negative negative]
  have positive := neg_positive_of_negative negative
  calc
    mul value (neg (positiveInverse (neg value) positive)) =
        mul (neg (neg value))
          (neg (positiveInverse (neg value) positive)) := by
      rw [neg_neg]
    _ = mul (neg value) (positiveInverse (neg value) positive) :=
      multiplicativeSelection.ring.neg_mul_neg _ _
    _ = one := mul_positiveInverse (neg value) positive

public theorem negative_or_positive_of_nonzero {value : selection.Carrier}
    (nonzero : value ≠ zero) : lt value zero ∨ lt zero value := by
  rcases le_total value zero with nonpositive | nonnegative
  · by_cases reverse : le zero value
    · exact False.elim (nonzero (le_antisymm nonpositive reverse))
    · exact Or.inl ⟨nonpositive, reverse⟩
  · by_cases reverse : le value zero
    · exact False.elim (nonzero (le_antisymm reverse nonnegative))
    · exact Or.inr ⟨nonnegative, reverse⟩

public theorem mul_inverse_cancel {value : selection.Carrier}
    (nonzero : value ≠ zero) : mul value (inverse value) = one := by
  rcases negative_or_positive_of_nonzero nonzero with negative | positive
  · exact mul_inverse_cancel_of_negative negative
  · exact mul_inverse_cancel_of_positive positive

public theorem inverse_mul_cancel {value : selection.Carrier}
    (nonzero : value ≠ zero) : mul (inverse value) value = one := by
  rw [mul_comm]
  exact mul_inverse_cancel nonzero

public theorem one_ne_zero : one ≠ zero := by
  intro equal
  apply (show (1 : Rat) ≠ 0 by decide)
  apply ofRat_injective
  rw [ofRat_one, ofRat_zero, equal]

public theorem inverse_nonzero {value : selection.Carrier}
    (nonzero : value ≠ zero) : inverse value ≠ zero := by
  intro inverseZeroEqual
  have identity := mul_inverse_cancel nonzero
  rw [inverseZeroEqual] at identity
  apply one_ne_zero
  calc
    one = mul value zero := identity.symm
    _ = zero := multiplicativeSelection.ring.mul_zero value

public theorem mul_eq_zero_iff {left right : selection.Carrier} :
    mul left right = zero ↔ left = zero ∨ right = zero := by
  constructor
  · intro productZero
    by_cases leftZero : left = zero
    · exact Or.inl leftZero
    · apply Or.inr
      calc
        right = mul one right :=
          (multiplicativeSelection.ring.multiplicative.one_mul right).symm
        _ = mul (mul (inverse left) left) right := by
          rw [inverse_mul_cancel leftZero]
        _ = mul (inverse left) (mul left right) :=
          multiplicativeSelection.ring.multiplicative.mul_assoc _ _ _
        _ = mul (inverse left) zero := by rw [productZero]
        _ = zero := multiplicativeSelection.ring.mul_zero _
  · rintro (leftZero | rightZero)
    · rw [leftZero]
      exact multiplicativeSelection.ring.zero_mul right
    · rw [rightZero]
      exact multiplicativeSelection.ring.mul_zero left

public theorem mul_positive {left right : selection.Carrier}
    (leftPositive : lt zero left) (rightPositive : lt zero right) :
    lt zero (mul left right) := by
  constructor
  · exact mul_nonnegative leftPositive.left rightPositive.left
  · intro productNonpositive
    have productZero := le_antisymm productNonpositive
      (mul_nonnegative leftPositive.left rightPositive.left)
    rcases (mul_eq_zero_iff.mp productZero) with leftZero | rightZero
    · subst left
      exact (lt_irrefl zero) leftPositive
    · subst right
      exact (lt_irrefl zero) rightPositive

public theorem positive_iff_nonnegative_and_nonzero
    {value : selection.Carrier} :
    lt zero value ↔ le zero value ∧ value ≠ zero := by
  constructor
  · intro positive
    refine ⟨positive.left, ?_⟩
    intro equal
    subst value
    exact lt_irrefl zero positive
  · rintro ⟨nonnegative, nonzero⟩
    refine ⟨nonnegative, ?_⟩
    intro nonpositive
    exact nonzero (le_antisymm nonpositive nonnegative)

public theorem positiveInverse_positive (value : selection.Carrier)
    (positive : lt zero value) :
    lt zero (positiveInverse value positive) := by
  apply positive_iff_nonnegative_and_nonzero.mpr
  refine ⟨positiveInverse_nonnegative value positive, ?_⟩
  intro equal
  have identity := mul_positiveInverse value positive
  rw [equal] at identity
  apply one_ne_zero
  calc
    one = mul value zero := identity.symm
    _ = zero := multiplicativeSelection.ring.mul_zero value

public theorem inverse_of_positive_positive {value : selection.Carrier}
    (positive : lt zero value) : lt zero (inverse value) := by
  rw [inverse_of_positive positive]
  exact positiveInverse_positive value positive

public theorem inverse_nonnegative {value : selection.Carrier}
    (nonnegative : le zero value) : le zero (inverse value) := by
  by_cases equal : value = zero
  · subst value
    rw [inverse_zero]
    exact le_refl zero
  · exact (inverse_of_positive_positive
      (positive_iff_nonnegative_and_nonzero.mpr ⟨nonnegative, equal⟩)).left

public theorem mul_left_cancel_of_nonzero {factor left right : selection.Carrier}
    (factorNonzero : factor ≠ zero)
    (equal : mul factor left = mul factor right) : left = right := by
  calc
    left = mul one left :=
      (multiplicativeSelection.ring.multiplicative.one_mul left).symm
    _ = mul (mul (inverse factor) factor) left := by
      rw [inverse_mul_cancel factorNonzero]
    _ = mul (inverse factor) (mul factor left) :=
      multiplicativeSelection.ring.multiplicative.mul_assoc _ _ _
    _ = mul (inverse factor) (mul factor right) := by rw [equal]
    _ = mul (mul (inverse factor) factor) right :=
      (multiplicativeSelection.ring.multiplicative.mul_assoc _ _ _).symm
    _ = mul one right := by rw [inverse_mul_cancel factorNonzero]
    _ = right := multiplicativeSelection.ring.multiplicative.one_mul right

public theorem mul_right_cancel_of_nonzero {factor left right : selection.Carrier}
    (factorNonzero : factor ≠ zero)
    (equal : mul left factor = mul right factor) : left = right := by
  apply mul_left_cancel_of_nonzero factorNonzero
  rw [mul_comm factor left, mul_comm factor right]
  exact equal

public theorem inverse_inverse (value : selection.Carrier) :
    inverse (inverse value) = value := by
  by_cases zeroValue : value = zero
  · subst value
    rw [inverse_zero, inverse_zero]
  · apply mul_left_cancel_of_nonzero (inverse_nonzero zeroValue)
    rw [mul_inverse_cancel (inverse_nonzero zeroValue),
      inverse_mul_cancel zeroValue]

public theorem mul_lt_mul_positive_right {left right factor : selection.Carrier}
    (less : lt left right) (factorPositive : lt zero factor) :
    lt (mul left factor) (mul right factor) := by
  constructor
  · exact mul_le_mul_nonnegative_right less.left factorPositive.left
  · intro reverse
    have inverseNonnegative : le zero (inverse factor) :=
      (inverse_of_positive_positive factorPositive).left
    have restored := mul_le_mul_nonnegative_right reverse inverseNonnegative
    apply less.right
    simpa only [mul_assoc, mul_inverse_cancel_of_positive factorPositive,
      mul_one] using restored

public theorem mul_lt_mul_positive_left {left right factor : selection.Carrier}
    (less : lt left right) (factorPositive : lt zero factor) :
    lt (mul factor left) (mul factor right) := by
  rw [mul_comm factor left, mul_comm factor right]
  exact mul_lt_mul_positive_right less factorPositive

public theorem inverse_lt_inverse_of_positive {left right : selection.Carrier}
    (leftPositive : lt zero left) (rightPositive : lt zero right)
    (less : lt left right) : lt (inverse right) (inverse left) := by
  have rightInversePositive := inverse_of_positive_positive rightPositive
  have first := mul_lt_mul_positive_right less rightInversePositive
  have leftNonzero := positive_iff_nonnegative_and_nonzero.mp leftPositive |>.right
  have rightNonzero := positive_iff_nonnegative_and_nonzero.mp rightPositive |>.right
  have belowOne : lt (mul left (inverse right)) one := by
    simpa only [mul_inverse_cancel rightNonzero] using first
  have scaled := mul_lt_mul_positive_left belowOne
    (inverse_of_positive_positive leftPositive)
  simpa only [← mul_assoc, inverse_mul_cancel leftNonzero,
    mul_comm one, mul_one] using scaled

/-- Reciprocal order reversal for positive elements.
Positivity of the right element is derived from positivity of the left
element and the order relation. -/
public theorem inverse_le_inverse_of_positive {left right : selection.Carrier}
    (leftPositive : lt zero left) (included : le left right) :
    le (inverse right) (inverse left) := by
  by_cases equal : left = right
  · rw [equal]
    exact le_refl _
  · have strict : lt left right :=
      ⟨included, fun reverse => equal (le_antisymm included reverse)⟩
    have rightPositive : lt zero right :=
      ⟨le_trans leftPositive.left included,
        fun nonpositive => leftPositive.right (le_trans included nonpositive)⟩
    exact (inverse_lt_inverse_of_positive leftPositive rightPositive strict).left

@[expose] public noncomputable def div
    (left right : selection.Carrier) : selection.Carrier :=
  mul left (inverse right)

public theorem div_eq_mul_inverse (left right : selection.Carrier) :
    div left right = mul left (inverse right) :=
  rfl

public theorem div_nonnegative {left right : selection.Carrier}
    (leftNonnegative : le zero left) (rightNonnegative : le zero right) :
    le zero (div left right) :=
  mul_nonnegative leftNonnegative (inverse_nonnegative rightNonnegative)

public theorem div_positive {left right : selection.Carrier}
    (leftPositive : lt zero left) (rightPositive : lt zero right) :
    lt zero (div left right) :=
  mul_positive leftPositive (inverse_of_positive_positive rightPositive)

/-- Order reversal for division with a nonnegative numerator and positive lower
denominator. -/
public theorem div_le_div_of_positive {numerator left right : selection.Carrier}
    (numeratorNonnegative : le zero numerator)
    (leftPositive : lt zero left) (included : le left right) :
    le (div numerator right) (div numerator left) :=
  mul_le_mul_nonnegative_left
    (inverse_le_inverse_of_positive leftPositive included) numeratorNonnegative

/-- Strict order reversal for division with a positive numerator and positive
lower denominator. -/
public theorem div_lt_div_of_positive {numerator left right : selection.Carrier}
    (numeratorPositive : lt zero numerator)
    (leftPositive : lt zero left) (less : lt left right) :
    lt (div numerator right) (div numerator left) := by
  have rightPositive : lt zero right :=
    ⟨le_trans leftPositive.left less.left,
      fun nonpositive => leftPositive.right (le_trans less.left nonpositive)⟩
  exact mul_lt_mul_positive_left
    (inverse_lt_inverse_of_positive leftPositive rightPositive less) numeratorPositive

public theorem div_mul_cancel (left : selection.Carrier)
    {right : selection.Carrier} (rightNonzero : right ≠ zero) :
    mul (div left right) right = left := by
  unfold div
  rw [mul_assoc, inverse_mul_cancel rightNonzero, mul_one]

public theorem mul_div_cancel (left : selection.Carrier)
    {right : selection.Carrier} (rightNonzero : right ≠ zero) :
    mul right (div left right) = left := by
  rw [mul_comm]
  exact div_mul_cancel left rightNonzero

public theorem div_self {value : selection.Carrier}
    (nonzero : value ≠ zero) : div value value = one :=
  mul_inverse_cancel nonzero

public theorem inverse_eq_div_one (value : selection.Carrier) :
    inverse value = div one value := by
  unfold div
  symm
  calc
    mul one (inverse value) = mul (inverse value) one := mul_comm _ _
    _ = inverse value := mul_one _

public theorem inverse_one : inverse one = one := by
  have identity := mul_inverse_cancel (value := one) one_ne_zero
  simpa only [mul_comm one (inverse one), mul_one] using identity

public theorem div_one (value : selection.Carrier) : div value one = value := by
  rw [div_eq_mul_inverse, inverse_one, mul_one]

public theorem zero_div (value : selection.Carrier) : div zero value = zero :=
  multiplicativeSelection.ring.zero_mul (inverse value)

/-- Division by zero evaluates to zero by reciprocal definition. -/
public theorem div_zero (value : selection.Carrier) : div value zero = zero := by
  rw [div_eq_mul_inverse, inverse_zero]
  exact multiplicativeSelection.ring.mul_zero value

/-- Iterated division cancellation requiring only a nonzero numerator.
The cancellation holds at a zero denominator because division by zero vanishes. -/
public theorem div_div_cancel (numerator denominator : selection.Carrier)
    (numeratorNonzero : numerator ≠ zero) :
    div numerator (div numerator denominator) = denominator := by
  by_cases denominatorZero : denominator = zero
  · subst denominator
    rw [div_zero, div_zero]
  · have quotientNonzero : div numerator denominator ≠ zero := by
      intro quotientZero
      have cancellation := div_mul_cancel numerator denominatorZero
      rw [quotientZero] at cancellation
      have vanished : mul zero denominator = zero :=
        multiplicativeSelection.ring.zero_mul denominator
      exact numeratorNonzero (cancellation.symm.trans vanished)
    apply mul_right_cancel_of_nonzero quotientNonzero
    rw [div_mul_cancel numerator quotientNonzero,
      mul_div_cancel numerator denominatorZero]

/-- The rational embedding carries the totalized rational reciprocal to the
selected reciprocal. Both sides send zero to zero, and elsewhere the embedded
reciprocal is a right inverse, which the nonzero factor cancels. -/
public theorem ofRat_inverse (value : Rat) :
    selection.ofRat value⁻¹ = inverse (selection.ofRat value) := by
  by_cases zeroValue : value = 0
  · subst value
    rw [Rat.inv_zero, ofRat_zero, inverse_zero]
  · have embeddedNonzero : selection.ofRat value ≠ zero := by
      intro equal
      exact zeroValue (ofRat_injective (equal.trans ofRat_zero.symm))
    apply mul_left_cancel_of_nonzero embeddedNonzero
    rw [← ofRat_mul, Rat.mul_inv_cancel value zeroValue, ofRat_one,
      mul_inverse_cancel embeddedNonzero]

/-- The rational embedding preserves totalized division, including division by
zero, which vanishes on both sides. -/
public theorem ofRat_div (left right : Rat) :
    selection.ofRat (left / right) = div (selection.ofRat left) (selection.ofRat right) := by
  rw [Rat.div_def, ofRat_mul, ofRat_inverse, div_eq_mul_inverse]

end Problib.Real.Construction.Dedekind
