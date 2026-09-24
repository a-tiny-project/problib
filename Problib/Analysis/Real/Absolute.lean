module

public import Problib.Real.Arithmetic

/-! Absolute value on the sealed real carrier.

`Problib.Analysis.Rational` builds its epsilon-delta estimates on `Rat.abs`,
which Lean core supplies. The real carrier has no absolute value, so the same
estimates need one built first. It is stated here, beside the analysis that
consumes it, exactly as the rational absolute-value lemmas are stated beside the
rational derivative. The strict order and ring arithmetic it rests on live in
`Problib.Real.Arithmetic`.
-/

set_option autoImplicit false

namespace Problib.Analysis.Real

open Problib.Real.Construction.Dedekind

/-! ### Absolute value -/

/-- The absolute value of a real-carrier value, by sign. -/
@[expose] public noncomputable def abs (value : selection.Carrier) :
    selection.Carrier := by
  classical
  exact if le zero value then value else neg value

/-- Above zero the absolute value is the value. -/
public theorem abs_of_nonnegative {value : selection.Carrier}
    (nonnegative : le zero value) : abs value = value := by
  classical
  unfold abs
  simp only [if_pos nonnegative]

/-- Below zero the absolute value is the negation. -/
public theorem abs_of_nonpositive {value : selection.Carrier}
    (nonpositive : le value zero) : abs value = neg value := by
  classical
  by_cases nonnegative : le zero value
  · have equal : value = zero := le_antisymm nonpositive nonnegative
    rw [equal, neg_zero, abs_of_nonnegative (le_refl zero)]
  · unfold abs
    simp only [if_neg nonnegative]

/-- The absolute value of zero is zero. -/
public theorem abs_zero : abs zero = zero :=
  abs_of_nonnegative (le_refl zero)

/-- The absolute value is nonnegative. -/
public theorem abs_nonnegative (value : selection.Carrier) :
    le zero (abs value) := by
  classical
  by_cases nonnegative : le zero value
  · rw [abs_of_nonnegative nonnegative]
    exact nonnegative
  · rw [abs_of_nonpositive (le_of_lt (lt_of_not_le nonnegative))]
    exact neg_nonnegative_iff.mpr (le_of_lt (lt_of_not_le nonnegative))

/-- A weak absolute bound is a two-sided weak bound. -/
public theorem abs_le {value bound : selection.Carrier} :
    le (abs value) bound ↔ le (neg bound) value ∧ le value bound := by
  classical
  constructor
  · intro bounded
    by_cases nonnegative : le zero value
    · rw [abs_of_nonnegative nonnegative] at bounded
      refine ⟨?_, bounded⟩
      exact le_trans (neg_nonpositive_iff.mp (le_trans nonnegative bounded)) nonnegative
    · have nonpositive := le_of_lt (lt_of_not_le nonnegative)
      rw [abs_of_nonpositive nonpositive] at bounded
      have reflected : le (neg bound) (neg (neg value)) := neg_le_neg_iff.mpr bounded
      rw [neg_neg] at reflected
      refine ⟨reflected, ?_⟩
      exact le_trans nonpositive
        (le_trans (neg_nonnegative_iff.mpr nonpositive) bounded)
  · rintro ⟨lower, upper⟩
    by_cases nonnegative : le zero value
    · rw [abs_of_nonnegative nonnegative]
      exact upper
    · rw [abs_of_nonpositive (le_of_lt (lt_of_not_le nonnegative))]
      have reflected : le (neg value) (neg (neg bound)) := neg_le_neg_iff.mpr lower
      rwa [neg_neg] at reflected

/-- A strict absolute bound is a two-sided strict bound. -/
public theorem abs_lt {value bound : selection.Carrier} :
    lt (abs value) bound ↔ lt (neg bound) value ∧ lt value bound := by
  classical
  constructor
  · intro bounded
    by_cases nonnegative : le zero value
    · rw [abs_of_nonnegative nonnegative] at bounded
      refine ⟨?_, bounded⟩
      exact lt_of_lt_of_le
        (neg_negative_iff.mp (lt_of_le_of_lt nonnegative bounded)) nonnegative
    · have nonpositive := le_of_lt (lt_of_not_le nonnegative)
      rw [abs_of_nonpositive nonpositive] at bounded
      have reflected : lt (neg bound) (neg (neg value)) := neg_lt_neg_iff.mpr bounded
      rw [neg_neg] at reflected
      refine ⟨reflected, ?_⟩
      exact lt_of_le_of_lt nonpositive
        (lt_of_le_of_lt (neg_nonnegative_iff.mpr nonpositive) bounded)
  · rintro ⟨lower, upper⟩
    by_cases nonnegative : le zero value
    · rw [abs_of_nonnegative nonnegative]
      exact upper
    · rw [abs_of_nonpositive (le_of_lt (lt_of_not_le nonnegative))]
      have reflected : lt (neg value) (neg (neg bound)) := neg_lt_neg_iff.mpr lower
      rwa [neg_neg] at reflected

/-- A value is weakly below its absolute value. -/
public theorem le_abs (value : selection.Carrier) : le value (abs value) :=
  (abs_le.mp (le_refl (abs value))).right

/-- The negated absolute value is weakly below the value. -/
public theorem neg_abs_le (value : selection.Carrier) :
    le (neg (abs value)) value :=
  (abs_le.mp (le_refl (abs value))).left

/-- Absolute value ignores sign. -/
public theorem abs_neg (value : selection.Carrier) : abs (neg value) = abs value := by
  classical
  by_cases nonnegative : le zero value
  · rw [abs_of_nonpositive (neg_nonpositive_iff.mp nonnegative), neg_neg,
      abs_of_nonnegative nonnegative]
  · have nonpositive := le_of_lt (lt_of_not_le nonnegative)
    rw [abs_of_nonnegative (neg_nonnegative_iff.mpr nonpositive),
      abs_of_nonpositive nonpositive]

/-- Absolute value of a difference is symmetric in its arguments. -/
public theorem abs_sub_comm (left right : selection.Carrier) :
    abs (sub left right) = abs (sub right left) := by
  rw [← neg_sub left right, abs_neg]

/-- The absolute value vanishes only at zero. -/
public theorem abs_eq_zero_iff {value : selection.Carrier} :
    abs value = zero ↔ value = zero := by
  classical
  constructor
  · intro vanished
    by_cases nonnegative : le zero value
    · rw [abs_of_nonnegative nonnegative] at vanished
      exact vanished
    · rw [abs_of_nonpositive (le_of_lt (lt_of_not_le nonnegative))] at vanished
      have := congrArg neg vanished
      rwa [neg_neg, neg_zero] at this
  · intro vanished
    rw [vanished, abs_zero]

/-- A nonzero value has positive absolute value. -/
public theorem abs_positive_of_nonzero {value : selection.Carrier}
    (nonzero : value ≠ zero) : lt zero (abs value) :=
  positive_iff_nonnegative_and_nonzero.mpr
    ⟨abs_nonnegative value, fun vanished => nonzero (abs_eq_zero_iff.mp vanished)⟩

/-- The triangle inequality. -/
public theorem abs_add_le (left right : selection.Carrier) :
    le (abs (add left right)) (add (abs left) (abs right)) := by
  apply abs_le.mpr
  constructor
  · rw [neg_add]
    exact add_le_add (neg_abs_le left) (neg_abs_le right)
  · exact add_le_add (le_abs left) (le_abs right)

/-- Absolute value is multiplicative. -/
public theorem abs_mul (left right : selection.Carrier) :
    abs (mul left right) = mul (abs left) (abs right) := by
  classical
  by_cases leftNonnegative : le zero left <;> by_cases rightNonnegative : le zero right
  · rw [abs_of_nonnegative leftNonnegative, abs_of_nonnegative rightNonnegative,
      abs_of_nonnegative (mul_nonnegative leftNonnegative rightNonnegative)]
  · have rightNonpositive := le_of_lt (lt_of_not_le rightNonnegative)
    have product : le zero (mul left (neg right)) :=
      mul_nonnegative leftNonnegative (neg_nonnegative_iff.mpr rightNonpositive)
    rw [mul_neg] at product
    rw [abs_of_nonnegative leftNonnegative, abs_of_nonpositive rightNonpositive,
      abs_of_nonpositive (neg_nonnegative_iff.mp product),
      mul_neg]
  · have leftNonpositive := le_of_lt (lt_of_not_le leftNonnegative)
    have product : le zero (mul (neg left) right) :=
      mul_nonnegative (neg_nonnegative_iff.mpr leftNonpositive) rightNonnegative
    rw [neg_mul] at product
    rw [abs_of_nonpositive leftNonpositive, abs_of_nonnegative rightNonnegative,
      abs_of_nonpositive (neg_nonnegative_iff.mp product),
      neg_mul]
  · have leftNonpositive := le_of_lt (lt_of_not_le leftNonnegative)
    have rightNonpositive := le_of_lt (lt_of_not_le rightNonnegative)
    have product : le zero (mul (neg left) (neg right)) :=
      mul_nonnegative (neg_nonnegative_iff.mpr leftNonpositive)
        (neg_nonnegative_iff.mpr rightNonpositive)
    rw [neg_mul_neg] at product
    rw [abs_of_nonpositive leftNonpositive, abs_of_nonpositive rightNonpositive,
      abs_of_nonnegative product, neg_mul_neg]

/-- Absolute value commutes with the reciprocal. -/
public theorem abs_inverse (value : selection.Carrier) :
    abs (inverse value) = inverse (abs value) := by
  classical
  by_cases nonnegative : le zero value
  · rw [abs_of_nonnegative nonnegative,
      abs_of_nonnegative (inverse_nonnegative nonnegative)]
  · have nonpositive := le_of_lt (lt_of_not_le nonnegative)
    have reciprocalNonpositive : le (inverse value) zero :=
      neg_nonnegative_iff.mp (by
        rw [← inverse_neg]
        exact inverse_nonnegative (neg_nonnegative_iff.mpr nonpositive))
    rw [abs_of_nonpositive nonpositive, abs_of_nonpositive reciprocalNonpositive,
      inverse_neg]

/-- Absolute value commutes with division. -/
public theorem abs_div (left right : selection.Carrier) :
    abs (div left right) = div (abs left) (abs right) := by
  rw [div_eq_mul_inverse, div_eq_mul_inverse, abs_mul, abs_inverse]

end Problib.Analysis.Real
