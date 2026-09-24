module

public import Problib.Real.Inverse

/-! Order and ring arithmetic on the sealed real carrier.

The carrier's selections expose addition, multiplication, and the weak order
through their laws. The facts every analysis file needs next come here: the
strict order, translation, negation, the ring identities the selections state
only for their own structures, and small constants such as two. They are one
`le_trans` or one rewrite each. Before this leaf existed, files re-proved them
privately. `Problib.Analysis.Real.Absolute` builds absolute value on them.
-/

set_option autoImplicit false

namespace Problib.Real.Construction.Dedekind

private instance : Std.Associative (α := selection.Carrier) mul :=
  ⟨fun left middle right => mul_assoc left middle right⟩
private instance : Std.Commutative (α := selection.Carrier) mul := ⟨mul_comm⟩

/-! ### Strict order

`lt left right` unfolds to `le left right ∧ ¬le right left`, so every fact below
is one `le_trans` and one contrapositive. -/

/-- A strict bound is a weak bound. -/
public theorem le_of_lt {left right : selection.Carrier}
    (less : lt left right) : le left right :=
  less.left

/-- Strict order is transitive. -/
public theorem lt_trans {left middle right : selection.Carrier}
    (first : lt left middle) (second : lt middle right) : lt left right :=
  ⟨le_trans first.left second.left,
    fun reverse => first.right (le_trans second.left reverse)⟩

/-- A strict bound followed by a weak bound is strict. -/
public theorem lt_of_lt_of_le {left middle right : selection.Carrier}
    (first : lt left middle) (second : le middle right) : lt left right :=
  ⟨le_trans first.left second, fun reverse => first.right (le_trans second reverse)⟩

/-- A weak bound followed by a strict bound is strict. -/
public theorem lt_of_le_of_lt {left middle right : selection.Carrier}
    (first : le left middle) (second : lt middle right) : lt left right :=
  ⟨le_trans first second.left, fun reverse => second.right (le_trans reverse first)⟩

/-- A failed weak bound is a strict bound the other way. -/
public theorem lt_of_not_le {left right : selection.Carrier}
    (failed : ¬le left right) : lt right left :=
  ⟨(le_total left right).resolve_left failed, failed⟩

/-- A strict bound refutes the reverse weak bound. -/
public theorem not_le_of_lt {left right : selection.Carrier}
    (less : lt left right) : ¬le right left :=
  less.right

/-- Exactly one of below, equal, above holds. -/
public theorem lt_trichotomy (left right : selection.Carrier) :
    lt left right ∨ left = right ∨ lt right left := by
  classical
  by_cases forward : le left right
  · by_cases backward : le right left
    · exact Or.inr (Or.inl (le_antisymm forward backward))
    · exact Or.inl ⟨forward, backward⟩
  · exact Or.inr (Or.inr (lt_of_not_le forward))

/-- Distinct values are strictly ordered one way or the other. -/
public theorem lt_or_lt_of_ne {left right : selection.Carrier}
    (distinct : left ≠ right) : lt left right ∨ lt right left := by
  rcases lt_trichotomy left right with below | equal | above
  · exact Or.inl below
  · exact absurd equal distinct
  · exact Or.inr above

/-! ### Translation and negation -/

/-- Adding on the right preserves a strict bound. -/
public theorem add_lt_add_right {left right : selection.Carrier}
    (shift : selection.Carrier) (less : lt left right) :
    lt (add left shift) (add right shift) :=
  add_lt_add_right_iff.mpr less

/-- Adding on the left preserves a strict bound. -/
public theorem add_lt_add_left {left right : selection.Carrier}
    (shift : selection.Carrier) (less : lt left right) :
    lt (add shift left) (add shift right) :=
  add_lt_add_left_iff.mpr less

/-- Weak bounds add. -/
public theorem add_le_add {first second third fourth : selection.Carrier}
    (left : le first second) (right : le third fourth) :
    le (add first third) (add second fourth) :=
  le_trans (add_le_add_right_iff.mpr left) (add_le_add_left_iff.mpr right)

/-- A strict bound and a weak bound add to a strict bound. -/
public theorem add_lt_add_le {first second third fourth : selection.Carrier}
    (left : lt first second) (right : le third fourth) :
    lt (add first third) (add second fourth) :=
  lt_of_lt_of_le (add_lt_add_right third left) (add_le_add_left_iff.mpr right)

/-- Strict bounds add. -/
public theorem add_lt_add {first second third fourth : selection.Carrier}
    (left : lt first second) (right : lt third fourth) :
    lt (add first third) (add second fourth) :=
  add_lt_add_le left right.left

/-- Positives add to a positive. -/
public theorem add_positive {left right : selection.Carrier}
    (leftPositive : lt zero left) (rightPositive : lt zero right) :
    lt zero (add left right) := by
  have combined := add_lt_add leftPositive rightPositive
  rwa [add_zero] at combined

/-! ### Ring lemmas the carrier exposes only through its selection -/

/-- Negation passes through a product on the right. -/
public theorem mul_neg (left right : selection.Carrier) :
    mul left (neg right) = neg (mul left right) :=
  multiplicativeSelection.ring.mul_neg left right

/-- Negation passes through a product on the left. -/
public theorem neg_mul (left right : selection.Carrier) :
    mul (neg left) right = neg (mul left right) :=
  multiplicativeSelection.ring.neg_mul left right

/-- A sum distributes into a product on the right. -/
public theorem add_mul (left middle right : selection.Carrier) :
    mul (add left middle) right = add (mul left right) (mul middle right) :=
  multiplicativeSelection.ring.add_mul left middle right

/-- A difference distributes out of a product on the left. -/
public theorem mul_sub (left middle right : selection.Carrier) :
    mul left (sub middle right) = sub (mul left middle) (mul left right) := by
  rw [sub_eq_add_neg, sub_eq_add_neg, mul_add, mul_neg]

/-- A difference distributes into a product on the right. -/
public theorem sub_mul (left middle right : selection.Carrier) :
    mul (sub left middle) right = sub (mul left right) (mul middle right) := by
  rw [sub_eq_add_neg, sub_eq_add_neg, add_mul, neg_mul]

/-- Multiplying by zero on the right vanishes. -/
public theorem mul_zero (value : selection.Carrier) : mul value zero = zero :=
  multiplicativeSelection.ring.mul_zero value

/-- Multiplying by zero on the left vanishes. -/
public theorem zero_mul (value : selection.Carrier) : mul zero value = zero :=
  multiplicativeSelection.ring.zero_mul value

/-- One is a left unit. -/
public theorem one_mul (value : selection.Carrier) : mul one value = value := by
  rw [mul_comm, mul_one]

/-- A value minus itself vanishes. -/
public theorem sub_self (value : selection.Carrier) : sub value value = zero := by
  rw [sub_eq_add_neg, add_neg]

/-- Subtracting zero changes nothing. -/
public theorem sub_zero (value : selection.Carrier) : sub value zero = value := by
  rw [sub_eq_add_neg, neg_zero, add_zero]

/-- Differences chain through an intermediate value. -/
public theorem sub_add_sub (left middle right : selection.Carrier) :
    add (sub left middle) (sub middle right) = sub left right := by
  rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, add_assoc, ← add_assoc (neg middle) middle,
    add_comm (neg middle) middle, add_neg, add_comm zero (neg right), add_zero]

/-- A difference added back recovers the value. -/
public theorem add_sub_cancel (left right : selection.Carrier) :
    add right (sub left right) = left := by
  rw [sub_eq_add_neg, ← add_assoc, add_comm right left, add_assoc, add_neg, add_zero]

/-- A difference added back on the right recovers the value. -/
public theorem sub_add_cancel (left right : selection.Carrier) :
    add (sub left right) right = left := by
  rw [sub_eq_add_neg, add_assoc, add_comm (neg right) right, add_neg, add_zero]

/-- Subtracting the first summand recovers the second. -/
public theorem add_sub_self (left right : selection.Carrier) :
    sub (add left right) left = right := by
  rw [sub_eq_add_neg, add_comm left right, add_assoc, add_neg, add_zero]

/-- Division distributes over a sum in the numerator. -/
public theorem add_div (left middle right : selection.Carrier) :
    div (add left middle) right = add (div left right) (div middle right) := by
  rw [div_eq_mul_inverse, div_eq_mul_inverse, div_eq_mul_inverse, add_mul]

/-- Division distributes over a difference in the numerator. -/
public theorem sub_div (left middle right : selection.Carrier) :
    div (sub left middle) right = sub (div left right) (div middle right) := by
  rw [div_eq_mul_inverse, div_eq_mul_inverse, div_eq_mul_inverse, sub_mul]

/-- A left factor of a numerator leaves the quotient. -/
public theorem mul_div_assoc (left middle right : selection.Carrier) :
    div (mul left middle) right = mul left (div middle right) := by
  rw [div_eq_mul_inverse, div_eq_mul_inverse, mul_assoc]

/-- A right factor of a numerator leaves the quotient. -/
public theorem div_mul_right (left middle right : selection.Carrier) :
    div (mul left middle) right = mul (div left right) middle := by
  rw [div_eq_mul_inverse, div_eq_mul_inverse, mul_assoc, mul_comm middle (inverse right),
    ← mul_assoc]

/-- Negation leaves a quotient through the numerator. -/
public theorem neg_div (left right : selection.Carrier) :
    div (neg left) right = neg (div left right) := by
  rw [div_eq_mul_inverse, div_eq_mul_inverse, neg_mul]

/-- The reciprocal of a product is the product of the reciprocals. -/
public theorem inverse_mul {left right : selection.Carrier}
    (leftNonzero : left ≠ zero) (rightNonzero : right ≠ zero) :
    inverse (mul left right) = mul (inverse left) (inverse right) := by
  have productNonzero : mul left right ≠ zero := by
    intro vanished
    rcases mul_eq_zero_iff.mp vanished with leftZero | rightZero
    · exact leftNonzero leftZero
    · exact rightNonzero rightZero
  apply mul_right_cancel_of_nonzero productNonzero
  rw [inverse_mul_cancel productNonzero]
  symm
  calc mul (mul (inverse left) (inverse right)) (mul left right)
      = mul (mul (inverse left) left) (mul (inverse right) right) := by ac_rfl
    _ = one := by
      rw [inverse_mul_cancel leftNonzero, inverse_mul_cancel rightNonzero, mul_one]

/-- The difference of two reciprocals is a single quotient. -/
public theorem inverse_sub {left right : selection.Carrier}
    (leftNonzero : left ≠ zero) (rightNonzero : right ≠ zero) :
    sub (inverse left) (inverse right) = div (sub right left) (mul left right) := by
  have productNonzero : mul left right ≠ zero := by
    intro vanished
    rcases mul_eq_zero_iff.mp vanished with leftZero | rightZero
    · exact leftNonzero leftZero
    · exact rightNonzero rightZero
  apply mul_right_cancel_of_nonzero productNonzero
  rw [div_mul_cancel _ productNonzero, sub_mul, ← mul_assoc,
    inverse_mul_cancel leftNonzero, one_mul, mul_comm left right, ← mul_assoc,
    inverse_mul_cancel rightNonzero, one_mul]

/-- One is positive. -/
public theorem one_positive : lt zero one :=
  positive_iff_nonnegative_and_nonzero.mpr ⟨one_nonnegative, one_ne_zero⟩

/-- Two negations in a product cancel. -/
public theorem neg_mul_neg (left right : selection.Carrier) :
    mul (neg left) (neg right) = mul left right :=
  multiplicativeSelection.ring.neg_mul_neg left right

/-- Negation exchanges nonnegativity for nonpositivity. -/
public theorem neg_nonnegative_iff {value : selection.Carrier} :
    le zero (neg value) ↔ le value zero := by
  have reflected := neg_le_neg_iff (left := value) (right := zero)
  rwa [neg_zero] at reflected

/-- Negation exchanges positivity for negativity. -/
public theorem neg_positive_iff {value : selection.Carrier} :
    lt zero (neg value) ↔ lt value zero := by
  have reflected := neg_lt_neg_iff (left := value) (right := zero)
  rwa [neg_zero] at reflected

/-- Negation exchanges positivity for negativity, read from the value. -/
public theorem neg_negative_iff {value : selection.Carrier} :
    lt zero value ↔ lt (neg value) zero := by
  have reflected := neg_positive_iff (value := neg value)
  rwa [neg_neg] at reflected

/-- Negation exchanges nonpositivity for nonnegativity. -/
public theorem neg_nonpositive_iff {value : selection.Carrier} :
    le zero value ↔ le (neg value) zero := by
  have reflected := neg_nonnegative_iff (value := neg value)
  rwa [neg_neg] at reflected

/-- Negation distributes over a sum. -/
public theorem neg_add (left right : selection.Carrier) :
    neg (add left right) = add (neg left) (neg right) := by
  apply add_left_cancel (left := add left right)
  calc add (add left right) (neg (add left right))
      = zero := add_neg _
    _ = add zero zero := (add_zero zero).symm
    _ = add (add left (neg left)) (add right (neg right)) := by rw [add_neg, add_neg]
    _ = add (add left right) (add (neg left) (neg right)) := by
      rw [add_assoc, add_assoc, add_left_comm (neg left) right (neg right)]

/-- Negation distributes over a difference, reversing it. -/
public theorem neg_sub (left right : selection.Carrier) :
    neg (sub left right) = sub right left := by
  rw [sub_eq_add_neg, sub_eq_add_neg, neg_add, neg_neg, add_comm]

/-- Negation distributes over a difference termwise. -/
public theorem neg_sub_distrib (left right : selection.Carrier) :
    neg (sub left right) = sub (neg left) (neg right) := by
  rw [neg_sub, sub_eq_add_neg, sub_eq_add_neg, neg_neg, add_comm]

/-- A difference is positive exactly when the order is strict. -/
public theorem sub_positive_iff {left right : selection.Carrier} :
    lt zero (sub right left) ↔ lt left right := by
  rw [sub_eq_add_neg]
  have shifted := add_lt_add_right_iff (left := zero) (right := add right (neg left))
    (shift := left)
  rw [add_comm zero left, add_zero, add_assoc, add_comm (neg left) left, add_neg,
    add_zero] at shifted
  exact shifted.symm

/-- Two positive values admit a positive value below both. -/
public theorem small_positive {left right : selection.Carrier}
    (leftPositive : lt zero left) (rightPositive : lt zero right) :
    ∃ value : selection.Carrier,
      lt zero value ∧ le value left ∧ le value right := by
  rcases le_total left right with smaller | larger
  · exact ⟨left, leftPositive, le_refl left, smaller⟩
  · exact ⟨right, rightPositive, larger, le_refl right⟩

/-- The reciprocal of a negation is the negated reciprocal. -/
public theorem inverse_neg (value : selection.Carrier) :
    inverse (neg value) = neg (inverse value) := by
  classical
  by_cases vanished : value = zero
  · rw [vanished, neg_zero, inverse_zero, neg_zero]
  · have negNonzero : neg value ≠ zero := by
      intro negVanished
      apply vanished
      have := congrArg neg negVanished
      rwa [neg_neg, neg_zero] at this
    apply mul_right_cancel_of_nonzero negNonzero
    rw [inverse_mul_cancel negNonzero, neg_mul_neg,
      inverse_mul_cancel vanished]

/-! ### Constants, signs, and cancellations -/

/-- Two, embedded from the rationals, is positive. -/
public theorem ofRat_two_positive : lt zero (selection.ofRat 2) := by
  rw [← ofRat_zero]
  exact (ofRat_lt_iff 0 2).mpr (by decide)

/-- Every successor, embedded from the rationals, is positive. -/
public theorem ofRat_succ_positive (index : Nat) :
    lt zero (selection.ofRat (index.succ : Rat)) := by
  rw [← ofRat_zero]
  exact (ofRat_lt_iff 0 (index.succ : Rat)).mpr
    (Rat.natCast_pos.mpr (Nat.zero_lt_succ index))

/-- A positive value is nonzero. -/
public theorem nonzero_of_positive {value : selection.Carrier}
    (positive : lt zero value) : value ≠ zero :=
  (positive_iff_nonnegative_and_nonzero.mp positive).2

/-- Two, embedded from the rationals, is nonzero. -/
public theorem ofRat_two_nonzero : selection.ofRat 2 ≠ zero :=
  nonzero_of_positive ofRat_two_positive

/-- One plus one is two. -/
public theorem one_add_one : add one one = selection.ofRat 2 := by
  have rational : (2 : Rat) = 1 + 1 := by decide +kernel
  rw [rational, ofRat_add, ofRat_one]

/-- Equal values are ordered. -/
public theorem le_of_equal {left right : selection.Carrier} (equal : left = right) :
    le left right :=
  equal ▸ le_refl left

/-- By totality, a failed bound is the reverse bound. -/
public theorem le_of_not_le {left right : selection.Carrier}
    (failed : ¬le right left) : le left right :=
  (le_total left right).resolve_right failed

/-- Zero added on the left vanishes. -/
public theorem zero_add (value : selection.Carrier) : add zero value = value := by
  rw [add_comm, add_zero]

/-- Subtracting from zero negates. -/
public theorem zero_sub (value : selection.Carrier) : sub zero value = neg value := by
  rw [sub_eq_add_neg, zero_add]

/-- Subtracting a difference from its minuend leaves the subtrahend. -/
public theorem sub_sub_cancel (value shift : selection.Carrier) :
    sub value (sub value shift) = shift := by
  rw [sub_eq_add_neg, sub_eq_add_neg, neg_add, neg_neg, ← add_assoc, add_neg, zero_add]

/-- A difference of sums is the sum of differences. -/
public theorem add_sub_add_comm (first second third fourth : selection.Carrier) :
    sub (add first third) (add second fourth) =
      add (sub first second) (sub third fourth) := by
  rw [sub_eq_add_neg, neg_add, sub_eq_add_neg, sub_eq_add_neg, add_assoc first third,
    ← add_assoc third, add_comm third (neg second), add_assoc (neg second),
    ← add_assoc first]

/-- An ordered pair has a nonnegative difference. -/
public theorem sub_nonnegative {left right : selection.Carrier}
    (included : le left right) : le zero (sub right left) := by
  have shifted := add_le_add_right_iff (shift := neg left) |>.mpr included
  rwa [add_neg, ← sub_eq_add_neg] at shifted

/-- A sum of nonnegative values is nonnegative. -/
public theorem add_nonnegative {left right : selection.Carrier}
    (leftNonnegative : le zero left) (rightNonnegative : le zero right) :
    le zero (add left right) := by
  have sum := add_le_add leftNonnegative rightNonnegative
  rwa [add_zero] at sum

/-- A square is nonnegative. -/
public theorem mul_self_nonnegative (value : selection.Carrier) :
    le zero (mul value value) := by
  rcases le_total zero value with nonnegative | nonpositive
  · exact mul_nonnegative nonnegative nonnegative
  · have flipped := neg_nonnegative_iff.mpr nonpositive
    have product := mul_nonnegative flipped flipped
    rwa [neg_mul_neg] at product

/-- The middle factors of a product of products swap. -/
public theorem mul_mul_mul_comm (first second third fourth : selection.Carrier) :
    mul (mul first second) (mul third fourth) =
      mul (mul first third) (mul second fourth) := by
  rw [mul_assoc, ← mul_assoc second third, mul_comm second third,
    mul_assoc third second, ← mul_assoc]

/-- The reciprocal of a product is the product of reciprocals, including at
zero, whose reciprocal is zero. -/
public theorem inverse_mul_total (left right : selection.Carrier) :
    inverse (mul left right) = mul (inverse left) (inverse right) := by
  classical
  by_cases leftZero : left = zero
  · rw [leftZero, zero_mul, inverse_zero, zero_mul]
  by_cases rightZero : right = zero
  · rw [rightZero, mul_zero, inverse_zero, mul_zero]
  exact inverse_mul leftZero rightZero

/-- A positive left factor reflects the weak order. -/
public theorem mul_le_mul_left_iff {factor left right : selection.Carrier}
    (positive : lt zero factor) :
    le (mul factor left) (mul factor right) ↔ le left right := by
  constructor
  · intro scaled
    exact Classical.byContradiction fun failed =>
      (mul_lt_mul_positive_left (lt_of_not_le failed) positive).2 scaled
  · intro included
    exact mul_le_mul_nonnegative_left included positive.1

/-- A positive left factor reflects the strict order. -/
public theorem mul_lt_mul_left_iff {factor left right : selection.Carrier}
    (positive : lt zero factor) :
    lt (mul factor left) (mul factor right) ↔ lt left right := by
  constructor
  · intro scaled
    exact ⟨(mul_le_mul_left_iff positive).mp scaled.1,
      fun reversed => scaled.2 ((mul_le_mul_left_iff positive).mpr reversed)⟩
  · intro less
    exact mul_lt_mul_positive_left less positive

/-- Division by a positive value preserves the weak order. -/
public theorem div_le_div_right {left right step : selection.Carrier}
    (positive : lt zero step) (included : le left right) :
    le (div left step) (div right step) := by
  rw [div_eq_mul_inverse, div_eq_mul_inverse]
  exact mul_le_mul_nonnegative_right included (inverse_of_positive_positive positive).left

end Problib.Real.Construction.Dedekind
