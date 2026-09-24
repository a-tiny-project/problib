module

public import Problib.Measure.Real.Interval

set_option autoImplicit false

namespace Problib.Measure.StandardBorel.Real

open Problib.Measure.Real
open Problib.Real.Construction.Dedekind

private theorem one_lt_double : lt one (add one one) := by
  have shifted := (add_lt_add_left_iff (shift := one)).mpr one_positive
  simpa only [add_zero] using shifted

private noncomputable def midpoint : Carrier := inverse (add one one)

private theorem midpoint_positive : lt zero midpoint :=
  inverse_of_positive_positive (add_positive one_positive one_positive)

private theorem midpoint_lt_one : lt midpoint one := by
  have less := inverse_lt_inverse_of_positive one_positive
    (add_positive one_positive one_positive) one_lt_double
  simpa only [midpoint, inverse_one] using less

private theorem midpoint_nonzero : midpoint ≠ zero :=
  (positive_iff_nonnegative_and_nonzero.mp midpoint_positive).right

private theorem midpoint_double : add midpoint midpoint = one := by
  have nonzero := (positive_iff_nonnegative_and_nonzero.mp (add_positive one_positive one_positive)).right
  have cancellation := inverse_mul_cancel nonzero
  simpa only [midpoint, mul_add, mul_one] using cancellation

private noncomputable def reflection (value : Carrier) : Carrier := sub one value

private theorem reflection_zero : reflection zero = one := by
  simp only [reflection, sub_eq_add_neg, neg_zero, add_zero]

private theorem reflection_one : reflection one = zero := by
  simp only [reflection, sub_eq_add_neg, add_neg]

private theorem reflection_involution (value : Carrier) :
    reflection (reflection value) = value := by
  apply add_left_cancel (left := reflection value)
  calc
    add (reflection value) (reflection (reflection value)) = one :=
      add_sub_cancel one (reflection value)
    _ = add (reflection value) value :=
      ((add_comm (reflection value) value).trans (add_sub_cancel one value)).symm

private theorem reflection_midpoint : reflection midpoint = midpoint := by
  apply add_left_cancel (left := midpoint)
  calc
    add midpoint (reflection midpoint) = one := add_sub_cancel one midpoint
    _ = add midpoint midpoint := midpoint_double.symm

private theorem reflection_le {left right : Carrier} (included : le left right) :
    le (reflection right) (reflection left) := by
  simp only [reflection, sub_eq_add_neg]
  exact (add_le_add_left_iff (shift := one)).mpr (neg_le_neg_iff.mpr included)

private theorem reflection_lt {left right : Carrier} (less : lt left right) :
    lt (reflection right) (reflection left) := by
  simp only [reflection, sub_eq_add_neg]
  exact (add_lt_add_left_iff (shift := one)).mpr (neg_lt_neg_iff.mpr less)

private theorem reflection_ge_one {value : Carrier} (nonpositive : le value zero) :
    le one (reflection value) := by
  simpa only [reflection_zero] using reflection_le nonpositive

private noncomputable def contract (value : Carrier) : Carrier :=
  div midpoint (reflection value)

private noncomputable def expand (value : Carrier) : Carrier :=
  reflection (div midpoint value)

private theorem expand_contract (value : Carrier) : expand (contract value) = value := by
  unfold expand contract
  rw [div_div_cancel _ _ midpoint_nonzero, reflection_involution]

private theorem contract_expand (value : Carrier) : contract (expand value) = value := by
  unfold contract expand
  rw [reflection_involution, div_div_cancel _ _ midpoint_nonzero]

private theorem contract_bounds {value : Carrier} (nonpositive : le value zero) :
    Ioc zero midpoint (contract value) := by
  have denominatorLower := reflection_ge_one nonpositive
  have denominatorPositive := lt_of_lt_of_le one_positive denominatorLower
  refine ⟨div_positive midpoint_positive denominatorPositive, ?_⟩
  have bounded := div_le_div_of_positive midpoint_positive.left one_positive denominatorLower
  simpa only [contract, div_one] using bounded

private theorem contract_monotone {left right : Carrier}
    (rightNonpositive : le right zero) (included : le left right) :
    le (contract left) (contract right) :=
  div_le_div_of_positive midpoint_positive.left
    (lt_of_lt_of_le one_positive (reflection_ge_one rightNonpositive))
    (reflection_le included)

private theorem contract_lt_midpoint {value : Carrier} (negative : lt value zero) :
    lt (contract value) midpoint := by
  have denominatorAbove : lt one (reflection value) := by
    simpa only [reflection_zero] using reflection_lt negative
  have below := div_lt_div_of_positive midpoint_positive one_positive denominatorAbove
  simpa only [contract, div_one] using below

private theorem upper_bounds {value : Carrier} (positive : lt zero value) :
    Ioo midpoint one (reflection (contract (neg value))) := by
  have negative : lt (neg value) zero := by
    simpa only [neg_zero] using neg_lt_neg_iff.mpr positive
  have below := contract_lt_midpoint negative
  have bounded := contract_bounds negative.left
  constructor
  · simpa only [reflection_midpoint] using reflection_lt below
  · simpa only [reflection_zero] using reflection_lt bounded.left

private theorem expand_nonpositive {value : Carrier}
    (positive : lt zero value) (included : le value midpoint) :
    le (expand value) zero := by
  have above : le one (div midpoint value) := by
    have bounded := div_le_div_of_positive midpoint_positive.left positive included
    simpa only [div_self midpoint_nonzero] using bounded
  simpa only [expand, reflection_one] using reflection_le above

private theorem expand_negative {value : Carrier}
    (positive : lt zero value) (less : lt value midpoint) :
    lt (expand value) zero := by
  have above : lt one (div midpoint value) := by
    have bounded := div_lt_div_of_positive midpoint_positive positive less
    simpa only [div_self midpoint_nonzero] using bounded
  simpa only [expand, reflection_one] using reflection_lt above

private theorem expand_monotone {left right : Carrier}
    (leftPositive : lt zero left) (included : le left right) :
    le (expand left) (expand right) :=
  reflection_le (div_le_div_of_positive midpoint_positive.left leftPositive included)

private theorem upper_expand_positive {value : Carrier}
    (bounded : Ioo midpoint one value) :
    lt zero (neg (expand (reflection value))) := by
  have reflectedPositive : lt zero (reflection value) := by
    simpa only [reflection_one] using reflection_lt bounded.right
  have reflectedBelow : lt (reflection value) midpoint := by
    simpa only [reflection_midpoint] using reflection_lt bounded.left
  exact neg_positive_of_negative (expand_negative reflectedPositive reflectedBelow)

/-- Order-preserving bijection from the real line into the open unit interval. -/
public noncomputable def encode (value : Carrier) : Carrier := by
  classical
  exact if le value zero then contract value else reflection (contract (neg value))

/-- Inverse order-preserving bijection from the open unit interval to the real line. -/
public noncomputable def decode (value : Carrier) : Carrier := by
  classical
  exact if le value midpoint then expand value else neg (expand (reflection value))

/-- The encoded coordinate of any real number lies in the open unit interval. -/
public theorem encode_mem (value : Carrier) : Ioo zero one (encode value) := by
  classical
  by_cases nonpositive : le value zero
  · have bounded := contract_bounds nonpositive
    simp only [encode, if_pos nonpositive]
    exact ⟨bounded.left, lt_of_le_of_lt bounded.right midpoint_lt_one⟩
  · have bounded := upper_bounds (not_le_iff_lt.mp nonpositive)
    simp only [encode, if_neg nonpositive]
    exact ⟨lt_trans midpoint_positive bounded.left, bounded.right⟩

/-- Decoding an encoded real number recovers the original value. -/
public theorem decode_encode (value : Carrier) : decode (encode value) = value := by
  classical
  by_cases nonpositive : le value zero
  · have bounded := contract_bounds nonpositive
    simp only [encode, if_pos nonpositive, decode, if_pos bounded.right,
      expand_contract]
  · have bounded := upper_bounds (not_le_iff_lt.mp nonpositive)
    simp only [encode, if_neg nonpositive, decode, if_neg bounded.left.right,
      reflection_involution, expand_contract, neg_neg]

/-- Encoding a decoded coordinate in the open unit interval recovers the coordinate. -/
public theorem encode_decode (value : Carrier) (member : Ioo zero one value) :
    encode (decode value) = value := by
  classical
  by_cases below : le value midpoint
  · have nonpositive := expand_nonpositive member.left below
    simp only [decode, if_pos below, encode, if_pos nonpositive, contract_expand]
  · have positive := upper_expand_positive ⟨not_le_iff_lt.mp below, member.right⟩
    simp only [decode, if_neg below, encode, if_neg positive.right,
      neg_neg, contract_expand, reflection_involution]

/-- Monotonicity of the real line coordinate encoder. -/
public theorem encode_monotone {left right : Carrier} (included : le left right) :
    le (encode left) (encode right) := by
  classical
  by_cases rightNonpositive : le right zero
  · have leftNonpositive := le_trans included rightNonpositive
    simp only [encode, if_pos leftNonpositive, if_pos rightNonpositive]
    exact contract_monotone rightNonpositive included
  · by_cases leftNonpositive : le left zero
    · have lower := contract_bounds leftNonpositive
      have upper := upper_bounds (not_le_iff_lt.mp rightNonpositive)
      simp only [encode, if_pos leftNonpositive, if_neg rightNonpositive]
      exact le_trans lower.right upper.left.left
    · have reflectedLeft : le (neg left) zero := by
        simpa only [neg_zero] using
          neg_le_neg_iff.mpr (not_le_iff_lt.mp leftNonpositive).left
      simp only [encode, if_neg leftNonpositive, if_neg rightNonpositive]
      exact reflection_le
        (contract_monotone reflectedLeft (neg_le_neg_iff.mpr included))

/-- Monotonicity of the real line coordinate decoder on the open unit interval. -/
public theorem decode_monotone {left right : Carrier}
    (leftMember : Ioo zero one left) (rightMember : Ioo zero one right)
    (included : le left right) : le (decode left) (decode right) := by
  classical
  by_cases rightBelow : le right midpoint
  · have leftBelow := le_trans included rightBelow
    simp only [decode, if_pos leftBelow, if_pos rightBelow]
    exact expand_monotone leftMember.left included
  · by_cases leftBelow : le left midpoint
    · have lower := expand_nonpositive leftMember.left leftBelow
      have upper := upper_expand_positive ⟨not_le_iff_lt.mp rightBelow, rightMember.right⟩
      simp only [decode, if_pos leftBelow, if_neg rightBelow]
      exact le_trans lower upper.left
    · have reflectedPositive : lt zero (reflection right) := by
        simpa only [reflection_one] using reflection_lt rightMember.right
      simp only [decode, if_neg leftBelow, if_neg rightBelow]
      exact neg_le_neg_iff.mpr (expand_monotone reflectedPositive (reflection_le included))

end Problib.Measure.StandardBorel.Real
