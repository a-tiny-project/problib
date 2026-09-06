module

public import Foundations.Measure.Real.Interval

set_option autoImplicit false

namespace Foundations.Measure.StandardBorel.Real

open Foundations.Measure.Real
open Foundations.Real.Construction.Dedekind

private theorem one_positive : lt zero one :=
  positiveIffNonnegativeAndNonzero.mpr ⟨oneNonnegative, oneNeZero⟩

private theorem one_lt_double : lt one (add one one) := by
  have shifted := (addLtAddLeftIff (shift := one)).mpr one_positive
  simpa only [addZero] using shifted

private theorem double_positive : lt zero (add one one) :=
  ltTrans one_positive one_lt_double

private noncomputable def midpoint : Carrier := inverse (add one one)

private theorem midpoint_positive : lt zero midpoint :=
  inverseOfPositivePositive double_positive

private theorem midpoint_lt_one : lt midpoint one := by
  have less := inverseLtInverseOfPositive one_positive double_positive one_lt_double
  simpa only [midpoint, inverseOne] using less

private theorem midpoint_nonzero : midpoint ≠ zero :=
  (positiveIffNonnegativeAndNonzero.mp midpoint_positive).right

private theorem midpoint_double : add midpoint midpoint = one := by
  have nonzero := (positiveIffNonnegativeAndNonzero.mp double_positive).right
  have cancellation := inverseMulCancel nonzero
  simpa only [midpoint, mulAdd, mulOne] using cancellation

private noncomputable def reflection (value : Carrier) : Carrier := sub one value

private theorem reflection_zero : reflection zero = one := by
  simp only [reflection, subEqAddNeg, negZero, addZero]

private theorem reflection_one : reflection one = zero := by
  simp only [reflection, subEqAddNeg, addNeg]

private theorem reflection_involution (value : Carrier) :
    reflection (reflection value) = value := by
  apply addLeftCancel (left := reflection value)
  calc
    add (reflection value) (reflection (reflection value)) = one :=
      addSubCancel one (reflection value)
    _ = add (reflection value) value :=
      ((addComm (reflection value) value).trans (addSubCancel one value)).symm

private theorem reflection_midpoint : reflection midpoint = midpoint := by
  apply addLeftCancel (left := midpoint)
  calc
    add midpoint (reflection midpoint) = one := addSubCancel one midpoint
    _ = add midpoint midpoint := midpoint_double.symm

private theorem reflection_le {left right : Carrier} (included : le left right) :
    le (reflection right) (reflection left) := by
  simp only [reflection, subEqAddNeg]
  exact (addLeAddLeftIff (shift := one)).mpr (negLeNegIff.mpr included)

private theorem reflection_lt {left right : Carrier} (less : lt left right) :
    lt (reflection right) (reflection left) := by
  simp only [reflection, subEqAddNeg]
  exact (addLtAddLeftIff (shift := one)).mpr (negLtNegIff.mpr less)

private theorem reflection_ge_one {value : Carrier} (nonpositive : le value zero) :
    le one (reflection value) := by
  simpa only [reflection_zero] using reflection_le nonpositive

private noncomputable def contract (value : Carrier) : Carrier :=
  div midpoint (reflection value)

private noncomputable def expand (value : Carrier) : Carrier :=
  reflection (div midpoint value)

private theorem expand_contract (value : Carrier) : expand (contract value) = value := by
  unfold expand contract
  rw [divDivCancel _ _ midpoint_nonzero, reflection_involution]

private theorem contract_expand (value : Carrier) : contract (expand value) = value := by
  unfold contract expand
  rw [reflection_involution, divDivCancel _ _ midpoint_nonzero]

private theorem contract_bounds {value : Carrier} (nonpositive : le value zero) :
    Ioc zero midpoint (contract value) := by
  have denominatorLower := reflection_ge_one nonpositive
  have denominatorPositive := ltOfLtOfLe one_positive denominatorLower
  refine ⟨divPositive midpoint_positive denominatorPositive, ?_⟩
  have bounded := divLeDivOfPositive midpoint_positive.left one_positive denominatorLower
  simpa only [contract, divOne] using bounded

private theorem contract_monotone {left right : Carrier}
    (rightNonpositive : le right zero) (included : le left right) :
    le (contract left) (contract right) :=
  divLeDivOfPositive midpoint_positive.left
    (ltOfLtOfLe one_positive (reflection_ge_one rightNonpositive))
    (reflection_le included)

private theorem contract_lt_midpoint {value : Carrier} (negative : lt value zero) :
    lt (contract value) midpoint := by
  have denominatorAbove : lt one (reflection value) := by
    simpa only [reflection_zero] using reflection_lt negative
  have below := divLtDivOfPositive midpoint_positive one_positive denominatorAbove
  simpa only [contract, divOne] using below

private theorem upper_bounds {value : Carrier} (positive : lt zero value) :
    Ioo midpoint one (reflection (contract (neg value))) := by
  have negative : lt (neg value) zero := by
    simpa only [negZero] using negLtNegIff.mpr positive
  have below := contract_lt_midpoint negative
  have bounded := contract_bounds negative.left
  constructor
  · simpa only [reflection_midpoint] using reflection_lt below
  · simpa only [reflection_zero] using reflection_lt bounded.left

private theorem expand_nonpositive {value : Carrier}
    (positive : lt zero value) (included : le value midpoint) :
    le (expand value) zero := by
  have above : le one (div midpoint value) := by
    have bounded := divLeDivOfPositive midpoint_positive.left positive included
    simpa only [divSelf midpoint_nonzero] using bounded
  simpa only [expand, reflection_one] using reflection_le above

private theorem expand_negative {value : Carrier}
    (positive : lt zero value) (less : lt value midpoint) :
    lt (expand value) zero := by
  have above : lt one (div midpoint value) := by
    have bounded := divLtDivOfPositive midpoint_positive positive less
    simpa only [divSelf midpoint_nonzero] using bounded
  simpa only [expand, reflection_one] using reflection_lt above

private theorem expand_monotone {left right : Carrier}
    (leftPositive : lt zero left) (included : le left right) :
    le (expand left) (expand right) :=
  reflection_le (divLeDivOfPositive midpoint_positive.left leftPositive included)

private theorem upper_expand_positive {value : Carrier}
    (bounded : Ioo midpoint one value) :
    lt zero (neg (expand (reflection value))) := by
  have reflectedPositive : lt zero (reflection value) := by
    simpa only [reflection_one] using reflection_lt bounded.right
  have reflectedBelow : lt (reflection value) midpoint := by
    simpa only [reflection_midpoint] using reflection_lt bounded.left
  exact negPositiveOfNegative (expand_negative reflectedPositive reflectedBelow)

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
    exact ⟨bounded.left, ltOfLeOfLt bounded.right midpoint_lt_one⟩
  · have bounded := upper_bounds (notLeIffLt.mp nonpositive)
    simp only [encode, if_neg nonpositive]
    exact ⟨ltTrans midpoint_positive bounded.left, bounded.right⟩

/-- Decoding an encoded real number recovers the original value. -/
public theorem decode_encode (value : Carrier) : decode (encode value) = value := by
  classical
  by_cases nonpositive : le value zero
  · have bounded := contract_bounds nonpositive
    simp only [encode, if_pos nonpositive, decode, if_pos bounded.right,
      expand_contract]
  · have bounded := upper_bounds (notLeIffLt.mp nonpositive)
    simp only [encode, if_neg nonpositive, decode, if_neg bounded.left.right,
      reflection_involution, expand_contract, negNeg]

/-- Encoding a decoded coordinate in the open unit interval recovers the coordinate. -/
public theorem encode_decode (value : Carrier) (member : Ioo zero one value) :
    encode (decode value) = value := by
  classical
  by_cases below : le value midpoint
  · have nonpositive := expand_nonpositive member.left below
    simp only [decode, if_pos below, encode, if_pos nonpositive, contract_expand]
  · have positive := upper_expand_positive ⟨notLeIffLt.mp below, member.right⟩
    simp only [decode, if_neg below, encode, if_neg positive.right,
      negNeg, contract_expand, reflection_involution]

/-- Monotonicity of the real line coordinate encoder. -/
public theorem encode_monotone {left right : Carrier} (included : le left right) :
    le (encode left) (encode right) := by
  classical
  by_cases rightNonpositive : le right zero
  · have leftNonpositive := leTrans included rightNonpositive
    simp only [encode, if_pos leftNonpositive, if_pos rightNonpositive]
    exact contract_monotone rightNonpositive included
  · by_cases leftNonpositive : le left zero
    · have lower := contract_bounds leftNonpositive
      have upper := upper_bounds (notLeIffLt.mp rightNonpositive)
      simp only [encode, if_pos leftNonpositive, if_neg rightNonpositive]
      exact leTrans lower.right upper.left.left
    · have reflectedLeft : le (neg left) zero := by
        simpa only [negZero] using
          negLeNegIff.mpr (notLeIffLt.mp leftNonpositive).left
      simp only [encode, if_neg leftNonpositive, if_neg rightNonpositive]
      exact reflection_le
        (contract_monotone reflectedLeft (negLeNegIff.mpr included))

/-- Monotonicity of the real line coordinate decoder on the open unit interval. -/
public theorem decode_monotone {left right : Carrier}
    (leftMember : Ioo zero one left) (rightMember : Ioo zero one right)
    (included : le left right) : le (decode left) (decode right) := by
  classical
  by_cases rightBelow : le right midpoint
  · have leftBelow := leTrans included rightBelow
    simp only [decode, if_pos leftBelow, if_pos rightBelow]
    exact expand_monotone leftMember.left included
  · by_cases leftBelow : le left midpoint
    · have lower := expand_nonpositive leftMember.left leftBelow
      have upper := upper_expand_positive ⟨notLeIffLt.mp rightBelow, rightMember.right⟩
      simp only [decode, if_pos leftBelow, if_neg rightBelow]
      exact leTrans lower upper.left
    · have reflectedPositive : lt zero (reflection right) := by
        simpa only [reflection_one] using reflection_lt rightMember.right
      simp only [decode, if_neg leftBelow, if_neg rightBelow]
      exact negLeNegIff.mpr (expand_monotone reflectedPositive (reflection_le included))

end Foundations.Measure.StandardBorel.Real
