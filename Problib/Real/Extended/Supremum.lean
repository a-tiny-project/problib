module

public import Problib.Real.Extended.Multiplication

namespace Problib.Real.ENNReal

set_option autoImplicit false

private noncomputable def divideBy (upper : ENNReal) (factor : NNReal) :
    ENNReal :=
  match upper with
  | .finite value => .finite (NNReal.div value factor)
  | .top => top

private theorem mul_divideBy (upper : ENNReal) {factor : NNReal}
    (factorPositive : NNReal.lt NNReal.zero factor) :
    mul (finite factor) (divideBy upper factor) = upper := by
  have factorNonzero := (NNReal.zero_lt_iff_ne_zero factor).mp factorPositive
  cases upper with
  | top => exact finite_mul_top_of_ne_zero factorNonzero
  | finite value =>
      exact congrArg finite (NNReal.mul_div_cancel value factorNonzero)

private theorem mul_le_iff_le_divideBy {factor : NNReal}
    (factorPositive : NNReal.lt NNReal.zero factor)
    (value upper : ENNReal) :
    le (mul (finite factor) value) upper ↔
      le value (divideBy upper factor) := by
  have factorNonzero := (NNReal.zero_lt_iff_ne_zero factor).mp factorPositive
  cases upper with
  | top => exact ⟨fun _ => le_top _, fun _ => le_top _⟩
  | finite upperValue =>
      cases value with
      | top =>
          unfold divideBy
          rw [finite_mul_top_of_ne_zero factorNonzero]
          exact ⟨False.elim, False.elim⟩
      | finite valueValue =>
          unfold divideBy
          rw [finite_mul_finite]
          constructor
          · intro included
            apply NNReal.le_of_mul_le_mul_left factorPositive
            rw [NNReal.mul_div_cancel upperValue factorNonzero]
            exact included
          · intro included
            have scaled := NNReal.mul_le_mul_left included factor
            rw [NNReal.mul_div_cancel upperValue factorNonzero] at scaled
            exact scaled

public theorem mul_supremum_of_finite_positive (factor : NNReal)
    (factorPositive : NNReal.lt NNReal.zero factor)
    (set : ENNReal → Prop) :
    mul (finite factor) (supremum set) =
      supremum (image (mul (finite factor)) set) := by
  apply le_antisymm
  · apply (mul_le_iff_le_divideBy factorPositive _ _).mpr
    apply supremum_le
    intro value member
    apply (mul_le_iff_le_divideBy factorPositive _ _).mp
    exact le_supremum ⟨value, member, rfl⟩
  · apply supremum_le
    intro result member
    rcases member with ⟨value, valueMember, rfl⟩
    exact mul_le_mul_left (le_supremum valueMember) (finite factor)

public theorem mul_supremum (factor : ENNReal) (set : ENNReal → Prop) :
    mul factor (supremum set) =
      supremum (image (mul factor) set) := by
  cases factor with
  | finite factorValue =>
      rcases NNReal.eq_zero_or_zero_lt factorValue with factorZero | factorPositive
      · subst factorValue
        have imageZero : supremum (image (mul zero) set) = zero := by
          apply supremum_eq_zero_iff.mpr
          intro result member
          rcases member with ⟨value, valueMember, rfl⟩
          exact zero_mul value
        rw [show finite NNReal.zero = zero from rfl, zero_mul, imageZero]
      · exact mul_supremum_of_finite_positive factorValue factorPositive set
  | top =>
      by_cases supremumZero : supremum set = zero
      · have allZero := supremum_eq_zero_iff.mp supremumZero
        have imageZero : supremum (image (mul top) set) = zero := by
          apply supremum_eq_zero_iff.mpr
          intro result member
          rcases member with ⟨value, valueMember, rfl⟩
          rw [allZero value valueMember, mul_zero]
        rw [supremumZero, mul_zero, imageZero]
      · have positive : lt zero (supremum set) :=
          zero_lt_iff_ne_zero.mpr supremumZero
        rcases exists_greater_of_lt_supremum positive with
          ⟨value, valueMember, valuePositive⟩
        have valueNonzero := zero_lt_iff_ne_zero.mp valuePositive
        have imageTop : image (mul top) set top :=
          ⟨value, valueMember, (top_mul_of_ne_zero valueNonzero).symm⟩
        rw [top_mul_of_ne_zero supremumZero,
          supremum_eq_top_of_member imageTop]

public theorem mul_supremum_right (set : ENNReal → Prop) (factor : ENNReal) :
    mul (supremum set) factor =
      supremum (image (fun value => mul value factor) set) := by
  rw [mul_comm, mul_supremum]
  apply congrArg supremum
  funext result
  apply propext
  constructor
  · rintro ⟨value, member, rfl⟩
    exact ⟨value, member, mul_comm factor value⟩
  · rintro ⟨value, member, rfl⟩
    exact ⟨value, member, mul_comm value factor⟩

public theorem mul_iSup (factor : ENNReal) (values : Nat → ENNReal) :
    mul factor (iSup values) = iSup (fun index => mul factor (values index)) := by
  unfold iSup
  rw [mul_supremum]
  apply congrArg supremum
  funext result
  apply propext
  constructor
  · rintro ⟨value, ⟨index, rfl⟩, rfl⟩
    exact ⟨index, rfl⟩
  · rintro ⟨index, rfl⟩
    exact ⟨values index, ⟨index, rfl⟩, rfl⟩

end Problib.Real.ENNReal
