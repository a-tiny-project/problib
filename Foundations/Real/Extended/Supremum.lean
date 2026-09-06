module

public import Foundations.Real.Extended.Multiplication

namespace Foundations.Real.ENNReal

set_option autoImplicit false

private noncomputable def divideBy (upper : ENNReal) (factor : NNReal) :
    ENNReal :=
  match upper with
  | .finite value => .finite (NNReal.div value factor)
  | .top => top

private theorem mulDivideBy (upper : ENNReal) {factor : NNReal}
    (factorPositive : NNReal.lt NNReal.zero factor) :
    mul (finite factor) (divideBy upper factor) = upper := by
  have factorNonzero := (NNReal.zeroLtIffNeZero factor).mp factorPositive
  cases upper with
  | top => exact finiteMulTopOfNeZero factorNonzero
  | finite value =>
      exact congrArg finite (NNReal.mulDivCancel value factorNonzero)

private theorem mulLeIffLeDivideBy {factor : NNReal}
    (factorPositive : NNReal.lt NNReal.zero factor)
    (value upper : ENNReal) :
    le (mul (finite factor) value) upper ↔
      le value (divideBy upper factor) := by
  have factorNonzero := (NNReal.zeroLtIffNeZero factor).mp factorPositive
  cases upper with
  | top => exact ⟨fun _ => leTop _, fun _ => leTop _⟩
  | finite upperValue =>
      cases value with
      | top =>
          unfold divideBy
          rw [finiteMulTopOfNeZero factorNonzero]
          exact ⟨False.elim, False.elim⟩
      | finite valueValue =>
          unfold divideBy
          rw [finiteMulFinite]
          constructor
          · intro included
            apply NNReal.leOfMulLeMulLeft factorPositive
            rw [NNReal.mulDivCancel upperValue factorNonzero]
            exact included
          · intro included
            have scaled := NNReal.mulLeMulLeft included factor
            rw [NNReal.mulDivCancel upperValue factorNonzero] at scaled
            exact scaled

public theorem mulSupremumOfFinitePositive (factor : NNReal)
    (factorPositive : NNReal.lt NNReal.zero factor)
    (set : ENNReal → Prop) :
    mul (finite factor) (supremum set) =
      supremum (image (mul (finite factor)) set) := by
  apply leAntisymm
  · apply (mulLeIffLeDivideBy factorPositive _ _).mpr
    apply supremumLe
    intro value member
    apply (mulLeIffLeDivideBy factorPositive _ _).mp
    exact leSupremum ⟨value, member, rfl⟩
  · apply supremumLe
    intro result member
    rcases member with ⟨value, valueMember, rfl⟩
    exact mulLeMulLeft (leSupremum valueMember) (finite factor)

public theorem mulSupremum (factor : ENNReal) (set : ENNReal → Prop) :
    mul factor (supremum set) =
      supremum (image (mul factor) set) := by
  cases factor with
  | finite factorValue =>
      rcases NNReal.eqZeroOrZeroLt factorValue with factorZero | factorPositive
      · subst factorValue
        have imageZero : supremum (image (mul zero) set) = zero := by
          apply supremumEqZeroIff.mpr
          intro result member
          rcases member with ⟨value, valueMember, rfl⟩
          exact zeroMul value
        rw [show finite NNReal.zero = zero from rfl, zeroMul, imageZero]
      · exact mulSupremumOfFinitePositive factorValue factorPositive set
  | top =>
      by_cases supremumZero : supremum set = zero
      · have allZero := supremumEqZeroIff.mp supremumZero
        have imageZero : supremum (image (mul top) set) = zero := by
          apply supremumEqZeroIff.mpr
          intro result member
          rcases member with ⟨value, valueMember, rfl⟩
          rw [allZero value valueMember, mulZero]
        rw [supremumZero, mulZero, imageZero]
      · have positive : lt zero (supremum set) :=
          zeroLtIffNeZero.mpr supremumZero
        rcases existsGreaterOfLtSupremum positive with
          ⟨value, valueMember, valuePositive⟩
        have valueNonzero := zeroLtIffNeZero.mp valuePositive
        have imageTop : image (mul top) set top :=
          ⟨value, valueMember, (topMulOfNeZero valueNonzero).symm⟩
        rw [topMulOfNeZero supremumZero,
          supremumEqTopOfMember imageTop]

public theorem mulSupremumRight (set : ENNReal → Prop) (factor : ENNReal) :
    mul (supremum set) factor =
      supremum (image (fun value => mul value factor) set) := by
  rw [mulComm, mulSupremum]
  apply congrArg supremum
  funext result
  apply propext
  constructor
  · rintro ⟨value, member, rfl⟩
    exact ⟨value, member, mulComm factor value⟩
  · rintro ⟨value, member, rfl⟩
    exact ⟨value, member, mulComm value factor⟩

public theorem mulISup (factor : ENNReal) (values : Nat → ENNReal) :
    mul factor (iSup values) = iSup (fun index => mul factor (values index)) := by
  unfold iSup
  rw [mulSupremum]
  apply congrArg supremum
  funext result
  apply propext
  constructor
  · rintro ⟨value, ⟨index, rfl⟩, rfl⟩
    exact ⟨index, rfl⟩
  · rintro ⟨index, rfl⟩
    exact ⟨values index, ⟨index, rfl⟩, rfl⟩

end Foundations.Real.ENNReal
