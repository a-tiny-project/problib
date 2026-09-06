module

public import Foundations.Real.Extended.Additive

set_option autoImplicit false

namespace Foundations.Real.ENNReal

/-- Adding an extended-nonnegative constant distributes over the infimum of an
arbitrary predicate. -/
public theorem addInfimum (factor : ENNReal) (set : ENNReal → Prop) :
    add factor (infimum set) = infimum (image (add factor) set) := by
  apply leAntisymm
  · apply leInfimum
    rintro value ⟨before, member, rfl⟩
    exact addLeAddLeft (infimumLe member) factor
  · have included : le (sub (infimum (image (add factor) set)) factor)
        (infimum set) := by
      apply leInfimum
      intro value member
      apply subLeIffLeAdd.mpr
      rw [addComm value factor]
      exact infimumLe ⟨value, member, rfl⟩
    have shifted := addLeAddRight included factor
    rw [addComm (infimum set) factor] at shifted
    exact leTrans (leSubAdd _ factor) shifted

/-- Adding an extended-nonnegative constant distributes over an indexed
infimum. -/
public theorem addIInf (factor : ENNReal) (values : Nat → ENNReal) :
    add factor (iInf values) = iInf (fun index => add factor (values index)) := by
  unfold iInf
  rw [addInfimum]
  apply congrArg infimum
  funext result
  apply propext
  constructor
  · rintro ⟨value, ⟨index, rfl⟩, rfl⟩
    exact ⟨index, rfl⟩
  · rintro ⟨index, rfl⟩
    exact ⟨values index, ⟨index, rfl⟩, rfl⟩

/-- The infimum of the sum of two antitone sequences in the extended
nonnegative reals equals the sum of their individual infima. -/
public theorem iInfDiagonalAdd (left right : Nat → ENNReal)
    (leftAntitone : ∀ {first second}, first ≤ second → le (left second) (left first))
    (rightAntitone : ∀ {first second}, first ≤ second → le (right second) (right first)) :
    iInf (fun index => add (left index) (right index)) =
      add (iInf left) (iInf right) := by
  apply leAntisymm
  · rw [addIInf]
    apply leIInf
    intro rightIndex
    rw [addComm (iInf left) (right rightIndex), addIInf]
    apply leIInf
    intro leftIndex
    rw [addComm (right rightIndex) (left leftIndex)]
    exact leTrans
      (iInfLe (fun index => add (left index) (right index))
        (Nat.max leftIndex rightIndex))
      (addLeAdd
        (leftAntitone (Nat.le_max_left _ _))
        (rightAntitone (Nat.le_max_right _ _)))
  · apply leIInf
    intro index
    exact addLeAdd (iInfLe left index) (iInfLe right index)

/-- Subtraction from a fixed scalar converts an arbitrary predicate infimum
into a supremum of differences without finiteness hypotheses. -/
public theorem subInfimum (factor : ENNReal) (values : ENNReal → Prop) :
    sub factor (infimum values) =
      supremum (image (sub factor) values) := by
  apply leAntisymm
  · apply subLeIffLeAdd.mpr
    rw [addInfimum]
    apply leInfimum
    rintro _ ⟨value, member, rfl⟩
    exact subLeIffLeAdd.mp (leSupremum ⟨value, member, rfl⟩)
  · apply supremumLe
    rintro _ ⟨value, member, rfl⟩
    exact subLeSubLeft (infimumLe member) factor

/-- Subtraction from a fixed scalar converts an indexed countable infimum
into a supremum of differences without finiteness hypotheses. -/
public theorem subIInf (factor : ENNReal) (values : Nat → ENNReal) :
    sub factor (iInf values) = iSup (fun index => sub factor (values index)) := by
  unfold iInf iSup
  rw [subInfimum]
  apply congrArg supremum
  funext result
  apply propext
  constructor
  · rintro ⟨value, ⟨index, rfl⟩, rfl⟩
    exact ⟨index, rfl⟩
  · rintro ⟨index, rfl⟩
    exact ⟨values index, ⟨index, rfl⟩, rfl⟩

end Foundations.Real.ENNReal
