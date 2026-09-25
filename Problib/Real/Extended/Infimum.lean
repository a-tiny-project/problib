module

public import Problib.Real.Extended.Additive

set_option autoImplicit false

namespace Problib.Real.ENNReal

/-- Adding an extended-nonnegative constant distributes over the infimum of an
arbitrary predicate. -/
public theorem add_infimum (factor : ENNReal) (set : ENNReal → Prop) :
    add factor (infimum set) = infimum (image (add factor) set) := by
  apply le_antisymm
  · apply le_infimum
    rintro value ⟨before, member, rfl⟩
    exact add_le_add_left (infimum_le member) factor
  · have included : le (sub (infimum (image (add factor) set)) factor)
        (infimum set) := by
      apply le_infimum
      intro value member
      apply sub_le_iff_le_add.mpr
      rw [add_comm value factor]
      exact infimum_le ⟨value, member, rfl⟩
    have shifted := add_le_add_right included factor
    rw [add_comm (infimum set) factor] at shifted
    exact le_trans (le_sub_add _ factor) shifted

/-- Adding an extended-nonnegative constant distributes over an indexed
infimum. -/
public theorem add_iInf (factor : ENNReal) (values : Nat → ENNReal) :
    add factor (iInf values) = iInf (fun index => add factor (values index)) := by
  unfold iInf
  rw [add_infimum]
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
public theorem iInf_diagonal_add (left right : Nat → ENNReal)
    (leftAntitone : ∀ {first second}, first ≤ second → le (left second) (left first))
    (rightAntitone : ∀ {first second}, first ≤ second → le (right second) (right first)) :
    iInf (fun index => add (left index) (right index)) =
      add (iInf left) (iInf right) := by
  apply le_antisymm
  · rw [add_iInf]
    apply le_iInf
    intro rightIndex
    rw [add_comm (iInf left) (right rightIndex), add_iInf]
    apply le_iInf
    intro leftIndex
    rw [add_comm (right rightIndex) (left leftIndex)]
    exact le_trans
      (iInf_le (fun index => add (left index) (right index))
        (Nat.max leftIndex rightIndex))
      (add_le_add
        (leftAntitone (Nat.le_max_left _ _))
        (rightAntitone (Nat.le_max_right _ _)))
  · apply le_iInf
    intro index
    exact add_le_add (iInf_le left index) (iInf_le right index)

/-- Subtraction from a fixed scalar converts an arbitrary predicate infimum
into a supremum of differences without finiteness hypotheses. -/
public theorem sub_infimum (factor : ENNReal) (values : ENNReal → Prop) :
    sub factor (infimum values) =
      supremum (image (sub factor) values) := by
  apply le_antisymm
  · apply sub_le_iff_le_add.mpr
    rw [add_infimum]
    apply le_infimum
    rintro _ ⟨value, member, rfl⟩
    exact sub_le_iff_le_add.mp (le_supremum ⟨value, member, rfl⟩)
  · apply supremum_le
    rintro _ ⟨value, member, rfl⟩
    exact sub_le_sub_left (infimum_le member) factor

/-- Subtraction from a fixed scalar converts an indexed countable infimum
into a supremum of differences without finiteness hypotheses. -/
public theorem sub_iInf (factor : ENNReal) (values : Nat → ENNReal) :
    sub factor (iInf values) = iSup (fun index => sub factor (values index)) := by
  unfold iInf iSup
  rw [sub_infimum]
  apply congrArg supremum
  funext result
  apply propext
  constructor
  · rintro ⟨value, ⟨index, rfl⟩, rfl⟩
    exact ⟨index, rfl⟩
  · rintro ⟨index, rfl⟩
    exact ⟨values index, ⟨index, rfl⟩, rfl⟩

end Problib.Real.ENNReal
