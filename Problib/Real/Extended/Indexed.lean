module

public import Problib.Real.Extended.Order

namespace Problib.Real.ENNReal

set_option autoImplicit false

@[expose] public def image (transform : ENNReal → ENNReal)
    (set : ENNReal → Prop) (result : ENNReal) : Prop :=
  ∃ value, set value ∧ result = transform value

@[expose] public noncomputable def iSup (values : Nat → ENNReal) : ENNReal :=
  supremum (fun value => ∃ index, value = values index)

public theorem le_iSup (values : Nat → ENNReal) (index : Nat) :
    le (values index) (iSup values) := by
  unfold iSup
  exact le_supremum ⟨index, rfl⟩

public theorem iSup_le {values : Nat → ENNReal} {upper : ENNReal}
    (isUpper : ∀ index, le (values index) upper) :
    le (iSup values) upper := by
  unfold iSup
  apply supremum_le
  rintro value ⟨index, equal⟩
  rw [equal]
  exact isUpper index

public theorem iSup_le_iff {values : Nat → ENNReal} {upper : ENNReal} :
    le (iSup values) upper ↔ ∀ index, le (values index) upper := by
  constructor
  · intro supremumUpper index
    exact le_trans (le_iSup values index) supremumUpper
  · exact iSup_le

public theorem iSup_mono {left right : Nat → ENNReal}
    (included : ∀ index, le (left index) (right index)) :
    le (iSup left) (iSup right) := by
  apply iSup_le
  intro index
  exact le_trans (included index) (le_iSup right index)

public theorem iSup_const (value : ENNReal) :
    iSup (fun _ => value) = value := by
  apply le_antisymm
  · apply iSup_le
    intro index
    exact le_refl value
  · exact le_iSup (fun _ => value) 0

public theorem exists_index_greater_of_lt_iSup {values : Nat → ENNReal}
    {lower : ENNReal} (less : lt lower (iSup values)) :
    ∃ index, lt lower (values index) := by
  unfold iSup at less
  rcases exists_greater_of_lt_supremum less with
    ⟨value, ⟨index, equal⟩, greater⟩
  exact ⟨index, equal ▸ greater⟩

@[expose] public noncomputable def iInf (values : Nat → ENNReal) : ENNReal :=
  infimum (fun value => ∃ index, value = values index)

public theorem iInf_le (values : Nat → ENNReal) (index : Nat) :
    le (iInf values) (values index) := by
  unfold iInf
  exact infimum_le ⟨index, rfl⟩

public theorem le_iInf {values : Nat → ENNReal} {lower : ENNReal}
    (isLower : ∀ index, le lower (values index)) :
    le lower (iInf values) := by
  unfold iInf
  apply le_infimum
  rintro value ⟨index, equal⟩
  rw [equal]
  exact isLower index

public theorem le_iInf_iff {values : Nat → ENNReal} {lower : ENNReal} :
    le lower (iInf values) ↔ ∀ index, le lower (values index) := by
  constructor
  · intro lowerInfimum index
    exact le_trans lowerInfimum (iInf_le values index)
  · exact le_iInf

public theorem iInf_mono {left right : Nat → ENNReal}
    (included : ∀ index, le (left index) (right index)) :
    le (iInf left) (iInf right) := by
  apply le_iInf
  intro index
  exact le_trans (iInf_le left index) (included index)

public theorem iInf_const (value : ENNReal) :
    iInf (fun _ => value) = value := by
  apply le_antisymm
  · exact iInf_le (fun _ => value) 0
  · apply le_iInf
    intro index
    exact le_refl value

public theorem exists_index_less_of_iInf_lt {values : Nat → ENNReal}
    {upper : ENNReal} (less : lt (iInf values) upper) :
    ∃ index, lt (values index) upper := by
  unfold iInf at less
  rcases exists_less_of_infimum_lt less with
    ⟨value, ⟨index, equal⟩, smaller⟩
  exact ⟨index, equal ▸ smaller⟩

/-- Shifting by a finite offset preserves the infimum of an antitone
extended-nonnegative sequence. -/
public theorem iInf_tail (values : Nat → ENNReal)
    (antitone : ∀ {first second}, first ≤ second → le (values second) (values first))
    (offset : Nat) :
    iInf (fun index => values (offset + index)) = iInf values := by
  apply le_antisymm
  · apply le_iInf
    intro index
    exact le_trans (iInf_le (fun index => values (offset + index)) index)
      (antitone (Nat.le_add_left index offset))
  · exact le_iInf (fun index => iInf_le values (offset + index))

end Problib.Real.ENNReal
