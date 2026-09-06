module

public import Foundations.Real.Extended.Order

namespace Foundations.Real.ENNReal

set_option autoImplicit false

@[expose] public def image (transform : ENNReal → ENNReal)
    (set : ENNReal → Prop) (result : ENNReal) : Prop :=
  ∃ value, set value ∧ result = transform value

@[expose] public noncomputable def iSup (values : Nat → ENNReal) : ENNReal :=
  supremum (fun value => ∃ index, value = values index)

public theorem leISup (values : Nat → ENNReal) (index : Nat) :
    le (values index) (iSup values) := by
  unfold iSup
  exact leSupremum ⟨index, rfl⟩

public theorem iSupLe {values : Nat → ENNReal} {upper : ENNReal}
    (isUpper : ∀ index, le (values index) upper) :
    le (iSup values) upper := by
  unfold iSup
  apply supremumLe
  rintro value ⟨index, equal⟩
  rw [equal]
  exact isUpper index

public theorem iSupLeIff {values : Nat → ENNReal} {upper : ENNReal} :
    le (iSup values) upper ↔ ∀ index, le (values index) upper := by
  constructor
  · intro supremumUpper index
    exact leTrans (leISup values index) supremumUpper
  · exact iSupLe

public theorem iSupMono {left right : Nat → ENNReal}
    (included : ∀ index, le (left index) (right index)) :
    le (iSup left) (iSup right) := by
  apply iSupLe
  intro index
  exact leTrans (included index) (leISup right index)

public theorem iSupConst (value : ENNReal) :
    iSup (fun _ => value) = value := by
  apply leAntisymm
  · apply iSupLe
    intro index
    exact leRefl value
  · exact leISup (fun _ => value) 0

public theorem existsIndexGreaterOfLtISup {values : Nat → ENNReal}
    {lower : ENNReal} (less : lt lower (iSup values)) :
    ∃ index, lt lower (values index) := by
  unfold iSup at less
  rcases existsGreaterOfLtSupremum less with
    ⟨value, ⟨index, equal⟩, greater⟩
  exact ⟨index, equal ▸ greater⟩

@[expose] public noncomputable def iInf (values : Nat → ENNReal) : ENNReal :=
  infimum (fun value => ∃ index, value = values index)

public theorem iInfLe (values : Nat → ENNReal) (index : Nat) :
    le (iInf values) (values index) := by
  unfold iInf
  exact infimumLe ⟨index, rfl⟩

public theorem leIInf {values : Nat → ENNReal} {lower : ENNReal}
    (isLower : ∀ index, le lower (values index)) :
    le lower (iInf values) := by
  unfold iInf
  apply leInfimum
  rintro value ⟨index, equal⟩
  rw [equal]
  exact isLower index

public theorem leIInfIff {values : Nat → ENNReal} {lower : ENNReal} :
    le lower (iInf values) ↔ ∀ index, le lower (values index) := by
  constructor
  · intro lowerInfimum index
    exact leTrans lowerInfimum (iInfLe values index)
  · exact leIInf

public theorem iInfMono {left right : Nat → ENNReal}
    (included : ∀ index, le (left index) (right index)) :
    le (iInf left) (iInf right) := by
  apply leIInf
  intro index
  exact leTrans (iInfLe left index) (included index)

public theorem iInfConst (value : ENNReal) :
    iInf (fun _ => value) = value := by
  apply leAntisymm
  · exact iInfLe (fun _ => value) 0
  · apply leIInf
    intro index
    exact leRefl value

public theorem existsIndexLessOfIInfLt {values : Nat → ENNReal}
    {upper : ENNReal} (less : lt (iInf values) upper) :
    ∃ index, lt (values index) upper := by
  unfold iInf at less
  rcases existsLessOfInfimumLt less with
    ⟨value, ⟨index, equal⟩, smaller⟩
  exact ⟨index, equal ▸ smaller⟩

/-- Shifting by a finite offset preserves the infimum of an antitone
extended-nonnegative sequence. -/
public theorem iInfTail (values : Nat → ENNReal)
    (antitone : ∀ {first second}, first ≤ second → le (values second) (values first))
    (offset : Nat) :
    iInf (fun index => values (offset + index)) = iInf values := by
  apply leAntisymm
  · apply leIInf
    intro index
    exact leTrans (iInfLe (fun index => values (offset + index)) index)
      (antitone (Nat.le_add_left index offset))
  · exact leIInf (fun index => iInfLe values (offset + index))

end Foundations.Real.ENNReal
