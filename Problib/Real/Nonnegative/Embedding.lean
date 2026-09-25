module

public import Problib.Real.Nonnegative.Core

set_option autoImplicit false

namespace Problib.Real

namespace NNReal

public theorem ofReal_of_nonnegative
    {value : Construction.Dedekind.selection.Carrier}
    (nonnegative : Construction.Dedekind.le Construction.Dedekind.zero value) :
    ofReal value = ⟨value, nonnegative⟩ := by
  classical
  unfold ofReal
  simp only [dif_pos nonnegative]

public theorem ofReal_toReal (value : NNReal) : ofReal (toReal value) = value :=
  ofReal_of_nonnegative value.property

public theorem toReal_ofReal
    {value : Construction.Dedekind.selection.Carrier}
    (nonnegative : Construction.Dedekind.le Construction.Dedekind.zero value) :
    toReal (ofReal value) = value := by
  rw [ofReal_of_nonnegative nonnegative]
  rfl

public theorem ofReal_of_not_nonnegative
    {value : Construction.Dedekind.selection.Carrier}
    (notNonnegative :
      ¬Construction.Dedekind.le Construction.Dedekind.zero value) :
    ofReal value = zero := by
  classical
  unfold ofReal
  simp only [dif_neg notNonnegative]

public theorem ofReal_zero : ofReal Construction.Dedekind.zero = zero := by
  apply ext
  rw [toReal_ofReal (Construction.Dedekind.le_refl _), toReal_zero]

public theorem ofReal_monotone
    {left right : Construction.Dedekind.selection.Carrier}
    (included : Construction.Dedekind.le left right) :
    le (ofReal left) (ofReal right) := by
  by_cases leftNonnegative :
      Construction.Dedekind.le Construction.Dedekind.zero left
  · have rightNonnegative :=
      Construction.Dedekind.le_trans leftNonnegative included
    change Construction.Dedekind.le
      (toReal (ofReal left)) (toReal (ofReal right))
    rw [toReal_ofReal leftNonnegative, toReal_ofReal rightNonnegative]
    exact included
  · rw [ofReal_of_not_nonnegative leftNonnegative]
    exact zero_le _

public theorem ofReal_eq_zero_iff
    {value : Construction.Dedekind.selection.Carrier} :
    ofReal value = zero ↔
      Construction.Dedekind.le value Construction.Dedekind.zero := by
  constructor
  · intro equal
    by_cases nonnegative :
        Construction.Dedekind.le Construction.Dedekind.zero value
    · have valuesEqual := congrArg toReal equal
      rw [toReal_ofReal nonnegative, toReal_zero] at valuesEqual
      rw [valuesEqual]
      exact Construction.Dedekind.le_refl Construction.Dedekind.zero
    · rcases Construction.Dedekind.le_total
        value Construction.Dedekind.zero with nonpositive | reverse
      · exact nonpositive
      · exact False.elim (nonnegative reverse)
  · intro nonpositive
    by_cases nonnegative :
        Construction.Dedekind.le Construction.Dedekind.zero value
    · have equal := Construction.Dedekind.le_antisymm
        nonpositive nonnegative
      subst value
      exact ofReal_zero
    · exact ofReal_of_not_nonnegative nonnegative

@[expose] public def ofRat (value : Rat) (nonnegative : 0 ≤ value) : NNReal :=
  ⟨Construction.Dedekind.selection.ofRat value, by
    rw [← Construction.Dedekind.ofRat_zero]
    exact (Construction.Dedekind.ofRat_le_iff 0 value).mpr nonnegative⟩

public theorem toReal_ofRat (value : Rat) (nonnegative : 0 ≤ value) :
    toReal (ofRat value nonnegative) =
      Construction.Dedekind.selection.ofRat value :=
  rfl

public theorem ofRat_le_iff (left right : Rat)
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right) :
    le (ofRat left leftNonnegative) (ofRat right rightNonnegative) ↔
      left ≤ right :=
  Construction.Dedekind.ofRat_le_iff left right

public theorem ofRat_lt_iff (left right : Rat)
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right) :
    lt (ofRat left leftNonnegative) (ofRat right rightNonnegative) ↔
      left < right :=
  Construction.Dedekind.ofRat_lt_iff left right

public theorem ofRat_zero : ofRat 0 (by decide) = zero := by
  apply ext
  rw [toReal_ofRat, toReal_zero]
  exact Construction.Dedekind.ofRat_zero

public theorem ofRat_one : ofRat 1 (by decide) = one := by
  apply ext
  rw [toReal_ofRat, toReal_one]
  exact Construction.Dedekind.ofRat_one

public theorem ofRat_add (left right : Rat)
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right) :
    ofRat (left + right)
        (Rat.add_nonneg leftNonnegative rightNonnegative) =
      add (ofRat left leftNonnegative) (ofRat right rightNonnegative) := by
  apply ext
  rw [toReal_ofRat, toReal_add, toReal_ofRat, toReal_ofRat]
  exact Construction.Dedekind.ofRat_add left right

public theorem ofRat_mul (left right : Rat)
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right) :
    ofRat (left * right)
        (Rat.mul_nonneg leftNonnegative rightNonnegative) =
      mul (ofRat left leftNonnegative) (ofRat right rightNonnegative) := by
  apply ext
  rw [toReal_ofRat, toReal_mul, toReal_ofRat, toReal_ofRat]
  exact Construction.Dedekind.ofRat_mul left right

public theorem exists_rational_between {left right : NNReal}
    (less : lt left right) :
    ∃ rational : Rat, ∃ nonnegative : 0 ≤ rational,
      lt left (ofRat rational nonnegative) ∧
        lt (ofRat rational nonnegative) right := by
  rcases Construction.Dedekind.exists_rational_between less with
    ⟨rational, leftRational, rationalRight⟩
  have embeddedNonnegative : Construction.Dedekind.le
      Construction.Dedekind.zero
      (Construction.Dedekind.selection.ofRat rational) :=
    Construction.Dedekind.le_trans left.property leftRational.left
  have rationalNonnegative : 0 ≤ rational := by
    apply (Construction.Dedekind.ofRat_le_iff 0 rational).mp
    rw [Construction.Dedekind.ofRat_zero]
    exact embeddedNonnegative
  refine ⟨rational, rationalNonnegative, ?_, ?_⟩
  · exact leftRational
  · exact rationalRight

/-- Clamping an embedded rational at zero is the embedding of the rational
clamp: a nonnegative rational keeps its value and a negative one becomes zero. -/
public theorem ofReal_ofRat (value : Rat) :
    ofReal (Construction.Dedekind.selection.ofRat value) =
      if nonnegative : 0 ≤ value then ofRat value nonnegative else zero := by
  by_cases nonnegative : 0 ≤ value
  · rw [dif_pos nonnegative]
    have embedded : Construction.Dedekind.le Construction.Dedekind.zero
        (Construction.Dedekind.selection.ofRat value) := by
      rw [← Construction.Dedekind.ofRat_zero]
      exact (Construction.Dedekind.ofRat_le_iff 0 value).mpr nonnegative
    rw [ofReal_of_nonnegative embedded]
    rfl
  · rw [dif_neg nonnegative]
    apply ofReal_of_not_nonnegative
    rw [← Construction.Dedekind.ofRat_zero, Construction.Dedekind.ofRat_le_iff]
    exact nonnegative

end NNReal

end Problib.Real
