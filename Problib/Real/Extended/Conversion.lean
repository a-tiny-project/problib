module

public import Problib.Real.Extended.Supremum

namespace Problib.Real

set_option autoImplicit false

local notation "SignedReal" => Construction.Dedekind.selection.Carrier

namespace ENNReal

/-- Embed a signed real into `ENNReal`, mapping negative values to zero. -/
@[expose] public noncomputable def ofReal (value : SignedReal) : ENNReal :=
  finite (NNReal.ofReal value)

/-- Project `ENNReal` to signed real, mapping `top` to zero. -/
@[expose] public def toReal : ENNReal → SignedReal
  | .finite value => NNReal.toReal value
  | .top => Construction.Dedekind.zero

public theorem ofReal_finite (value : SignedReal) : Finite (ofReal value) :=
  True.intro

public theorem toReal_finite (value : NNReal) :
    toReal (finite value) = NNReal.toReal value :=
  rfl

public theorem toReal_top : toReal top = Construction.Dedekind.zero :=
  rfl

public theorem toReal_zero : toReal zero = Construction.Dedekind.zero :=
  rfl

public theorem toReal_one : toReal one = Construction.Dedekind.one :=
  rfl

public theorem ofReal_zero : ofReal Construction.Dedekind.zero = zero := by
  unfold ofReal
  exact congrArg finite NNReal.ofReal_zero

public theorem ofReal_of_nonnegative {value : SignedReal}
    (nonnegative : Construction.Dedekind.le Construction.Dedekind.zero value) :
    ofReal value = finite ⟨value, nonnegative⟩ := by
  unfold ofReal
  exact congrArg finite (NNReal.ofReal_of_nonnegative nonnegative)

public theorem ofReal_of_not_nonnegative {value : SignedReal}
    (notNonnegative :
      ¬Construction.Dedekind.le Construction.Dedekind.zero value) :
    ofReal value = zero := by
  unfold ofReal zero
  exact congrArg finite (NNReal.ofReal_of_not_nonnegative notNonnegative)

public theorem ofReal_monotone {left right : SignedReal}
    (included : Construction.Dedekind.le left right) :
    le (ofReal left) (ofReal right) :=
  NNReal.ofReal_monotone included

public theorem ofReal_add {left right : SignedReal}
    (leftNonnegative :
      Construction.Dedekind.le Construction.Dedekind.zero left)
    (rightNonnegative :
      Construction.Dedekind.le Construction.Dedekind.zero right) :
    ofReal (Construction.Dedekind.add left right) =
      add (ofReal left) (ofReal right) := by
  have sumNonnegative : Construction.Dedekind.le
      Construction.Dedekind.zero (Construction.Dedekind.add left right) := by
    exact (NNReal.add ⟨left, leftNonnegative⟩
      ⟨right, rightNonnegative⟩).property
  rw [ofReal_of_nonnegative sumNonnegative,
    ofReal_of_nonnegative leftNonnegative,
    ofReal_of_nonnegative rightNonnegative]
  rfl

public theorem ofReal_eq_zero_iff {value : SignedReal} :
    ofReal value = zero ↔
      Construction.Dedekind.le value Construction.Dedekind.zero := by
  constructor
  · intro equal
    apply NNReal.ofReal_eq_zero_iff.mp
    exact finite_injective equal
  · intro nonpositive
    exact congrArg finite (NNReal.ofReal_eq_zero_iff.mpr nonpositive)

public theorem toReal_nonnegative (value : ENNReal) :
    Construction.Dedekind.le Construction.Dedekind.zero (toReal value) := by
  cases value with
  | finite underlying => exact underlying.property
  | top => exact Construction.Dedekind.le_refl Construction.Dedekind.zero

public theorem toReal_ofReal {value : SignedReal}
    (nonnegative : Construction.Dedekind.le Construction.Dedekind.zero value) :
    toReal (ofReal value) = value := by
  unfold ofReal
  exact NNReal.toReal_ofReal nonnegative

public theorem ofReal_toReal_finite (value : NNReal) :
    ofReal (toReal (finite value)) = finite value := by
  unfold ofReal toReal
  exact congrArg finite (NNReal.ext (NNReal.toReal_ofReal value.property))

public theorem ofReal_one : ofReal Construction.Dedekind.one = one :=
  ofReal_toReal_finite NNReal.one

public theorem ofReal_toReal {value : ENNReal} (finiteValue : Finite value) :
    ofReal (toReal value) = value := by
  rcases exists_finite_of_finite finiteValue with ⟨underlying, rfl⟩
  exact ofReal_toReal_finite underlying

public theorem ofReal_toReal_top : ofReal (toReal top) = zero :=
  ofReal_zero

public theorem toReal_le_toReal_iff {left right : ENNReal}
    (leftFinite : Finite left) (rightFinite : Finite right) :
    Construction.Dedekind.le (toReal left) (toReal right) ↔ le left right := by
  rcases exists_finite_of_finite leftFinite with ⟨leftValue, rfl⟩
  rcases exists_finite_of_finite rightFinite with ⟨rightValue, rfl⟩
  exact Iff.rfl

public theorem toReal_lt_toReal_iff {left right : ENNReal}
    (leftFinite : Finite left) (rightFinite : Finite right) :
    Construction.Dedekind.lt (toReal left) (toReal right) ↔ lt left right := by
  rcases exists_finite_of_finite leftFinite with ⟨leftValue, rfl⟩
  rcases exists_finite_of_finite rightFinite with ⟨rightValue, rfl⟩
  exact Iff.rfl

public theorem ofReal_le_ofReal_iff {left right : SignedReal}
    (leftNonnegative :
      Construction.Dedekind.le Construction.Dedekind.zero left)
    (rightNonnegative :
      Construction.Dedekind.le Construction.Dedekind.zero right) :
    le (ofReal left) (ofReal right) ↔ Construction.Dedekind.le left right := by
  rw [ofReal_of_nonnegative leftNonnegative,
    ofReal_of_nonnegative rightNonnegative]
  exact Iff.rfl

public theorem ofReal_lt_ofReal_iff {left right : SignedReal}
    (leftNonnegative :
      Construction.Dedekind.le Construction.Dedekind.zero left)
    (rightNonnegative :
      Construction.Dedekind.le Construction.Dedekind.zero right) :
    lt (ofReal left) (ofReal right) ↔ Construction.Dedekind.lt left right := by
  rw [ofReal_of_nonnegative leftNonnegative,
    ofReal_of_nonnegative rightNonnegative]
  exact Iff.rfl

public theorem ofReal_le_iff_le_toReal {value : SignedReal} {upper : ENNReal}
    (upperFinite : Finite upper) :
    le (ofReal value) upper ↔
      Construction.Dedekind.le value (toReal upper) := by
  rcases exists_finite_of_finite upperFinite with ⟨upperValue, rfl⟩
  change NNReal.le (NNReal.ofReal value) upperValue ↔
    Construction.Dedekind.le value (NNReal.toReal upperValue)
  constructor
  · intro included
    by_cases valueNonnegative :
        Construction.Dedekind.le Construction.Dedekind.zero value
    · rw [NNReal.ofReal_of_nonnegative valueNonnegative] at included
      exact included
    · rcases Construction.Dedekind.le_total value Construction.Dedekind.zero with
        nonpositive | nonnegative
      · exact Construction.Dedekind.le_trans nonpositive upperValue.property
      · exact False.elim (valueNonnegative nonnegative)
  · intro included
    have upperRoundTrip :
        NNReal.ofReal (NNReal.toReal upperValue) = upperValue :=
      NNReal.ext (NNReal.toReal_ofReal upperValue.property)
    rw [← upperRoundTrip]
    exact NNReal.ofReal_monotone included

public theorem le_ofReal_iff_toReal_le {lower : ENNReal} {value : SignedReal}
    (lowerFinite : Finite lower)
    (valueNonnegative :
      Construction.Dedekind.le Construction.Dedekind.zero value) :
    le lower (ofReal value) ↔
      Construction.Dedekind.le (toReal lower) value := by
  rcases exists_finite_of_finite lowerFinite with ⟨lowerValue, rfl⟩
  rw [ofReal_of_nonnegative valueNonnegative]
  exact Iff.rfl

/-- Embed a non-negative rational into `ENNReal`. -/
@[expose] public def ofRat (value : Rat) (nonnegative : 0 ≤ value) : ENNReal :=
  finite (NNReal.ofRat value nonnegative)

public theorem toReal_ofRat (value : Rat) (nonnegative : 0 ≤ value) :
    toReal (ofRat value nonnegative) =
      Construction.Dedekind.selection.ofRat value :=
  rfl

public theorem ofRat_le_iff (left right : Rat)
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right) :
    le (ofRat left leftNonnegative) (ofRat right rightNonnegative) ↔
      left ≤ right :=
  NNReal.ofRat_le_iff left right leftNonnegative rightNonnegative

public theorem ofRat_lt_iff (left right : Rat)
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right) :
    lt (ofRat left leftNonnegative) (ofRat right rightNonnegative) ↔
      left < right :=
  NNReal.ofRat_lt_iff left right leftNonnegative rightNonnegative

public theorem ofRat_zero : ofRat 0 (by decide) = zero :=
  congrArg finite NNReal.ofRat_zero

public theorem ofRat_one : ofRat 1 (by decide) = one :=
  congrArg finite NNReal.ofRat_one

public theorem ofRat_add (left right : Rat)
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right) :
    ofRat (left + right) (Rat.add_nonneg leftNonnegative rightNonnegative) =
      add (ofRat left leftNonnegative) (ofRat right rightNonnegative) :=
  congrArg finite (NNReal.ofRat_add left right leftNonnegative rightNonnegative)

public theorem ofRat_mul (left right : Rat)
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right) :
    ofRat (left * right) (Rat.mul_nonneg leftNonnegative rightNonnegative) =
      mul (ofRat left leftNonnegative) (ofRat right rightNonnegative) :=
  congrArg finite (NNReal.ofRat_mul left right leftNonnegative rightNonnegative)

public theorem exists_rational_between_of_finite {left right : ENNReal}
    (leftFinite : Finite left) (rightFinite : Finite right)
    (less : lt left right) :
    ∃ rational : Rat, ∃ nonnegative : 0 ≤ rational,
      lt left (ofRat rational nonnegative) ∧
        lt (ofRat rational nonnegative) right := by
  rcases exists_finite_of_finite leftFinite with ⟨leftValue, rfl⟩
  rcases exists_finite_of_finite rightFinite with ⟨rightValue, rfl⟩
  rcases NNReal.exists_rational_between less with
    ⟨rational, nonnegative, leftRational, rationalRight⟩
  exact ⟨rational, nonnegative, leftRational, rationalRight⟩

end ENNReal

end Problib.Real
