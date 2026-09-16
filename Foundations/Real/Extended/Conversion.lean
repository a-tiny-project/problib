module

public import Foundations.Real.Extended.Supremum

namespace Foundations.Real

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

public theorem ofRealFinite (value : SignedReal) : Finite (ofReal value) :=
  True.intro

public theorem toRealFinite (value : NNReal) :
    toReal (finite value) = NNReal.toReal value :=
  rfl

public theorem toRealTop : toReal top = Construction.Dedekind.zero :=
  rfl

public theorem toRealZero : toReal zero = Construction.Dedekind.zero :=
  rfl

public theorem toRealOne : toReal one = Construction.Dedekind.one :=
  rfl

public theorem ofRealZero : ofReal Construction.Dedekind.zero = zero := by
  unfold ofReal
  exact congrArg finite NNReal.ofRealZero

public theorem ofRealOfNonnegative {value : SignedReal}
    (nonnegative : Construction.Dedekind.le Construction.Dedekind.zero value) :
    ofReal value = finite ⟨value, nonnegative⟩ := by
  unfold ofReal
  exact congrArg finite (NNReal.ofRealOfNonnegative nonnegative)

public theorem ofRealOfNotNonnegative {value : SignedReal}
    (notNonnegative :
      ¬Construction.Dedekind.le Construction.Dedekind.zero value) :
    ofReal value = zero := by
  unfold ofReal zero
  exact congrArg finite (NNReal.ofRealOfNotNonnegative notNonnegative)

public theorem ofRealMonotone {left right : SignedReal}
    (included : Construction.Dedekind.le left right) :
    le (ofReal left) (ofReal right) :=
  NNReal.ofRealMonotone included

public theorem ofRealAdd {left right : SignedReal}
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
  rw [ofRealOfNonnegative sumNonnegative,
    ofRealOfNonnegative leftNonnegative,
    ofRealOfNonnegative rightNonnegative]
  rfl

public theorem ofRealEqZeroIff {value : SignedReal} :
    ofReal value = zero ↔
      Construction.Dedekind.le value Construction.Dedekind.zero := by
  constructor
  · intro equal
    apply NNReal.ofRealEqZeroIff.mp
    exact finiteInjective equal
  · intro nonpositive
    exact congrArg finite (NNReal.ofRealEqZeroIff.mpr nonpositive)

public theorem toRealNonnegative (value : ENNReal) :
    Construction.Dedekind.le Construction.Dedekind.zero (toReal value) := by
  cases value with
  | finite underlying => exact underlying.property
  | top => exact Construction.Dedekind.leRefl Construction.Dedekind.zero

public theorem toRealOfReal {value : SignedReal}
    (nonnegative : Construction.Dedekind.le Construction.Dedekind.zero value) :
    toReal (ofReal value) = value := by
  unfold ofReal
  exact NNReal.toRealOfReal nonnegative

public theorem ofRealToRealFinite (value : NNReal) :
    ofReal (toReal (finite value)) = finite value := by
  unfold ofReal toReal
  exact congrArg finite (NNReal.ext (NNReal.toRealOfReal value.property))

public theorem ofRealToReal {value : ENNReal} (finiteValue : Finite value) :
    ofReal (toReal value) = value := by
  rcases existsFiniteOfFinite finiteValue with ⟨underlying, rfl⟩
  exact ofRealToRealFinite underlying

public theorem ofRealToRealTop : ofReal (toReal top) = zero :=
  ofRealZero

public theorem toRealLeToRealIff {left right : ENNReal}
    (leftFinite : Finite left) (rightFinite : Finite right) :
    Construction.Dedekind.le (toReal left) (toReal right) ↔ le left right := by
  rcases existsFiniteOfFinite leftFinite with ⟨leftValue, rfl⟩
  rcases existsFiniteOfFinite rightFinite with ⟨rightValue, rfl⟩
  exact Iff.rfl

public theorem toRealLtToRealIff {left right : ENNReal}
    (leftFinite : Finite left) (rightFinite : Finite right) :
    Construction.Dedekind.lt (toReal left) (toReal right) ↔ lt left right := by
  rcases existsFiniteOfFinite leftFinite with ⟨leftValue, rfl⟩
  rcases existsFiniteOfFinite rightFinite with ⟨rightValue, rfl⟩
  exact Iff.rfl

public theorem ofRealLeOfRealIff {left right : SignedReal}
    (leftNonnegative :
      Construction.Dedekind.le Construction.Dedekind.zero left)
    (rightNonnegative :
      Construction.Dedekind.le Construction.Dedekind.zero right) :
    le (ofReal left) (ofReal right) ↔ Construction.Dedekind.le left right := by
  rw [ofRealOfNonnegative leftNonnegative,
    ofRealOfNonnegative rightNonnegative]
  exact Iff.rfl

public theorem ofRealLtOfRealIff {left right : SignedReal}
    (leftNonnegative :
      Construction.Dedekind.le Construction.Dedekind.zero left)
    (rightNonnegative :
      Construction.Dedekind.le Construction.Dedekind.zero right) :
    lt (ofReal left) (ofReal right) ↔ Construction.Dedekind.lt left right := by
  rw [ofRealOfNonnegative leftNonnegative,
    ofRealOfNonnegative rightNonnegative]
  exact Iff.rfl

public theorem ofRealLeIffLeToReal {value : SignedReal} {upper : ENNReal}
    (upperFinite : Finite upper) :
    le (ofReal value) upper ↔
      Construction.Dedekind.le value (toReal upper) := by
  rcases existsFiniteOfFinite upperFinite with ⟨upperValue, rfl⟩
  change NNReal.le (NNReal.ofReal value) upperValue ↔
    Construction.Dedekind.le value (NNReal.toReal upperValue)
  constructor
  · intro included
    by_cases valueNonnegative :
        Construction.Dedekind.le Construction.Dedekind.zero value
    · rw [NNReal.ofRealOfNonnegative valueNonnegative] at included
      exact included
    · rcases Construction.Dedekind.leTotal value Construction.Dedekind.zero with
        nonpositive | nonnegative
      · exact Construction.Dedekind.leTrans nonpositive upperValue.property
      · exact False.elim (valueNonnegative nonnegative)
  · intro included
    have upperRoundTrip :
        NNReal.ofReal (NNReal.toReal upperValue) = upperValue :=
      NNReal.ext (NNReal.toRealOfReal upperValue.property)
    rw [← upperRoundTrip]
    exact NNReal.ofRealMonotone included

public theorem leOfRealIffToRealLe {lower : ENNReal} {value : SignedReal}
    (lowerFinite : Finite lower)
    (valueNonnegative :
      Construction.Dedekind.le Construction.Dedekind.zero value) :
    le lower (ofReal value) ↔
      Construction.Dedekind.le (toReal lower) value := by
  rcases existsFiniteOfFinite lowerFinite with ⟨lowerValue, rfl⟩
  rw [ofRealOfNonnegative valueNonnegative]
  exact Iff.rfl

/-- Embed a non-negative rational into `ENNReal`. -/
@[expose] public def ofRat (value : Rat) (nonnegative : 0 ≤ value) : ENNReal :=
  finite (NNReal.ofRat value nonnegative)

public theorem toRealOfRat (value : Rat) (nonnegative : 0 ≤ value) :
    toReal (ofRat value nonnegative) =
      Construction.Dedekind.selection.ofRat value :=
  rfl

public theorem ofRatLeIff (left right : Rat)
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right) :
    le (ofRat left leftNonnegative) (ofRat right rightNonnegative) ↔
      left ≤ right :=
  NNReal.ofRatLeIff left right leftNonnegative rightNonnegative

public theorem ofRatLtIff (left right : Rat)
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right) :
    lt (ofRat left leftNonnegative) (ofRat right rightNonnegative) ↔
      left < right :=
  NNReal.ofRatLtIff left right leftNonnegative rightNonnegative

public theorem ofRatZero : ofRat 0 (by decide) = zero :=
  congrArg finite NNReal.ofRatZero

public theorem ofRatOne : ofRat 1 (by decide) = one :=
  congrArg finite NNReal.ofRatOne

public theorem ofRatAdd (left right : Rat)
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right) :
    ofRat (left + right) (Rat.add_nonneg leftNonnegative rightNonnegative) =
      add (ofRat left leftNonnegative) (ofRat right rightNonnegative) :=
  congrArg finite (NNReal.ofRatAdd left right leftNonnegative rightNonnegative)

public theorem ofRatMul (left right : Rat)
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right) :
    ofRat (left * right) (Rat.mul_nonneg leftNonnegative rightNonnegative) =
      mul (ofRat left leftNonnegative) (ofRat right rightNonnegative) :=
  congrArg finite (NNReal.ofRatMul left right leftNonnegative rightNonnegative)

public theorem existsRationalBetweenOfFinite {left right : ENNReal}
    (leftFinite : Finite left) (rightFinite : Finite right)
    (less : lt left right) :
    ∃ rational : Rat, ∃ nonnegative : 0 ≤ rational,
      lt left (ofRat rational nonnegative) ∧
        lt (ofRat rational nonnegative) right := by
  rcases existsFiniteOfFinite leftFinite with ⟨leftValue, rfl⟩
  rcases existsFiniteOfFinite rightFinite with ⟨rightValue, rfl⟩
  rcases NNReal.existsRationalBetween less with
    ⟨rational, nonnegative, leftRational, rationalRight⟩
  exact ⟨rational, nonnegative, leftRational, rationalRight⟩

end ENNReal

end Foundations.Real
