module

public import Foundations.Real.Nonnegative.Core

set_option autoImplicit false

namespace Foundations.Real

namespace NNReal

public theorem ofRealOfNonnegative
    {value : Construction.Dedekind.selection.Carrier}
    (nonnegative : Construction.Dedekind.le Construction.Dedekind.zero value) :
    ofReal value = ⟨value, nonnegative⟩ := by
  classical
  unfold ofReal
  simp only [dif_pos nonnegative]

public theorem toRealOfReal
    {value : Construction.Dedekind.selection.Carrier}
    (nonnegative : Construction.Dedekind.le Construction.Dedekind.zero value) :
    toReal (ofReal value) = value := by
  rw [ofRealOfNonnegative nonnegative]
  rfl

public theorem ofRealOfNotNonnegative
    {value : Construction.Dedekind.selection.Carrier}
    (notNonnegative :
      ¬Construction.Dedekind.le Construction.Dedekind.zero value) :
    ofReal value = zero := by
  classical
  unfold ofReal
  simp only [dif_neg notNonnegative]

public theorem ofRealZero : ofReal Construction.Dedekind.zero = zero := by
  apply ext
  rw [toRealOfReal (Construction.Dedekind.leRefl _), toRealZero]

public theorem ofRealMonotone
    {left right : Construction.Dedekind.selection.Carrier}
    (included : Construction.Dedekind.le left right) :
    le (ofReal left) (ofReal right) := by
  by_cases leftNonnegative :
      Construction.Dedekind.le Construction.Dedekind.zero left
  · have rightNonnegative :=
      Construction.Dedekind.leTrans leftNonnegative included
    change Construction.Dedekind.le
      (toReal (ofReal left)) (toReal (ofReal right))
    rw [toRealOfReal leftNonnegative, toRealOfReal rightNonnegative]
    exact included
  · rw [ofRealOfNotNonnegative leftNonnegative]
    exact zeroLe _

public theorem ofRealEqZeroIff
    {value : Construction.Dedekind.selection.Carrier} :
    ofReal value = zero ↔
      Construction.Dedekind.le value Construction.Dedekind.zero := by
  constructor
  · intro equal
    by_cases nonnegative :
        Construction.Dedekind.le Construction.Dedekind.zero value
    · have valuesEqual := congrArg toReal equal
      rw [toRealOfReal nonnegative, toRealZero] at valuesEqual
      rw [valuesEqual]
      exact Construction.Dedekind.leRefl Construction.Dedekind.zero
    · rcases Construction.Dedekind.leTotal
        value Construction.Dedekind.zero with nonpositive | reverse
      · exact nonpositive
      · exact False.elim (nonnegative reverse)
  · intro nonpositive
    by_cases nonnegative :
        Construction.Dedekind.le Construction.Dedekind.zero value
    · have equal := Construction.Dedekind.leAntisymm
        nonpositive nonnegative
      subst value
      exact ofRealZero
    · exact ofRealOfNotNonnegative nonnegative

@[expose] public def ofRat (value : Rat) (nonnegative : 0 ≤ value) : NNReal :=
  ⟨Construction.Dedekind.selection.ofRat value, by
    rw [← Construction.Dedekind.ofRatZero]
    exact (Construction.Dedekind.ofRatLeIff 0 value).mpr nonnegative⟩

public theorem toRealOfRat (value : Rat) (nonnegative : 0 ≤ value) :
    toReal (ofRat value nonnegative) =
      Construction.Dedekind.selection.ofRat value :=
  rfl

public theorem ofRatLeIff (left right : Rat)
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right) :
    le (ofRat left leftNonnegative) (ofRat right rightNonnegative) ↔
      left ≤ right :=
  Construction.Dedekind.ofRatLeIff left right

public theorem ofRatLtIff (left right : Rat)
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right) :
    lt (ofRat left leftNonnegative) (ofRat right rightNonnegative) ↔
      left < right :=
  Construction.Dedekind.ofRatLtIff left right

public theorem ofRatZero : ofRat 0 (by decide) = zero := by
  apply ext
  rw [toRealOfRat, toRealZero]
  exact Construction.Dedekind.ofRatZero

public theorem ofRatOne : ofRat 1 (by decide) = one := by
  apply ext
  rw [toRealOfRat, toRealOne]
  exact Construction.Dedekind.ofRatOne

public theorem ofRatAdd (left right : Rat)
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right) :
    ofRat (left + right)
        (Rat.add_nonneg leftNonnegative rightNonnegative) =
      add (ofRat left leftNonnegative) (ofRat right rightNonnegative) := by
  apply ext
  rw [toRealOfRat, toRealAdd, toRealOfRat, toRealOfRat]
  exact Construction.Dedekind.ofRatAdd left right

public theorem ofRatMul (left right : Rat)
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right) :
    ofRat (left * right)
        (Rat.mul_nonneg leftNonnegative rightNonnegative) =
      mul (ofRat left leftNonnegative) (ofRat right rightNonnegative) := by
  apply ext
  rw [toRealOfRat, toRealMul, toRealOfRat, toRealOfRat]
  exact Construction.Dedekind.ofRatMul left right

public theorem existsRationalBetween {left right : NNReal}
    (less : lt left right) :
    ∃ rational : Rat, ∃ nonnegative : 0 ≤ rational,
      lt left (ofRat rational nonnegative) ∧
        lt (ofRat rational nonnegative) right := by
  rcases Construction.Dedekind.existsRationalBetween less with
    ⟨rational, leftRational, rationalRight⟩
  have embeddedNonnegative : Construction.Dedekind.le
      Construction.Dedekind.zero
      (Construction.Dedekind.selection.ofRat rational) :=
    Construction.Dedekind.leTrans left.property leftRational.left
  have rationalNonnegative : 0 ≤ rational := by
    apply (Construction.Dedekind.ofRatLeIff 0 rational).mp
    rw [Construction.Dedekind.ofRatZero]
    exact embeddedNonnegative
  refine ⟨rational, rationalNonnegative, ?_, ?_⟩
  · exact leftRational
  · exact rationalRight

end NNReal

end Foundations.Real
