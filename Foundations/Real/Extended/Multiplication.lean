module

public import Foundations.Real.Extended.Additive

namespace Foundations.Real.ENNReal

set_option autoImplicit false

@[expose] public noncomputable def mul (left right : ENNReal) : ENNReal := by
  classical
  exact match left, right with
  | .finite leftValue, .finite rightValue =>
      .finite (NNReal.mul leftValue rightValue)
  | .finite value, .top => if value = NNReal.zero then zero else top
  | .top, .finite value => if value = NNReal.zero then zero else top
  | .top, .top => top

public theorem finiteMulFinite (left right : NNReal) :
    mul (finite left) (finite right) = finite (NNReal.mul left right) := by
  classical
  rfl

/-- The product of two finite extended-nonnegative values is finite. -/
public theorem mulFinite {left right : ENNReal}
    (leftFinite : Finite left) (rightFinite : Finite right) : Finite (mul left right) := by
  rcases existsFiniteOfFinite leftFinite with ⟨leftValue, rfl⟩
  rcases existsFiniteOfFinite rightFinite with ⟨rightValue, rfl⟩
  exact True.intro

public theorem finiteMulTopOfEqZero {value : NNReal}
    (equal : value = NNReal.zero) : mul (finite value) top = zero := by
  classical
  unfold mul
  simp only [if_pos equal]

public theorem finiteMulTopOfNeZero {value : NNReal}
    (nonzero : value ≠ NNReal.zero) : mul (finite value) top = top := by
  classical
  unfold mul
  simp only [if_neg nonzero]

public theorem topMulFiniteOfEqZero {value : NNReal}
    (equal : value = NNReal.zero) : mul top (finite value) = zero := by
  classical
  unfold mul
  simp only [if_pos equal]

public theorem topMulFiniteOfNeZero {value : NNReal}
    (nonzero : value ≠ NNReal.zero) : mul top (finite value) = top := by
  classical
  unfold mul
  simp only [if_neg nonzero]

public theorem topMulTop : mul top top = top := by
  classical
  rfl

public theorem mulComm (left right : ENNReal) : mul left right = mul right left := by
  cases left with
  | top => cases right <;> rfl
  | finite leftValue =>
      cases right with
      | top => rfl
      | finite rightValue =>
          exact congrArg finite (NNReal.mulComm leftValue rightValue)

public theorem mulZero (value : ENNReal) : mul value zero = zero := by
  classical
  cases value with
  | top => exact topMulFiniteOfEqZero rfl
  | finite underlying => exact congrArg finite (NNReal.mulZero underlying)

public theorem zeroMul (value : ENNReal) : mul zero value = zero := by
  rw [mulComm, mulZero]

public theorem mulTopOfNeZero {value : ENNReal} (nonzero : value ≠ zero) :
    mul value top = top := by
  classical
  cases value with
  | top => rfl
  | finite underlying =>
      have underlyingNonzero : underlying ≠ NNReal.zero := by
        intro equal
        apply nonzero
        exact congrArg finite equal
      exact finiteMulTopOfNeZero underlyingNonzero

public theorem topMulOfNeZero {value : ENNReal} (nonzero : value ≠ zero) :
    mul top value = top := by
  rw [mulComm]
  exact mulTopOfNeZero nonzero

public theorem mulEqZeroIff {left right : ENNReal} :
    mul left right = zero ↔ left = zero ∨ right = zero := by
  classical
  cases left with
  | top =>
      cases right with
      | top =>
          rw [topMulTop]
          constructor
          · intro equal
            exact False.elim (topNeFinite NNReal.zero equal)
          · rintro (leftZero | rightZero)
            · exact False.elim (topNeFinite NNReal.zero leftZero)
            · exact False.elim (topNeFinite NNReal.zero rightZero)
      | finite rightValue =>
          by_cases rightZero : rightValue = NNReal.zero
          · subst rightValue
            rw [topMulFiniteOfEqZero rfl]
            exact ⟨fun _ => Or.inr rfl, fun _ => rfl⟩
          · constructor
            · intro equal
              rw [topMulFiniteOfNeZero rightZero] at equal
              exact False.elim (topNeFinite NNReal.zero equal)
            · rintro (leftZero | rightEqual)
              · exact False.elim (topNeFinite NNReal.zero leftZero)
              · exact False.elim (rightZero (finiteInjective rightEqual))
  | finite leftValue =>
      cases right with
      | top =>
          by_cases leftZero : leftValue = NNReal.zero
          · subst leftValue
            rw [finiteMulTopOfEqZero rfl]
            exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
          · constructor
            · intro equal
              rw [finiteMulTopOfNeZero leftZero] at equal
              exact False.elim (topNeFinite NNReal.zero equal)
            · rintro (leftEqual | rightZero)
              · exact False.elim (leftZero (finiteInjective leftEqual))
              · exact False.elim (topNeFinite NNReal.zero rightZero)
      | finite rightValue =>
          constructor
          · intro equal
            rcases (NNReal.mulEqZeroIff.mp (finiteInjective equal)) with
              leftZero | rightZero
            · exact Or.inl (congrArg finite leftZero)
            · exact Or.inr (congrArg finite rightZero)
          · rintro (leftZero | rightZero)
            · exact congrArg finite
                ((NNReal.mulEqZeroIff).mpr (Or.inl (finiteInjective leftZero)))
            · exact congrArg finite
                ((NNReal.mulEqZeroIff).mpr (Or.inr (finiteInjective rightZero)))

private theorem nnrealMulNeZero {left right : NNReal}
    (leftNonzero : left ≠ NNReal.zero)
    (rightNonzero : right ≠ NNReal.zero) :
    NNReal.mul left right ≠ NNReal.zero := by
  intro equal
  rcases NNReal.mulEqZeroIff.mp equal with leftZero | rightZero
  · exact leftNonzero leftZero
  · exact rightNonzero rightZero

public theorem mulAssoc (left middle right : ENNReal) :
    mul (mul left middle) right = mul left (mul middle right) := by
  by_cases leftZero : left = zero
  · subst left
    rw [zeroMul, zeroMul, zeroMul]
  · by_cases middleZero : middle = zero
    · subst middle
      calc
        mul (mul left zero) right = mul zero right :=
          congrArg (fun value => mul value right) (mulZero left)
        _ = zero := zeroMul right
        _ = mul left zero := (mulZero left).symm
        _ = mul left (mul zero right) :=
          congrArg (mul left) (zeroMul right).symm
    · by_cases rightZero : right = zero
      · subst right
        rw [mulZero, mulZero, mulZero]
      · have leftMiddleNonzero : mul left middle ≠ zero := by
          intro equal
          rcases mulEqZeroIff.mp equal with equal | equal
          · exact leftZero equal
          · exact middleZero equal
        have middleRightNonzero : mul middle right ≠ zero := by
          intro equal
          rcases mulEqZeroIff.mp equal with equal | equal
          · exact middleZero equal
          · exact rightZero equal
        cases left with
        | top =>
            rw [topMulOfNeZero middleZero, topMulOfNeZero rightZero,
              topMulOfNeZero middleRightNonzero]
        | finite leftValue =>
            cases middle with
            | top =>
                rw [mulTopOfNeZero leftZero, topMulOfNeZero rightZero]
                exact (mulTopOfNeZero leftZero).symm
            | finite middleValue =>
                cases right with
                | top =>
                    rw [mulTopOfNeZero leftMiddleNonzero,
                      mulTopOfNeZero middleZero, mulTopOfNeZero leftZero]
                | finite rightValue =>
                    exact congrArg finite
                      (NNReal.mulAssoc leftValue middleValue rightValue)

public theorem oneNeZero : one ≠ zero := by
  intro equal
  exact NNReal.oneNeZero (finiteInjective equal)

public theorem mulOne (value : ENNReal) : mul value one = value := by
  classical
  cases value with
  | top => exact topMulFiniteOfNeZero NNReal.oneNeZero
  | finite underlying => exact congrArg finite (NNReal.mulOne underlying)

public theorem oneMul (value : ENNReal) : mul one value = value := by
  rw [mulComm, mulOne]

public theorem mulAdd (factor left right : ENNReal) :
    mul factor (add left right) =
      add (mul factor left) (mul factor right) := by
  by_cases factorZero : factor = zero
  · subst factor
    rw [zeroMul, zeroMul, zeroMul, zeroAdd]
  · cases factor with
    | top =>
        by_cases leftZero : left = zero
        · subst left
          rw [zeroAdd, mulZero, zeroAdd]
        · by_cases rightZero : right = zero
          · subst right
            rw [addZero, mulZero, addZero]
          · have sumNonzero : add left right ≠ zero := by
              intro equal
              rcases addEqZeroIff.mp equal with ⟨leftEqual, rightEqual⟩
              exact leftZero leftEqual
            rw [topMulOfNeZero sumNonzero, topMulOfNeZero leftZero,
              topMulOfNeZero rightZero, topAdd]
    | finite factorValue =>
        cases left with
        | top =>
            rw [topAdd, mulTopOfNeZero factorZero, topAdd]
        | finite leftValue =>
            cases right with
            | top =>
                rw [addTop, mulTopOfNeZero factorZero, addTop]
            | finite rightValue =>
                exact congrArg finite
                  (NNReal.mulAdd factorValue leftValue rightValue)

public noncomputable def semiring :
    Foundations.Algebra.CommutativeSemiringLaws ENNReal where
  additive := {
    zero := zero
    add := add
    add_comm := addComm
    add_assoc := addAssoc
    add_zero := addZero
  }
  multiplicative := {
    one := one
    mul := mul
    mul_comm := mulComm
    mul_assoc := mulAssoc
    mul_one := mulOne
  }
  zero_mul := zeroMul
  mul_add := mulAdd

public theorem mulLeMulRight {left right : ENNReal}
    (included : le left right) (factor : ENNReal) :
    le (mul left factor) (mul right factor) := by
  classical
  cases factor with
  | top =>
      cases left with
      | top =>
          cases right with
          | top => exact leRefl top
          | finite _ => exact False.elim included
      | finite leftValue =>
          cases right with
          | top => exact leTop _
          | finite rightValue =>
              by_cases leftZero : leftValue = NNReal.zero
              · simp only [mul, if_pos leftZero]
                exact zeroLe _
              · have rightNonzero : rightValue ≠ NNReal.zero := by
                  intro rightZero
                  subst rightValue
                  exact leftZero (NNReal.leAntisymm included
                    (NNReal.zeroLe leftValue))
                simp only [mul, if_neg leftZero, if_neg rightNonzero]
                exact leRefl top
  | finite factorValue =>
      by_cases factorZero : factorValue = NNReal.zero
      · subst factorValue
        simpa only [show finite NNReal.zero = zero from rfl,
          mulZero] using leRefl zero
      · cases left with
        | top =>
            cases right with
            | top => exact leRefl (mul top (finite factorValue))
            | finite _ => exact False.elim included
        | finite leftValue =>
            cases right with
            | top =>
                simp only [mul, if_neg factorZero]
                exact leTop _
            | finite rightValue =>
                exact NNReal.mulLeMulRight included factorValue

public theorem mulLeMulLeft {left right : ENNReal}
    (included : le left right) (factor : ENNReal) :
    le (mul factor left) (mul factor right) := by
  rw [mulComm factor left, mulComm factor right]
  exact mulLeMulRight included factor

public theorem mulLeMul {firstLeft firstRight secondLeft secondRight : ENNReal}
    (firstIncluded : le firstLeft firstRight)
    (secondIncluded : le secondLeft secondRight) :
    le (mul firstLeft secondLeft) (mul firstRight secondRight) :=
  leTrans (mulLeMulRight firstIncluded secondLeft)
    (mulLeMulLeft secondIncluded firstRight)

/-- Multiplication on the right by a finite positive extended real reflects
and preserves the non-strict order. -/
public theorem mulLeMulRightIff {factor left right : ENNReal}
    (factorFinite : Finite factor) (factorPositive : lt zero factor) :
    le (mul left factor) (mul right factor) ↔ le left right := by
  constructor
  · intro included
    rcases existsFiniteOfFinite factorFinite with ⟨factorValue, rfl⟩
    cases left with
    | finite leftValue =>
        cases right with
        | finite rightValue =>
            exact NNReal.leOfMulLeMulRight factorPositive included
        | top => exact leTop _
    | top =>
        cases right with
        | finite rightValue =>
            rw [topMulOfNeZero (zeroLtIffNeZero.mp factorPositive)] at included
            exact False.elim included
        | top => exact leRefl _
  · intro included
    exact mulLeMulRight included factor

/-- Multiplication on the left by a finite positive extended real reflects
and preserves the non-strict order. -/
public theorem mulLeMulLeftIff {factor left right : ENNReal}
    (factorFinite : Finite factor) (factorPositive : lt zero factor) :
    le (mul factor left) (mul factor right) ↔ le left right := by
  rw [mulComm factor left, mulComm factor right]
  exact mulLeMulRightIff factorFinite factorPositive

/-- A finite mass and positive finite budget admit a positive finite scale
fitting within that budget. -/
public theorem existsPositiveScale {mass budget : ENNReal}
    (massFinite : ENNReal.Finite mass) (budgetFinite : ENNReal.Finite budget)
    (budgetPositive : ENNReal.lt ENNReal.zero budget) :
    ∃ factor, ENNReal.Finite factor ∧ ENNReal.lt ENNReal.zero factor ∧
      ENNReal.le (ENNReal.mul factor mass) budget := by
  rcases ENNReal.existsFiniteOfFinite massFinite with ⟨massValue, rfl⟩
  rcases ENNReal.existsFiniteOfFinite budgetFinite with ⟨budgetValue, rfl⟩
  by_cases zero : massValue = NNReal.zero
  · refine ⟨ENNReal.one, True.intro, NNReal.onePositive, ?_⟩
    rw [zero]
    change ENNReal.le (ENNReal.mul ENNReal.one ENNReal.zero) (.finite budgetValue)
    rw [ENNReal.mulZero]
    exact ENNReal.zeroLe _
  · refine ⟨.finite (NNReal.div budgetValue massValue), True.intro,
      NNReal.divPositive budgetPositive ((NNReal.zeroLtIffNeZero massValue).mpr zero), ?_⟩
    change NNReal.le (NNReal.mul (NNReal.div budgetValue massValue) massValue) budgetValue
    rw [NNReal.divMulCancel budgetValue zero]
    exact NNReal.leRefl _

end Foundations.Real.ENNReal
