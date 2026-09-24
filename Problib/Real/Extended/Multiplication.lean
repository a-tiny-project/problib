module

public import Problib.Real.Extended.Additive

namespace Problib.Real.ENNReal

set_option autoImplicit false

@[expose] public noncomputable def mul (left right : ENNReal) : ENNReal := by
  classical
  exact match left, right with
  | .finite leftValue, .finite rightValue =>
      .finite (NNReal.mul leftValue rightValue)
  | .finite value, .top => if value = NNReal.zero then zero else top
  | .top, .finite value => if value = NNReal.zero then zero else top
  | .top, .top => top

public theorem finite_mul_finite (left right : NNReal) :
    mul (finite left) (finite right) = finite (NNReal.mul left right) := by
  classical
  rfl

/-- The product of two finite extended-nonnegative values is finite. -/
public theorem mul_finite {left right : ENNReal}
    (leftFinite : Finite left) (rightFinite : Finite right) : Finite (mul left right) := by
  rcases exists_finite_of_finite leftFinite with ⟨leftValue, rfl⟩
  rcases exists_finite_of_finite rightFinite with ⟨rightValue, rfl⟩
  exact True.intro

public theorem finite_mul_top_of_eq_zero {value : NNReal}
    (equal : value = NNReal.zero) : mul (finite value) top = zero := by
  classical
  unfold mul
  simp only [if_pos equal]

public theorem finite_mul_top_of_ne_zero {value : NNReal}
    (nonzero : value ≠ NNReal.zero) : mul (finite value) top = top := by
  classical
  unfold mul
  simp only [if_neg nonzero]

public theorem top_mul_finite_of_eq_zero {value : NNReal}
    (equal : value = NNReal.zero) : mul top (finite value) = zero := by
  classical
  unfold mul
  simp only [if_pos equal]

public theorem top_mul_finite_of_ne_zero {value : NNReal}
    (nonzero : value ≠ NNReal.zero) : mul top (finite value) = top := by
  classical
  unfold mul
  simp only [if_neg nonzero]

public theorem top_mul_top : mul top top = top := by
  classical
  rfl

public theorem mul_comm (left right : ENNReal) : mul left right = mul right left := by
  cases left with
  | top => cases right <;> rfl
  | finite leftValue =>
      cases right with
      | top => rfl
      | finite rightValue =>
          exact congrArg finite (NNReal.mul_comm leftValue rightValue)

public theorem mul_zero (value : ENNReal) : mul value zero = zero := by
  classical
  cases value with
  | top => exact top_mul_finite_of_eq_zero rfl
  | finite underlying => exact congrArg finite (NNReal.mul_zero underlying)

public theorem zero_mul (value : ENNReal) : mul zero value = zero := by
  rw [mul_comm, mul_zero]

public theorem mul_top_of_ne_zero {value : ENNReal} (nonzero : value ≠ zero) :
    mul value top = top := by
  classical
  cases value with
  | top => rfl
  | finite underlying =>
      have underlyingNonzero : underlying ≠ NNReal.zero := by
        intro equal
        apply nonzero
        exact congrArg finite equal
      exact finite_mul_top_of_ne_zero underlyingNonzero

public theorem top_mul_of_ne_zero {value : ENNReal} (nonzero : value ≠ zero) :
    mul top value = top := by
  rw [mul_comm]
  exact mul_top_of_ne_zero nonzero

public theorem mul_eq_zero_iff {left right : ENNReal} :
    mul left right = zero ↔ left = zero ∨ right = zero := by
  classical
  cases left with
  | top =>
      cases right with
      | top =>
          rw [top_mul_top]
          constructor
          · intro equal
            exact False.elim (top_ne_finite NNReal.zero equal)
          · rintro (leftZero | rightZero)
            · exact False.elim (top_ne_finite NNReal.zero leftZero)
            · exact False.elim (top_ne_finite NNReal.zero rightZero)
      | finite rightValue =>
          by_cases rightZero : rightValue = NNReal.zero
          · subst rightValue
            rw [top_mul_finite_of_eq_zero rfl]
            exact ⟨fun _ => Or.inr rfl, fun _ => rfl⟩
          · constructor
            · intro equal
              rw [top_mul_finite_of_ne_zero rightZero] at equal
              exact False.elim (top_ne_finite NNReal.zero equal)
            · rintro (leftZero | rightEqual)
              · exact False.elim (top_ne_finite NNReal.zero leftZero)
              · exact False.elim (rightZero (finite_injective rightEqual))
  | finite leftValue =>
      cases right with
      | top =>
          by_cases leftZero : leftValue = NNReal.zero
          · subst leftValue
            rw [finite_mul_top_of_eq_zero rfl]
            exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
          · constructor
            · intro equal
              rw [finite_mul_top_of_ne_zero leftZero] at equal
              exact False.elim (top_ne_finite NNReal.zero equal)
            · rintro (leftEqual | rightZero)
              · exact False.elim (leftZero (finite_injective leftEqual))
              · exact False.elim (top_ne_finite NNReal.zero rightZero)
      | finite rightValue =>
          constructor
          · intro equal
            rcases (NNReal.mul_eq_zero_iff.mp (finite_injective equal)) with
              leftZero | rightZero
            · exact Or.inl (congrArg finite leftZero)
            · exact Or.inr (congrArg finite rightZero)
          · rintro (leftZero | rightZero)
            · exact congrArg finite
                ((NNReal.mul_eq_zero_iff).mpr (Or.inl (finite_injective leftZero)))
            · exact congrArg finite
                ((NNReal.mul_eq_zero_iff).mpr (Or.inr (finite_injective rightZero)))

private theorem nnreal_mul_ne_zero {left right : NNReal}
    (leftNonzero : left ≠ NNReal.zero)
    (rightNonzero : right ≠ NNReal.zero) :
    NNReal.mul left right ≠ NNReal.zero := by
  intro equal
  rcases NNReal.mul_eq_zero_iff.mp equal with leftZero | rightZero
  · exact leftNonzero leftZero
  · exact rightNonzero rightZero

public theorem mul_assoc (left middle right : ENNReal) :
    mul (mul left middle) right = mul left (mul middle right) := by
  by_cases leftZero : left = zero
  · subst left
    rw [zero_mul, zero_mul, zero_mul]
  · by_cases middleZero : middle = zero
    · subst middle
      calc
        mul (mul left zero) right = mul zero right :=
          congrArg (fun value => mul value right) (mul_zero left)
        _ = zero := zero_mul right
        _ = mul left zero := (mul_zero left).symm
        _ = mul left (mul zero right) :=
          congrArg (mul left) (zero_mul right).symm
    · by_cases rightZero : right = zero
      · subst right
        rw [mul_zero, mul_zero, mul_zero]
      · have leftMiddleNonzero : mul left middle ≠ zero := by
          intro equal
          rcases mul_eq_zero_iff.mp equal with equal | equal
          · exact leftZero equal
          · exact middleZero equal
        have middleRightNonzero : mul middle right ≠ zero := by
          intro equal
          rcases mul_eq_zero_iff.mp equal with equal | equal
          · exact middleZero equal
          · exact rightZero equal
        cases left with
        | top =>
            rw [top_mul_of_ne_zero middleZero, top_mul_of_ne_zero rightZero,
              top_mul_of_ne_zero middleRightNonzero]
        | finite leftValue =>
            cases middle with
            | top =>
                rw [mul_top_of_ne_zero leftZero, top_mul_of_ne_zero rightZero]
                exact (mul_top_of_ne_zero leftZero).symm
            | finite middleValue =>
                cases right with
                | top =>
                    rw [mul_top_of_ne_zero leftMiddleNonzero,
                      mul_top_of_ne_zero middleZero, mul_top_of_ne_zero leftZero]
                | finite rightValue =>
                    exact congrArg finite
                      (NNReal.mul_assoc leftValue middleValue rightValue)


/-- The middle factors of a product of products swap. -/
public theorem mul_mul_mul_comm (first second third fourth : ENNReal) :
    mul (mul first second) (mul third fourth) =
      mul (mul first third) (mul second fourth) := by
  rw [mul_assoc, ← mul_assoc second third, mul_comm second third,
    mul_assoc third second, ← mul_assoc]
public theorem one_ne_zero : one ≠ zero := by
  intro equal
  exact NNReal.one_ne_zero (finite_injective equal)

public theorem mul_one (value : ENNReal) : mul value one = value := by
  classical
  cases value with
  | top => exact top_mul_finite_of_ne_zero NNReal.one_ne_zero
  | finite underlying => exact congrArg finite (NNReal.mul_one underlying)

public theorem one_mul (value : ENNReal) : mul one value = value := by
  rw [mul_comm, mul_one]

public theorem mul_add (factor left right : ENNReal) :
    mul factor (add left right) =
      add (mul factor left) (mul factor right) := by
  by_cases factorZero : factor = zero
  · subst factor
    rw [zero_mul, zero_mul, zero_mul, zero_add]
  · cases factor with
    | top =>
        by_cases leftZero : left = zero
        · subst left
          rw [zero_add, mul_zero, zero_add]
        · by_cases rightZero : right = zero
          · subst right
            rw [add_zero, mul_zero, add_zero]
          · have sumNonzero : add left right ≠ zero := by
              intro equal
              rcases add_eq_zero_iff.mp equal with ⟨leftEqual, rightEqual⟩
              exact leftZero leftEqual
            rw [top_mul_of_ne_zero sumNonzero, top_mul_of_ne_zero leftZero,
              top_mul_of_ne_zero rightZero, top_add]
    | finite factorValue =>
        cases left with
        | top =>
            rw [top_add, mul_top_of_ne_zero factorZero, top_add]
        | finite leftValue =>
            cases right with
            | top =>
                rw [add_top, mul_top_of_ne_zero factorZero, add_top]
            | finite rightValue =>
                exact congrArg finite
                  (NNReal.mul_add factorValue leftValue rightValue)

public noncomputable def semiring :
    Problib.Algebra.CommutativeSemiringLaws ENNReal where
  additive := {
    zero := zero
    add := add
    add_comm := add_comm
    add_assoc := add_assoc
    add_zero := add_zero
  }
  multiplicative := {
    one := one
    mul := mul
    mul_comm := mul_comm
    mul_assoc := mul_assoc
    mul_one := mul_one
  }
  zero_mul := zero_mul
  mul_add := mul_add

public theorem mul_le_mul_right {left right : ENNReal}
    (included : le left right) (factor : ENNReal) :
    le (mul left factor) (mul right factor) := by
  classical
  cases factor with
  | top =>
      cases left with
      | top =>
          cases right with
          | top => exact le_refl top
          | finite _ => exact False.elim included
      | finite leftValue =>
          cases right with
          | top => exact le_top _
          | finite rightValue =>
              by_cases leftZero : leftValue = NNReal.zero
              · simp only [mul, if_pos leftZero]
                exact zero_le _
              · have rightNonzero : rightValue ≠ NNReal.zero := by
                  intro rightZero
                  subst rightValue
                  exact leftZero (NNReal.le_antisymm included
                    (NNReal.zero_le leftValue))
                simp only [mul, if_neg leftZero, if_neg rightNonzero]
                exact le_refl top
  | finite factorValue =>
      by_cases factorZero : factorValue = NNReal.zero
      · subst factorValue
        simpa only [show finite NNReal.zero = zero from rfl,
          mul_zero] using le_refl zero
      · cases left with
        | top =>
            cases right with
            | top => exact le_refl (mul top (finite factorValue))
            | finite _ => exact False.elim included
        | finite leftValue =>
            cases right with
            | top =>
                simp only [mul, if_neg factorZero]
                exact le_top _
            | finite rightValue =>
                exact NNReal.mul_le_mul_right included factorValue

public theorem mul_le_mul_left {left right : ENNReal}
    (included : le left right) (factor : ENNReal) :
    le (mul factor left) (mul factor right) := by
  rw [mul_comm factor left, mul_comm factor right]
  exact mul_le_mul_right included factor

public theorem mul_le_mul {firstLeft firstRight secondLeft secondRight : ENNReal}
    (firstIncluded : le firstLeft firstRight)
    (secondIncluded : le secondLeft secondRight) :
    le (mul firstLeft secondLeft) (mul firstRight secondRight) :=
  le_trans (mul_le_mul_right firstIncluded secondLeft)
    (mul_le_mul_left secondIncluded firstRight)

/-- Multiplication on the right by a finite positive extended real reflects
and preserves the non-strict order. -/
public theorem mul_le_mul_right_iff {factor left right : ENNReal}
    (factorFinite : Finite factor) (factorPositive : lt zero factor) :
    le (mul left factor) (mul right factor) ↔ le left right := by
  constructor
  · intro included
    rcases exists_finite_of_finite factorFinite with ⟨factorValue, rfl⟩
    cases left with
    | finite leftValue =>
        cases right with
        | finite rightValue =>
            exact NNReal.le_of_mul_le_mul_right factorPositive included
        | top => exact le_top _
    | top =>
        cases right with
        | finite rightValue =>
            rw [top_mul_of_ne_zero (zero_lt_iff_ne_zero.mp factorPositive)] at included
            exact False.elim included
        | top => exact le_refl _
  · intro included
    exact mul_le_mul_right included factor

/-- Multiplication on the left by a finite positive extended real reflects
and preserves the non-strict order. -/
public theorem mul_le_mul_left_iff {factor left right : ENNReal}
    (factorFinite : Finite factor) (factorPositive : lt zero factor) :
    le (mul factor left) (mul factor right) ↔ le left right := by
  rw [mul_comm factor left, mul_comm factor right]
  exact mul_le_mul_right_iff factorFinite factorPositive

/-- A finite mass and positive finite budget admit a positive finite scale
fitting within that budget. -/
public theorem exists_positive_scale {mass budget : ENNReal}
    (massFinite : ENNReal.Finite mass) (budgetFinite : ENNReal.Finite budget)
    (budgetPositive : ENNReal.lt ENNReal.zero budget) :
    ∃ factor, ENNReal.Finite factor ∧ ENNReal.lt ENNReal.zero factor ∧
      ENNReal.le (ENNReal.mul factor mass) budget := by
  rcases ENNReal.exists_finite_of_finite massFinite with ⟨massValue, rfl⟩
  rcases ENNReal.exists_finite_of_finite budgetFinite with ⟨budgetValue, rfl⟩
  by_cases zero : massValue = NNReal.zero
  · refine ⟨ENNReal.one, True.intro, NNReal.one_positive, ?_⟩
    rw [zero]
    change ENNReal.le (ENNReal.mul ENNReal.one ENNReal.zero) (.finite budgetValue)
    rw [ENNReal.mul_zero]
    exact ENNReal.zero_le _
  · refine ⟨.finite (NNReal.div budgetValue massValue), True.intro,
      NNReal.div_positive budgetPositive ((NNReal.zero_lt_iff_ne_zero massValue).mpr zero), ?_⟩
    change NNReal.le (NNReal.mul (NNReal.div budgetValue massValue) massValue) budgetValue
    rw [NNReal.div_mul_cancel budgetValue zero]
    exact NNReal.le_refl _

end Problib.Real.ENNReal
