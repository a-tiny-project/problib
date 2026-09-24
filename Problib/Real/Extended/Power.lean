module

public import Problib.Real.Extended.Conversion

set_option autoImplicit false

namespace Problib.Real.ENNReal

/-- Positive finite scaling commutes with indexed infima. -/
private theorem mul_iInf_of_finite_positive (factor : ENNReal)
    (factorFinite : Finite factor) (factorPositive : lt zero factor)
    (values : Nat → ENNReal) :
    mul factor (iInf values) = iInf (fun index => mul factor (values index)) := by
  apply le_antisymm
  · apply le_iInf
    intro index
    exact mul_le_mul_left (iInf_le values index) factor
  · rcases exists_finite_of_finite factorFinite with ⟨underlying, rfl⟩
    have nonzero : underlying ≠ NNReal.zero :=
      (NNReal.zero_lt_iff_ne_zero underlying).mp factorPositive
    let result := iInf (fun index => mul (finite underlying) (values index))
    let quotient : ENNReal := match result with
      | .finite value => .finite (NNReal.div value underlying)
      | .top => .top
    have reconstruct : mul (finite underlying) quotient = result := by
      cases h : result with
      | finite value =>
          dsimp [quotient]
          rw [h, finite_mul_finite, NNReal.mul_div_cancel value nonzero]
      | top =>
          dsimp [quotient]
          rw [h, finite_mul_top_of_ne_zero nonzero]
    have lower : le quotient (iInf values) := by
      apply le_iInf
      intro index
      apply (mul_le_mul_left_iff (factor := finite underlying) True.intro factorPositive).mp
      rw [reconstruct]
      exact iInf_le (fun index => mul (finite underlying) (values index)) index
    change le result (mul (finite underlying) (iInf values))
    rw [← reconstruct]
    exact mul_le_mul_left lower (finite underlying)

/-- Natural powers of an extended nonnegative real. -/
@[expose] public noncomputable def pow (base : ENNReal) : Nat → ENNReal
  | 0 => one
  | count + 1 => mul base (pow base count)

@[simp] public theorem pow_zero (base : ENNReal) : pow base 0 = one := rfl

@[simp] public theorem pow_succ (base : ENNReal) (count : Nat) :
    pow base (count + 1) = mul base (pow base count) := rfl

/-- The power at a sum is the product of the two powers. -/
public theorem pow_add (base : ENNReal) (first second : Nat) :
    pow base (first + second) =
      mul (pow base first) (pow base second) := by
  induction first with
  | zero =>
      rw [Nat.zero_add, pow_zero, one_mul]
  | succ first induction =>
      rw [Nat.succ_add, pow_succ, induction, pow_succ, mul_assoc]

/-- The unit base remains one at every natural power. -/
public theorem pow_one (count : Nat) : pow one count = one := by
  induction count with
  | zero => rfl
  | succ count induction => rw [pow_succ, induction, one_mul]

/-- Every positive power of zero is zero. -/
public theorem pow_zero_succ (count : Nat) : pow zero (count + 1) = zero := by
  rw [pow_succ, zero_mul]

/-- Natural powers preserve the order of nonnegative bases. -/
public theorem pow_le_pow {left right : ENNReal} (included : le left right)
    (count : Nat) : le (pow left count) (pow right count) := by
  induction count with
  | zero => exact le_refl one
  | succ count induction =>
      rw [pow_succ, pow_succ]
      exact mul_le_mul included induction

/-- Powers of a base at most one decrease with the exponent. -/
public theorem pow_antitone {base : ENNReal} (atMostOne : le base one)
    {first second : Nat} (included : first ≤ second) :
    le (pow base second) (pow base first) := by
  have step (count : Nat) : le (pow base (count + 1)) (pow base count) := by
    rw [pow_succ]
    simpa only [one_mul] using mul_le_mul_right atMostOne (pow base count)
  induction included with
  | refl => exact le_refl _
  | @step count _ induction => exact le_trans (step count) induction

/-- Powers of a base strictly below one have infimum zero. -/
public theorem iInf_pow_eq_zero {base : ENNReal} (belowOne : lt base one) :
    iInf (pow base) = zero := by
  have finiteBase : Finite base := finite_of_le belowOne.left True.intro
  have atMostOne := belowOne.left
  by_cases baseZero : base = zero
  · apply le_antisymm
    · exact le_trans (iInf_le (pow base) 1) (by rw [baseZero, pow_zero_succ]; exact le_refl zero)
    · exact zero_le _
  · have positiveBase : lt zero base := zero_lt_iff_ne_zero.mpr baseZero
    let limit := iInf (pow base)
    have limitFinite : Finite limit := by
      apply finite_of_le (iInf_le (pow base) 0)
      exact True.intro
    have fixed : mul base limit = limit := by
      calc
        mul base limit = iInf (fun index => mul base (pow base index)) :=
          mul_iInf_of_finite_positive base finiteBase positiveBase (pow base)
        _ = iInf (fun index => pow base (index + 1)) := by
          apply congrArg iInf
          funext index
          rw [pow_succ]
        _ = limit := by
          simpa only [Nat.add_comm] using
            iInf_tail (pow base) (fun {first second} included =>
              pow_antitone atMostOne included) 1
    apply Classical.byContradiction
    intro nonzero
    have positiveLimit : lt zero limit := zero_lt_iff_ne_zero.mpr nonzero
    have reverse : le one base := by
      apply (mul_le_mul_right_iff limitFinite positiveLimit).mp
      rw [one_mul, fixed]
      exact le_refl limit
    exact belowOne.right reverse

/-- Geometric powers eventually fall below every positive tolerance. -/
public theorem pow_eventually_lt {base tolerance : ENNReal}
    (belowOne : lt base one) (positive : lt zero tolerance) :
    ∃ stage : Nat, ∀ index : Nat, stage ≤ index →
      lt (pow base index) tolerance := by
  have infLess : lt (iInf (pow base)) tolerance := by
    rw [iInf_pow_eq_zero belowOne]
    exact positive
  rcases exists_index_less_of_iInf_lt infLess with ⟨stage, small⟩
  refine ⟨stage, fun index later => ?_⟩
  have decreased := pow_antitone belowOne.left later
  exact ⟨le_trans decreased small.left,
    fun reverse => small.right (le_trans reverse decreased)⟩

end Problib.Real.ENNReal
