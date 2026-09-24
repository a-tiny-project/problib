module

public import Problib.Real.Nonnegative.Embedding

set_option autoImplicit false

namespace Problib.Real

namespace NNReal

public theorem add_eq_zero_iff {left right : NNReal} :
    add left right = zero ↔ left = zero ∧ right = zero := by
  constructor
  · intro equal
    have leftSum : le left (add left right) := by
      simpa only [add_zero] using add_le_add_left (zero_le right) left
    have rightSum : le right (add left right) := by
      simpa only [zero_add] using add_le_add_right (zero_le left) right
    rw [equal] at leftSum rightSum
    exact ⟨le_antisymm leftSum (zero_le left),
      le_antisymm rightSum (zero_le right)⟩
  · rintro ⟨leftZero, rightZero⟩
    rw [leftZero, rightZero, zero_add]

public theorem one_ne_zero : one ≠ zero := by
  intro equal
  apply Construction.Dedekind.one_ne_zero
  simpa only [toReal_one, toReal_zero] using congrArg toReal equal

public theorem add_lt_add_right_iff {left right shift : NNReal} :
    lt (add left shift) (add right shift) ↔ lt left right := by
  change Construction.Dedekind.lt
      (Construction.Dedekind.add (toReal left) (toReal shift))
      (Construction.Dedekind.add (toReal right) (toReal shift)) ↔
    Construction.Dedekind.lt (toReal left) (toReal right)
  exact Construction.Dedekind.add_lt_add_right_iff

public theorem add_lt_add_left_iff {left right shift : NNReal} :
    lt (add shift left) (add shift right) ↔ lt left right := by
  change Construction.Dedekind.lt
      (Construction.Dedekind.add (toReal shift) (toReal left))
      (Construction.Dedekind.add (toReal shift) (toReal right)) ↔
    Construction.Dedekind.lt (toReal left) (toReal right)
  exact Construction.Dedekind.add_lt_add_left_iff

public theorem add_positive_left {left right : NNReal}
    (leftPositive : lt zero left) : lt zero (add left right) := by
  apply lt_of_lt_of_le leftPositive
  simpa only [add_zero] using add_le_add_left (zero_le right) left

public theorem add_positive_right {left right : NNReal}
    (rightPositive : lt zero right) : lt zero (add left right) := by
  rw [add_comm]
  exact add_positive_left rightPositive

public theorem mul_positive {left right : NNReal}
    (leftPositive : lt zero left) (rightPositive : lt zero right) :
    lt zero (mul left right) := by
  change Construction.Dedekind.lt Construction.Dedekind.zero
    (Construction.Dedekind.mul (toReal left) (toReal right))
  exact Construction.Dedekind.mul_positive leftPositive rightPositive

public theorem toReal_ne_zero {value : NNReal} (nonzero : value ≠ zero) :
    toReal value ≠ Construction.Dedekind.zero := by
  intro equal
  apply nonzero
  apply ext
  rw [equal, toReal_zero]

public theorem mul_left_cancel {factor left right : NNReal}
    (factorNonzero : factor ≠ zero)
    (equal : mul factor left = mul factor right) : left = right := by
  apply ext
  apply Construction.Dedekind.mul_left_cancel_of_nonzero
    (toReal_ne_zero factorNonzero)
  simpa only [toReal_mul] using congrArg toReal equal

public theorem mul_right_cancel {factor left right : NNReal}
    (factorNonzero : factor ≠ zero)
    (equal : mul left factor = mul right factor) : left = right := by
  apply ext
  apply Construction.Dedekind.mul_right_cancel_of_nonzero
    (toReal_ne_zero factorNonzero)
  simpa only [toReal_mul] using congrArg toReal equal

private theorem positive_real_nonzero {value : NNReal}
    (positive : lt zero value) : toReal value ≠ Construction.Dedekind.zero := by
  exact toReal_ne_zero ((zero_lt_iff_ne_zero value).mp positive)

public theorem le_of_mul_le_mul_left {factor left right : NNReal}
    (factorPositive : lt zero factor)
    (included : le (mul factor left) (mul factor right)) :
    le left right := by
  have inverseNonnegative : Construction.Dedekind.le
      Construction.Dedekind.zero
      (Construction.Dedekind.inverse (toReal factor)) := by
    rw [Construction.Dedekind.inverse_of_positive factorPositive]
    exact Construction.Dedekind.positiveInverse_nonnegative (toReal factor) factorPositive
  have productIncluded : Construction.Dedekind.le
      (Construction.Dedekind.mul (toReal factor) (toReal left))
      (Construction.Dedekind.mul (toReal factor) (toReal right)) := by
    change Construction.Dedekind.le
      (toReal (mul factor left)) (toReal (mul factor right)) at included
    rw [toReal_mul, toReal_mul] at included
    exact included
  have scaled := Construction.Dedekind.mul_le_mul_nonnegative_left
    productIncluded inverseNonnegative
  rw [← Construction.Dedekind.mul_assoc, Construction.Dedekind.inverse_mul_cancel
      (positive_real_nonzero factorPositive),
    Construction.Dedekind.mul_comm
      Construction.Dedekind.one (toReal left),
    Construction.Dedekind.mul_one,
    ← Construction.Dedekind.mul_assoc, Construction.Dedekind.inverse_mul_cancel
      (positive_real_nonzero factorPositive),
    Construction.Dedekind.mul_comm
      Construction.Dedekind.one (toReal right),
    Construction.Dedekind.mul_one] at scaled
  exact scaled

public theorem mul_le_mul_left_iff {factor left right : NNReal}
    (factorPositive : lt zero factor) :
    le (mul factor left) (mul factor right) ↔ le left right :=
  ⟨le_of_mul_le_mul_left factorPositive,
    fun included => mul_le_mul_left included factor⟩

public theorem le_of_mul_le_mul_right {factor left right : NNReal}
    (factorPositive : lt zero factor)
    (included : le (mul left factor) (mul right factor)) :
    le left right := by
  rw [mul_comm left factor, mul_comm right factor] at included
  exact le_of_mul_le_mul_left factorPositive included

public theorem mul_le_mul_right_iff {factor left right : NNReal}
    (factorPositive : lt zero factor) :
    le (mul left factor) (mul right factor) ↔ le left right :=
  ⟨le_of_mul_le_mul_right factorPositive,
    fun included => mul_le_mul_right included factor⟩

public theorem sub_of_le {left right : NNReal} (included : le right left) :
    toReal (sub left right) = Construction.Dedekind.sub (toReal left) (toReal right) := by
  classical
  unfold sub toReal
  simp only [dif_pos included]

public theorem sub_eq_zero_of_le {left right : NNReal}
    (included : le left right) : sub left right = zero := by
  by_cases reverse : le right left
  · have equal := le_antisymm included reverse
    subst right
    apply ext
    rw [sub_of_le (le_refl left), Construction.Dedekind.sub_eq_add_neg,
      Construction.Dedekind.add_neg, toReal_zero]
  · classical
    unfold sub
    simp only [dif_neg reverse]

public theorem sub_self (value : NNReal) : sub value value = zero :=
  sub_eq_zero_of_le (le_refl value)

public theorem sub_zero (value : NNReal) : sub value zero = value := by
  apply ext
  rw [sub_of_le (zero_le value), toReal_zero,
    Construction.Dedekind.sub_eq_add_neg,
    Construction.Dedekind.neg_zero, Construction.Dedekind.add_zero]

public theorem zero_sub (value : NNReal) : sub zero value = zero :=
  sub_eq_zero_of_le (zero_le value)

public theorem sub_add_cancel {left right : NNReal}
    (included : le right left) : add (sub left right) right = left := by
  apply ext
  rw [toReal_add, sub_of_le included,
    Construction.Dedekind.sub_eq_add_neg,
    Construction.Dedekind.add_assoc,
    Construction.Dedekind.add_comm
      (Construction.Dedekind.neg (toReal right)),
    Construction.Dedekind.add_neg, Construction.Dedekind.add_zero]

public theorem add_sub_cancel_right (left right : NNReal) :
    sub (add left right) right = left := by
  have included : le right (add left right) := by
    calc
      le right (add right left) := by
        simpa only [add_zero] using add_le_add_left (zero_le left) right
      _ = add left right := add_comm right left
  apply add_right_cancel (right := right)
  rw [sub_add_cancel included]

public theorem add_sub_cancel_left (left right : NNReal) :
    sub (add left right) left = right := by
  rw [add_comm]
  exact add_sub_cancel_right right left

public theorem sub_eq_zero_iff_le {left right : NNReal} :
    sub left right = zero ↔ le left right := by
  constructor
  · intro equal
    rcases le_total left right with included | reverse
    · exact included
    · have restored := sub_add_cancel reverse
      rw [equal, zero_add] at restored
      rw [restored]
      exact le_refl left
  · exact sub_eq_zero_of_le

public theorem sub_le_self (left right : NNReal) : le (sub left right) left := by
  by_cases included : le right left
  · change Construction.Dedekind.le (toReal (sub left right)) (toReal left)
    rw [sub_of_le included, Construction.Dedekind.sub_eq_add_neg]
    have negNonpositive : Construction.Dedekind.le
        (Construction.Dedekind.neg (toReal right))
        Construction.Dedekind.zero := by
      rw [← Construction.Dedekind.neg_zero]
      exact (Construction.Dedekind.neg_le_neg_iff).mpr right.property
    have shifted :=
      (Construction.Dedekind.add_le_add_left_iff
        (left := Construction.Dedekind.neg (toReal right))
        (right := Construction.Dedekind.zero)
        (shift := toReal left)).mpr negNonpositive
    simpa only [Construction.Dedekind.add_zero] using shifted
  · classical
    unfold sub
    simp only [dif_neg included]
    exact zero_le left

public theorem sub_le_iff_le_add {left right upper : NNReal} :
    le (sub left right) upper ↔ le left (add upper right) := by
  by_cases included : le right left
  · constructor
    · intro differenceUpper
      have shifted := add_le_add_right differenceUpper right
      rw [sub_add_cancel included] at shifted
      exact shifted
    · intro leftUpper
      apply (add_le_add_right_iff).mp
      rw [sub_add_cancel included]
      exact leftUpper
  · have leftRight : le left right := by
      rcases le_total left right with leftRight | rightLeft
      · exact leftRight
      · exact False.elim (included rightLeft)
    constructor
    · intro _
      exact le_trans leftRight (by
        simpa only [zero_add] using add_le_add_right (zero_le upper) right)
    · intro _
      rw [sub_eq_zero_of_le leftRight]
      exact zero_le upper

public theorem le_sub_iff_add_le {left middle right : NNReal}
    (included : le right middle) :
    le left (sub middle right) ↔ le (add left right) middle := by
  constructor
  · intro leftDifference
    have shifted := add_le_add_right leftDifference right
    rw [sub_add_cancel included] at shifted
    exact shifted
  · intro shifted
    rw [← sub_add_cancel included] at shifted
    exact (add_le_add_right_iff).mp shifted

@[expose] public noncomputable def div (left right : NNReal) : NNReal :=
  ⟨Construction.Dedekind.div (toReal left) (toReal right),
    Construction.Dedekind.div_nonnegative left.property right.property⟩

public theorem toReal_div (left right : NNReal) :
    toReal (div left right) =
      Construction.Dedekind.div (toReal left) (toReal right) :=
  rfl

public theorem div_positive {left right : NNReal}
    (leftPositive : lt zero left) (rightPositive : lt zero right) :
    lt zero (div left right) := by
  change Construction.Dedekind.lt Construction.Dedekind.zero
    (Construction.Dedekind.div (toReal left) (toReal right))
  exact Construction.Dedekind.div_positive leftPositive rightPositive

public theorem div_mul_cancel (left : NNReal) {right : NNReal}
    (rightNonzero : right ≠ zero) : mul (div left right) right = left := by
  apply ext
  rw [toReal_mul, toReal_div]
  exact Construction.Dedekind.div_mul_cancel
    (toReal left) (toReal_ne_zero rightNonzero)

public theorem mul_div_cancel (left : NNReal) {right : NNReal}
    (rightNonzero : right ≠ zero) : mul right (div left right) = left := by
  apply ext
  rw [toReal_mul, toReal_div]
  exact Construction.Dedekind.mul_div_cancel
    (toReal left) (toReal_ne_zero rightNonzero)

public theorem div_self {value : NNReal} (nonzero : value ≠ zero) :
    div value value = one := by
  apply ext
  rw [toReal_div, toReal_one]
  exact Construction.Dedekind.div_self (toReal_ne_zero nonzero)

public theorem div_one (value : NNReal) : div value one = value := by
  apply ext
  rw [toReal_div, toReal_one]
  exact Construction.Dedekind.div_one (toReal value)

public theorem zero_div (value : NNReal) : div zero value = zero := by
  apply ext
  change Construction.Dedekind.div Construction.Dedekind.zero
    (toReal value) = Construction.Dedekind.zero
  exact Construction.Dedekind.zero_div (toReal value)

@[expose] public noncomputable def two : NNReal :=
  add one one

public theorem one_positive : lt zero one :=
  (zero_lt_iff_ne_zero one).mpr one_ne_zero

public theorem two_positive : lt zero two :=
  add_positive_left one_positive

public theorem two_ne_zero : two ≠ zero :=
  (zero_lt_iff_ne_zero two).mp two_positive

@[expose] public noncomputable def half (value : NNReal) : NNReal :=
  div value two

public theorem half_positive {value : NNReal} (positive : lt zero value) :
    lt zero (half value) :=
  div_positive positive two_positive

public theorem half_add_half (value : NNReal) :
    add (half value) (half value) = value := by
  calc
    add (half value) (half value) =
        add (mul (half value) one) (mul (half value) one) := by
      rw [mul_one]
    _ = mul (half value) (add one one) :=
      (mul_add (half value) one one).symm
    _ = mul (div value two) two := rfl
    _ = value := div_mul_cancel value two_ne_zero

public theorem le_of_forall_positive_le_add {left right : NNReal}
    (approaches : ∀ error, lt zero error → le left (add right error)) :
    le left right := by
  apply Classical.byContradiction
  intro notIncluded
  have reverse : le right left := by
    rcases le_total left right with included | reverse
    · exact False.elim (notIncluded included)
    · exact reverse
  let difference := sub left right
  have differenceNonzero : difference ≠ zero := by
    intro equal
    exact notIncluded ((sub_eq_zero_iff_le).mp equal)
  have differencePositive : lt zero difference :=
    (zero_lt_iff_ne_zero difference).mpr differenceNonzero
  let error := half difference
  have errorPositive : lt zero error := half_positive differencePositive
  have assumed := approaches error errorPositive
  have differenceLeError : le difference error := by
    apply (add_le_add_right_iff).mp
    rw [sub_add_cancel reverse, add_comm error right]
    exact assumed
  have errorLessDifference : lt error difference := by
    rw [← half_add_half difference]
    have shifted :=
      (add_lt_add_left_iff (left := zero) (right := error)
        (shift := error)).mpr errorPositive
    simpa only [add_zero] using shifted
  exact errorLessDifference.right differenceLeError

end NNReal

end Problib.Real
