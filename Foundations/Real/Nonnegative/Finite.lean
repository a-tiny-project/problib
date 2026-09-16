module

public import Foundations.Real.Nonnegative.Embedding

set_option autoImplicit false

namespace Foundations.Real

namespace NNReal

public theorem addEqZeroIff {left right : NNReal} :
    add left right = zero ↔ left = zero ∧ right = zero := by
  constructor
  · intro equal
    have leftSum : le left (add left right) := by
      simpa only [addZero] using addLeAddLeft (zeroLe right) left
    have rightSum : le right (add left right) := by
      simpa only [zeroAdd] using addLeAddRight (zeroLe left) right
    rw [equal] at leftSum rightSum
    exact ⟨leAntisymm leftSum (zeroLe left),
      leAntisymm rightSum (zeroLe right)⟩
  · rintro ⟨leftZero, rightZero⟩
    rw [leftZero, rightZero, zeroAdd]

public theorem oneNeZero : one ≠ zero := by
  intro equal
  apply Construction.Dedekind.oneNeZero
  simpa only [toRealOne, toRealZero] using congrArg toReal equal

public theorem addLtAddRightIff {left right shift : NNReal} :
    lt (add left shift) (add right shift) ↔ lt left right := by
  change Construction.Dedekind.lt
      (Construction.Dedekind.add (toReal left) (toReal shift))
      (Construction.Dedekind.add (toReal right) (toReal shift)) ↔
    Construction.Dedekind.lt (toReal left) (toReal right)
  exact Construction.Dedekind.addLtAddRightIff

public theorem addLtAddLeftIff {left right shift : NNReal} :
    lt (add shift left) (add shift right) ↔ lt left right := by
  change Construction.Dedekind.lt
      (Construction.Dedekind.add (toReal shift) (toReal left))
      (Construction.Dedekind.add (toReal shift) (toReal right)) ↔
    Construction.Dedekind.lt (toReal left) (toReal right)
  exact Construction.Dedekind.addLtAddLeftIff

public theorem addPositiveLeft {left right : NNReal}
    (leftPositive : lt zero left) : lt zero (add left right) := by
  apply ltOfLtOfLe leftPositive
  simpa only [addZero] using addLeAddLeft (zeroLe right) left

public theorem addPositiveRight {left right : NNReal}
    (rightPositive : lt zero right) : lt zero (add left right) := by
  rw [addComm]
  exact addPositiveLeft rightPositive

public theorem mulPositive {left right : NNReal}
    (leftPositive : lt zero left) (rightPositive : lt zero right) :
    lt zero (mul left right) := by
  change Construction.Dedekind.lt Construction.Dedekind.zero
    (Construction.Dedekind.mul (toReal left) (toReal right))
  exact Construction.Dedekind.mulPositive leftPositive rightPositive

public theorem toRealNeZero {value : NNReal} (nonzero : value ≠ zero) :
    toReal value ≠ Construction.Dedekind.zero := by
  intro equal
  apply nonzero
  apply ext
  rw [equal, toRealZero]

public theorem mulLeftCancel {factor left right : NNReal}
    (factorNonzero : factor ≠ zero)
    (equal : mul factor left = mul factor right) : left = right := by
  apply ext
  apply Construction.Dedekind.mulLeftCancelOfNonzero
    (toRealNeZero factorNonzero)
  simpa only [toRealMul] using congrArg toReal equal

public theorem mulRightCancel {factor left right : NNReal}
    (factorNonzero : factor ≠ zero)
    (equal : mul left factor = mul right factor) : left = right := by
  apply ext
  apply Construction.Dedekind.mulRightCancelOfNonzero
    (toRealNeZero factorNonzero)
  simpa only [toRealMul] using congrArg toReal equal

private theorem positiveRealNonzero {value : NNReal}
    (positive : lt zero value) : toReal value ≠ Construction.Dedekind.zero := by
  exact toRealNeZero ((zeroLtIffNeZero value).mp positive)

public theorem leOfMulLeMulLeft {factor left right : NNReal}
    (factorPositive : lt zero factor)
    (included : le (mul factor left) (mul factor right)) :
    le left right := by
  have inverseNonnegative : Construction.Dedekind.le
      Construction.Dedekind.zero
      (Construction.Dedekind.inverse (toReal factor)) := by
    rw [Construction.Dedekind.inverseOfPositive factorPositive]
    exact Construction.Dedekind.positiveInverseNonnegative (toReal factor) factorPositive
  have productIncluded : Construction.Dedekind.le
      (Construction.Dedekind.mul (toReal factor) (toReal left))
      (Construction.Dedekind.mul (toReal factor) (toReal right)) := by
    change Construction.Dedekind.le
      (toReal (mul factor left)) (toReal (mul factor right)) at included
    rw [toRealMul, toRealMul] at included
    exact included
  have scaled := Construction.Dedekind.mulLeMulNonnegativeLeft
    productIncluded inverseNonnegative
  rw [← Construction.Dedekind.mulAssoc, Construction.Dedekind.inverseMulCancel
      (positiveRealNonzero factorPositive),
    Construction.Dedekind.mulComm
      Construction.Dedekind.one (toReal left),
    Construction.Dedekind.mulOne,
    ← Construction.Dedekind.mulAssoc, Construction.Dedekind.inverseMulCancel
      (positiveRealNonzero factorPositive),
    Construction.Dedekind.mulComm
      Construction.Dedekind.one (toReal right),
    Construction.Dedekind.mulOne] at scaled
  exact scaled

public theorem mulLeMulLeftIff {factor left right : NNReal}
    (factorPositive : lt zero factor) :
    le (mul factor left) (mul factor right) ↔ le left right :=
  ⟨leOfMulLeMulLeft factorPositive,
    fun included => mulLeMulLeft included factor⟩

public theorem leOfMulLeMulRight {factor left right : NNReal}
    (factorPositive : lt zero factor)
    (included : le (mul left factor) (mul right factor)) :
    le left right := by
  rw [mulComm left factor, mulComm right factor] at included
  exact leOfMulLeMulLeft factorPositive included

public theorem mulLeMulRightIff {factor left right : NNReal}
    (factorPositive : lt zero factor) :
    le (mul left factor) (mul right factor) ↔ le left right :=
  ⟨leOfMulLeMulRight factorPositive,
    fun included => mulLeMulRight included factor⟩

public theorem subOfLe {left right : NNReal} (included : le right left) :
    toReal (sub left right) = Construction.Dedekind.sub (toReal left) (toReal right) := by
  classical
  unfold sub toReal
  simp only [dif_pos included]

public theorem subEqZeroOfLe {left right : NNReal}
    (included : le left right) : sub left right = zero := by
  by_cases reverse : le right left
  · have equal := leAntisymm included reverse
    subst right
    apply ext
    rw [subOfLe (leRefl left), Construction.Dedekind.subEqAddNeg,
      Construction.Dedekind.addNeg, toRealZero]
  · classical
    unfold sub
    simp only [dif_neg reverse]

public theorem subSelf (value : NNReal) : sub value value = zero :=
  subEqZeroOfLe (leRefl value)

public theorem subZero (value : NNReal) : sub value zero = value := by
  apply ext
  rw [subOfLe (zeroLe value), toRealZero,
    Construction.Dedekind.subEqAddNeg,
    Construction.Dedekind.negZero, Construction.Dedekind.addZero]

public theorem zeroSub (value : NNReal) : sub zero value = zero :=
  subEqZeroOfLe (zeroLe value)

public theorem subAddCancel {left right : NNReal}
    (included : le right left) : add (sub left right) right = left := by
  apply ext
  rw [toRealAdd, subOfLe included,
    Construction.Dedekind.subEqAddNeg,
    Construction.Dedekind.addAssoc,
    Construction.Dedekind.addComm
      (Construction.Dedekind.neg (toReal right)),
    Construction.Dedekind.addNeg, Construction.Dedekind.addZero]

public theorem addSubCancelRight (left right : NNReal) :
    sub (add left right) right = left := by
  have included : le right (add left right) := by
    calc
      le right (add right left) := by
        simpa only [addZero] using addLeAddLeft (zeroLe left) right
      _ = add left right := addComm right left
  apply addRightCancel (right := right)
  rw [subAddCancel included]

public theorem addSubCancelLeft (left right : NNReal) :
    sub (add left right) left = right := by
  rw [addComm]
  exact addSubCancelRight right left

public theorem subEqZeroIffLe {left right : NNReal} :
    sub left right = zero ↔ le left right := by
  constructor
  · intro equal
    rcases leTotal left right with included | reverse
    · exact included
    · have restored := subAddCancel reverse
      rw [equal, zeroAdd] at restored
      rw [restored]
      exact leRefl left
  · exact subEqZeroOfLe

public theorem subLeSelf (left right : NNReal) : le (sub left right) left := by
  by_cases included : le right left
  · change Construction.Dedekind.le (toReal (sub left right)) (toReal left)
    rw [subOfLe included, Construction.Dedekind.subEqAddNeg]
    have negNonpositive : Construction.Dedekind.le
        (Construction.Dedekind.neg (toReal right))
        Construction.Dedekind.zero := by
      rw [← Construction.Dedekind.negZero]
      exact (Construction.Dedekind.negLeNegIff).mpr right.property
    have shifted :=
      (Construction.Dedekind.addLeAddLeftIff
        (left := Construction.Dedekind.neg (toReal right))
        (right := Construction.Dedekind.zero)
        (shift := toReal left)).mpr negNonpositive
    simpa only [Construction.Dedekind.addZero] using shifted
  · classical
    unfold sub
    simp only [dif_neg included]
    exact zeroLe left

public theorem subLeIffLeAdd {left right upper : NNReal} :
    le (sub left right) upper ↔ le left (add upper right) := by
  by_cases included : le right left
  · constructor
    · intro differenceUpper
      have shifted := addLeAddRight differenceUpper right
      rw [subAddCancel included] at shifted
      exact shifted
    · intro leftUpper
      apply (addLeAddRightIff).mp
      rw [subAddCancel included]
      exact leftUpper
  · have leftRight : le left right := by
      rcases leTotal left right with leftRight | rightLeft
      · exact leftRight
      · exact False.elim (included rightLeft)
    constructor
    · intro _
      exact leTrans leftRight (by
        simpa only [zeroAdd] using addLeAddRight (zeroLe upper) right)
    · intro _
      rw [subEqZeroOfLe leftRight]
      exact zeroLe upper

public theorem leSubIffAddLe {left middle right : NNReal}
    (included : le right middle) :
    le left (sub middle right) ↔ le (add left right) middle := by
  constructor
  · intro leftDifference
    have shifted := addLeAddRight leftDifference right
    rw [subAddCancel included] at shifted
    exact shifted
  · intro shifted
    rw [← subAddCancel included] at shifted
    exact (addLeAddRightIff).mp shifted

@[expose] public noncomputable def div (left right : NNReal) : NNReal :=
  ⟨Construction.Dedekind.div (toReal left) (toReal right),
    Construction.Dedekind.divNonnegative left.property right.property⟩

public theorem toRealDiv (left right : NNReal) :
    toReal (div left right) =
      Construction.Dedekind.div (toReal left) (toReal right) :=
  rfl

public theorem divPositive {left right : NNReal}
    (leftPositive : lt zero left) (rightPositive : lt zero right) :
    lt zero (div left right) := by
  change Construction.Dedekind.lt Construction.Dedekind.zero
    (Construction.Dedekind.div (toReal left) (toReal right))
  exact Construction.Dedekind.divPositive leftPositive rightPositive

public theorem divMulCancel (left : NNReal) {right : NNReal}
    (rightNonzero : right ≠ zero) : mul (div left right) right = left := by
  apply ext
  rw [toRealMul, toRealDiv]
  exact Construction.Dedekind.divMulCancel
    (toReal left) (toRealNeZero rightNonzero)

public theorem mulDivCancel (left : NNReal) {right : NNReal}
    (rightNonzero : right ≠ zero) : mul right (div left right) = left := by
  apply ext
  rw [toRealMul, toRealDiv]
  exact Construction.Dedekind.mulDivCancel
    (toReal left) (toRealNeZero rightNonzero)

public theorem divSelf {value : NNReal} (nonzero : value ≠ zero) :
    div value value = one := by
  apply ext
  rw [toRealDiv, toRealOne]
  exact Construction.Dedekind.divSelf (toRealNeZero nonzero)

public theorem divOne (value : NNReal) : div value one = value := by
  apply ext
  rw [toRealDiv, toRealOne]
  exact Construction.Dedekind.divOne (toReal value)

public theorem zeroDiv (value : NNReal) : div zero value = zero := by
  apply ext
  change Construction.Dedekind.div Construction.Dedekind.zero
    (toReal value) = Construction.Dedekind.zero
  exact Construction.Dedekind.zeroDiv (toReal value)

@[expose] public noncomputable def two : NNReal :=
  add one one

public theorem onePositive : lt zero one :=
  (zeroLtIffNeZero one).mpr oneNeZero

public theorem twoPositive : lt zero two :=
  addPositiveLeft onePositive

public theorem twoNeZero : two ≠ zero :=
  (zeroLtIffNeZero two).mp twoPositive

@[expose] public noncomputable def half (value : NNReal) : NNReal :=
  div value two

public theorem halfPositive {value : NNReal} (positive : lt zero value) :
    lt zero (half value) :=
  divPositive positive twoPositive

public theorem halfAddHalf (value : NNReal) :
    add (half value) (half value) = value := by
  calc
    add (half value) (half value) =
        add (mul (half value) one) (mul (half value) one) := by
      rw [mulOne]
    _ = mul (half value) (add one one) :=
      (mulAdd (half value) one one).symm
    _ = mul (div value two) two := rfl
    _ = value := divMulCancel value twoNeZero

public theorem leOfForallPositiveLeAdd {left right : NNReal}
    (approaches : ∀ error, lt zero error → le left (add right error)) :
    le left right := by
  apply Classical.byContradiction
  intro notIncluded
  have reverse : le right left := by
    rcases leTotal left right with included | reverse
    · exact False.elim (notIncluded included)
    · exact reverse
  let difference := sub left right
  have differenceNonzero : difference ≠ zero := by
    intro equal
    exact notIncluded ((subEqZeroIffLe).mp equal)
  have differencePositive : lt zero difference :=
    (zeroLtIffNeZero difference).mpr differenceNonzero
  let error := half difference
  have errorPositive : lt zero error := halfPositive differencePositive
  have assumed := approaches error errorPositive
  have differenceLeError : le difference error := by
    apply (addLeAddRightIff).mp
    rw [subAddCancel reverse, addComm error right]
    exact assumed
  have errorLessDifference : lt error difference := by
    rw [← halfAddHalf difference]
    have shifted :=
      (addLtAddLeftIff (left := zero) (right := error)
        (shift := error)).mpr errorPositive
    simpa only [addZero] using shifted
  exact errorLessDifference.right differenceLeError

end NNReal

end Foundations.Real
