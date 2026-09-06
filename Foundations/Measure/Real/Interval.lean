module

public import Foundations.Measure.Space
public import Foundations.Real.Approximation

set_option autoImplicit false

namespace Foundations.Measure.Real

open Foundations.Real.Construction

public abbrev Carrier := Dedekind.selection.Carrier

@[expose] public def Iio (upper : Carrier) : Set Carrier :=
  fun value => Dedekind.lt value upper

@[expose] public def Iic (upper : Carrier) : Set Carrier :=
  fun value => Dedekind.le value upper

@[expose] public def Ioi (lower : Carrier) : Set Carrier :=
  fun value => Dedekind.lt lower value

@[expose] public def Ici (lower : Carrier) : Set Carrier :=
  fun value => Dedekind.le lower value

@[expose] public def Ioo (lower upper : Carrier) : Set Carrier :=
  fun value => Dedekind.lt lower value ∧ Dedekind.lt value upper

@[expose] public def Ioc (lower upper : Carrier) : Set Carrier :=
  fun value => Dedekind.lt lower value ∧ Dedekind.le value upper

@[expose] public def Ico (lower upper : Carrier) : Set Carrier :=
  fun value => Dedekind.le lower value ∧ Dedekind.lt value upper

@[expose] public def Icc (lower upper : Carrier) : Set Carrier :=
  fun value => Dedekind.le lower value ∧ Dedekind.le value upper

public theorem ltTrans {left middle right : Carrier}
    (leftMiddle : Dedekind.lt left middle)
    (middleRight : Dedekind.lt middle right) :
    Dedekind.lt left right := by
  constructor
  · exact Dedekind.leTrans leftMiddle.left middleRight.left
  · intro rightLeft
    exact middleRight.right (Dedekind.leTrans rightLeft leftMiddle.left)

public theorem ltOfLtOfLe {left middle right : Carrier}
    (leftMiddle : Dedekind.lt left middle)
    (middleRight : Dedekind.le middle right) :
    Dedekind.lt left right := by
  constructor
  · exact Dedekind.leTrans leftMiddle.left middleRight
  · intro rightLeft
    exact leftMiddle.right (Dedekind.leTrans middleRight rightLeft)

public theorem ltOfLeOfLt {left middle right : Carrier}
    (leftMiddle : Dedekind.le left middle)
    (middleRight : Dedekind.lt middle right) :
    Dedekind.lt left right := by
  constructor
  · exact Dedekind.leTrans leftMiddle middleRight.left
  · intro rightLeft
    exact middleRight.right (Dedekind.leTrans rightLeft leftMiddle)

public theorem notLtIffLe {left right : Carrier} :
    ¬Dedekind.lt left right ↔ Dedekind.le right left := by
  constructor
  · intro notLess
    rcases Dedekind.leTotal right left with included | reverse
    · exact included
    · by_cases included : Dedekind.le right left
      · exact included
      · exact False.elim (notLess ⟨reverse, included⟩)
  · intro reverse less
    exact less.right reverse

public theorem notLeIffLt {left right : Carrier} :
    ¬Dedekind.le left right ↔ Dedekind.lt right left := by
  constructor
  · intro notIncluded
    rcases Dedekind.leTotal right left with reverse | included
    · exact ⟨reverse, notIncluded⟩
    · exact False.elim (notIncluded included)
  · intro less included
    exact less.right included

public theorem complementIoi (boundary : Carrier) :
    Set.complement (Ioi boundary) = Iic boundary := by
  apply Set.ext
  intro value
  exact notLtIffLe

public theorem complementIic (boundary : Carrier) :
    Set.complement (Iic boundary) = Ioi boundary := by
  apply Set.ext
  intro value
  exact notLeIffLt

public theorem complementIio (boundary : Carrier) :
    Set.complement (Iio boundary) = Ici boundary := by
  apply Set.ext
  intro value
  exact notLtIffLe

public theorem complementIci (boundary : Carrier) :
    Set.complement (Ici boundary) = Iio boundary := by
  apply Set.ext
  intro value
  exact notLeIffLt

public theorem Ioo_eq_inter (lower upper : Carrier) :
    Ioo lower upper = Set.inter (Ioi lower) (Iio upper) :=
  rfl

public theorem Ioc_eq_inter (lower upper : Carrier) :
    Ioc lower upper = Set.inter (Ioi lower) (Iic upper) :=
  rfl

public theorem Ico_eq_inter (lower upper : Carrier) :
    Ico lower upper = Set.inter (Ici lower) (Iio upper) :=
  rfl

public theorem Icc_eq_inter (lower upper : Carrier) :
    Icc lower upper = Set.inter (Ici lower) (Iic upper) :=
  rfl

public theorem Ioc_eq_difference (lower upper : Carrier) :
    Ioc lower upper = Set.difference (Iic upper) (Iic lower) := by
  apply Set.ext
  intro value
  change (Dedekind.lt lower value ∧ Dedekind.le value upper) ↔
    Dedekind.le value upper ∧ ¬Dedekind.le value lower
  constructor
  · intro member
    exact ⟨member.2, member.1.right⟩
  · intro member
    exact ⟨notLeIffLt.mp member.2, member.1⟩

public theorem addSubCancel (left right : Carrier) :
    Dedekind.add right (Dedekind.sub left right) = left := by
  rw [Dedekind.subEqAddNeg,
    Dedekind.addLeftComm right left (Dedekind.neg right),
    Dedekind.addNeg, Dedekind.addZero]

public theorem ltSubIffAddLt {value upper shift : Carrier} :
    Dedekind.lt value (Dedekind.sub upper shift) ↔
      Dedekind.lt (Dedekind.add shift value) upper := by
  have translated := Dedekind.addLtAddLeftIff
    (left := value) (right := Dedekind.sub upper shift) (shift := shift)
  rw [addSubCancel] at translated
  exact translated.symm

public theorem ltIffSubPositive {left right : Carrier} :
    Dedekind.lt left right ↔
      Dedekind.lt Dedekind.zero (Dedekind.sub right left) := by
  rw [ltSubIffAddLt]
  rw [Dedekind.addZero]

@[expose] public noncomputable def minimum
    (left right : Carrier) : Carrier := by
  classical
  exact if Dedekind.le left right then left else right

@[expose] public noncomputable def maximum
    (left right : Carrier) : Carrier := by
  classical
  exact if Dedekind.le left right then right else left

public theorem leMinimumIff {value left right : Carrier} :
    Dedekind.le value (minimum left right) ↔
      Dedekind.le value left ∧ Dedekind.le value right := by
  classical
  by_cases included : Dedekind.le left right
  · unfold minimum
    rw [if_pos included]
    exact ⟨fun valueLeft =>
      ⟨valueLeft, Dedekind.leTrans valueLeft included⟩, fun member => member.1⟩
  · have reverse := (notLeIffLt.mp included).left
    unfold minimum
    rw [if_neg included]
    exact ⟨fun valueRight =>
      ⟨Dedekind.leTrans valueRight reverse, valueRight⟩, fun member => member.2⟩

public theorem maximumLtIff {left right value : Carrier} :
    Dedekind.lt (maximum left right) value ↔
      Dedekind.lt left value ∧ Dedekind.lt right value := by
  classical
  by_cases included : Dedekind.le left right
  · unfold maximum
    rw [if_pos included]
    exact ⟨fun rightLess =>
      ⟨ltOfLeOfLt included rightLess, rightLess⟩, fun member => member.2⟩
  · have reverse := (notLeIffLt.mp included).left
    unfold maximum
    rw [if_neg included]
    exact ⟨fun leftLess =>
      ⟨leftLess, ltOfLeOfLt reverse leftLess⟩, fun member => member.1⟩

public theorem inter_Ioc_Ioi (lower upper boundary : Carrier) :
    Set.inter (Ioc lower upper) (Ioi boundary) =
      Ioc (maximum lower boundary) upper := by
  apply Set.ext
  intro value
  change ((Dedekind.lt lower value ∧ Dedekind.le value upper) ∧
    Dedekind.lt boundary value) ↔
      Dedekind.lt (maximum lower boundary) value ∧ Dedekind.le value upper
  rw [maximumLtIff]
  constructor
  · intro member
    exact ⟨⟨member.1.1, member.2⟩, member.1.2⟩
  · intro member
    exact ⟨⟨member.1.1, member.2⟩, member.1.2⟩

public theorem difference_Ioc_Ioi (lower upper boundary : Carrier) :
    Set.difference (Ioc lower upper) (Ioi boundary) =
      Ioc lower (minimum upper boundary) := by
  apply Set.ext
  intro value
  change ((Dedekind.lt lower value ∧ Dedekind.le value upper) ∧
    ¬Dedekind.lt boundary value) ↔
      Dedekind.lt lower value ∧ Dedekind.le value (minimum upper boundary)
  rw [notLtIffLe, leMinimumIff]
  constructor
  · intro member
    exact ⟨member.1.1, member.1.2, member.2⟩
  · intro member
    exact ⟨⟨member.1, member.2.1⟩, member.2.2⟩

public theorem Ioc_empty_of_le {lower upper : Carrier}
    (reverse : Dedekind.le upper lower) :
    Ioc lower upper = Set.empty := by
  apply Set.ext
  intro value
  constructor
  · intro member
    exact member.1.right (Dedekind.leTrans member.2 reverse)
  · intro member
    exact False.elim member

public theorem Ioc_nonempty {lower upper : Carrier}
    (less : Dedekind.lt lower upper) : Set.Nonempty (Ioc lower upper) := by
  rcases Dedekind.existsRationalBetween less with
    ⟨rational, lowerLess, lessUpper⟩
  exact ⟨Dedekind.selection.ofRat rational, lowerLess, lessUpper.left⟩

public theorem Ioc_eq_empty_iff {lower upper : Carrier} :
    Ioc lower upper = Set.empty ↔ Dedekind.le upper lower := by
  constructor
  · intro empty
    rcases Dedekind.leTotal upper lower with reverse | forward
    · exact reverse
    · by_cases reverse : Dedekind.le upper lower
      · exact reverse
      · have less : Dedekind.lt lower upper := ⟨forward, reverse⟩
        rcases Ioc_nonempty less with ⟨value, member⟩
        rw [empty] at member
        exact False.elim member
  · exact Ioc_empty_of_le

public theorem Ioc_endpoints_eq {firstLower firstUpper secondLower secondUpper : Carrier}
    (firstNonempty : Dedekind.lt firstLower firstUpper)
    (secondNonempty : Dedekind.lt secondLower secondUpper)
    (equal : Ioc firstLower firstUpper = Ioc secondLower secondUpper) :
    firstLower = secondLower ∧ firstUpper = secondUpper := by
  have firstLowerSecondLower : Dedekind.le firstLower secondLower := by
    classical
    by_cases included : Dedekind.le firstLower secondLower
    · exact included
    have notIncluded : ¬Dedekind.le firstLower secondLower := included
    have secondLessFirst := notLeIffLt.mp notIncluded
    rcases Ioc_nonempty firstNonempty with ⟨value, valueMember⟩
    have valueSecond : Ioc secondLower secondUpper value := by
      rw [← equal]
      exact valueMember
    have firstLowerLeSecondUpper :=
      Dedekind.leTrans valueMember.1.left valueSecond.2
    have firstLowerSecond : Ioc secondLower secondUpper firstLower :=
      ⟨secondLessFirst, firstLowerLeSecondUpper⟩
    have firstLowerFirst : Ioc firstLower firstUpper firstLower := by
      rw [equal]
      exact firstLowerSecond
    exact False.elim (Dedekind.ltIrrefl firstLower firstLowerFirst.1)
  have secondLowerFirstLower : Dedekind.le secondLower firstLower := by
    classical
    by_cases included : Dedekind.le secondLower firstLower
    · exact included
    have notIncluded : ¬Dedekind.le secondLower firstLower := included
    have firstLessSecond := notLeIffLt.mp notIncluded
    rcases Ioc_nonempty secondNonempty with ⟨value, valueMember⟩
    have valueFirst : Ioc firstLower firstUpper value := by
      rw [equal]
      exact valueMember
    have secondLowerLeFirstUpper :=
      Dedekind.leTrans valueMember.1.left valueFirst.2
    have secondLowerFirst : Ioc firstLower firstUpper secondLower :=
      ⟨firstLessSecond, secondLowerLeFirstUpper⟩
    have secondLowerSecond : Ioc secondLower secondUpper secondLower := by
      rw [← equal]
      exact secondLowerFirst
    exact False.elim (Dedekind.ltIrrefl secondLower secondLowerSecond.1)
  have lowerEqual := Dedekind.leAntisymm
    firstLowerSecondLower secondLowerFirstLower
  have firstUpperSecondUpper : Dedekind.le firstUpper secondUpper := by
    classical
    by_cases included : Dedekind.le firstUpper secondUpper
    · exact included
    have notIncluded : ¬Dedekind.le firstUpper secondUpper := included
    have secondLessFirst := notLeIffLt.mp notIncluded
    have firstUpperFirst : Ioc firstLower firstUpper firstUpper :=
      ⟨firstNonempty, Dedekind.leRefl firstUpper⟩
    have firstUpperSecond : Ioc secondLower secondUpper firstUpper := by
      rw [← equal]
      exact firstUpperFirst
    exact False.elim (secondLessFirst.right firstUpperSecond.2)
  have secondUpperFirstUpper : Dedekind.le secondUpper firstUpper := by
    classical
    by_cases included : Dedekind.le secondUpper firstUpper
    · exact included
    have notIncluded : ¬Dedekind.le secondUpper firstUpper := included
    have firstLessSecond := notLeIffLt.mp notIncluded
    have secondUpperSecond : Ioc secondLower secondUpper secondUpper :=
      ⟨secondNonempty, Dedekind.leRefl secondUpper⟩
    have secondUpperFirst : Ioc firstLower firstUpper secondUpper := by
      rw [equal]
      exact secondUpperSecond
    exact False.elim (firstLessSecond.right secondUpperFirst.2)
  exact ⟨lowerEqual,
    Dedekind.leAntisymm firstUpperSecondUpper secondUpperFirstUpper⟩

end Foundations.Measure.Real
