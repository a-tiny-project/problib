module

public import Problib.Measure.Space
public import Problib.Real.Approximation
public import Problib.Real.Arithmetic

set_option autoImplicit false

namespace Problib.Measure.Real

open Problib.Real.Construction

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

public theorem not_lt_iff_le {left right : Carrier} :
    ¬Dedekind.lt left right ↔ Dedekind.le right left := by
  constructor
  · intro notLess
    rcases Dedekind.le_total right left with included | reverse
    · exact included
    · by_cases included : Dedekind.le right left
      · exact included
      · exact False.elim (notLess ⟨reverse, included⟩)
  · intro reverse less
    exact less.right reverse

public theorem not_le_iff_lt {left right : Carrier} :
    ¬Dedekind.le left right ↔ Dedekind.lt right left := by
  constructor
  · intro notIncluded
    rcases Dedekind.le_total right left with reverse | included
    · exact ⟨reverse, notIncluded⟩
    · exact False.elim (notIncluded included)
  · intro less included
    exact less.right included

public theorem complement_ioi (boundary : Carrier) :
    Set.complement (Ioi boundary) = Iic boundary := by
  apply Set.ext
  intro value
  exact not_lt_iff_le

public theorem complement_iic (boundary : Carrier) :
    Set.complement (Iic boundary) = Ioi boundary := by
  apply Set.ext
  intro value
  exact not_le_iff_lt

public theorem complement_iio (boundary : Carrier) :
    Set.complement (Iio boundary) = Ici boundary := by
  apply Set.ext
  intro value
  exact not_lt_iff_le

public theorem complement_ici (boundary : Carrier) :
    Set.complement (Ici boundary) = Iio boundary := by
  apply Set.ext
  intro value
  exact not_le_iff_lt

public theorem ioo_eq_inter (lower upper : Carrier) :
    Ioo lower upper = Set.inter (Ioi lower) (Iio upper) :=
  rfl

public theorem ioc_eq_inter (lower upper : Carrier) :
    Ioc lower upper = Set.inter (Ioi lower) (Iic upper) :=
  rfl

public theorem ico_eq_inter (lower upper : Carrier) :
    Ico lower upper = Set.inter (Ici lower) (Iio upper) :=
  rfl

public theorem icc_eq_inter (lower upper : Carrier) :
    Icc lower upper = Set.inter (Ici lower) (Iic upper) :=
  rfl

public theorem ioc_eq_difference (lower upper : Carrier) :
    Ioc lower upper = Set.difference (Iic upper) (Iic lower) := by
  apply Set.ext
  intro value
  change (Dedekind.lt lower value ∧ Dedekind.le value upper) ↔
    Dedekind.le value upper ∧ ¬Dedekind.le value lower
  constructor
  · intro member
    exact ⟨member.2, member.1.right⟩
  · intro member
    exact ⟨not_le_iff_lt.mp member.2, member.1⟩

public theorem lt_sub_iff_add_lt {value upper shift : Carrier} :
    Dedekind.lt value (Dedekind.sub upper shift) ↔
      Dedekind.lt (Dedekind.add shift value) upper := by
  have translated := Dedekind.add_lt_add_left_iff
    (left := value) (right := Dedekind.sub upper shift) (shift := shift)
  rw [Dedekind.add_sub_cancel] at translated
  exact translated.symm

public theorem lt_iff_sub_positive {left right : Carrier} :
    Dedekind.lt left right ↔
      Dedekind.lt Dedekind.zero (Dedekind.sub right left) := by
  rw [lt_sub_iff_add_lt]
  rw [Dedekind.add_zero]

@[expose] public noncomputable def minimum
    (left right : Carrier) : Carrier := by
  classical
  exact if Dedekind.le left right then left else right

@[expose] public noncomputable def maximum
    (left right : Carrier) : Carrier := by
  classical
  exact if Dedekind.le left right then right else left

public theorem le_minimum_iff {value left right : Carrier} :
    Dedekind.le value (minimum left right) ↔
      Dedekind.le value left ∧ Dedekind.le value right := by
  classical
  by_cases included : Dedekind.le left right
  · unfold minimum
    rw [if_pos included]
    exact ⟨fun valueLeft =>
      ⟨valueLeft, Dedekind.le_trans valueLeft included⟩, fun member => member.1⟩
  · have reverse := (not_le_iff_lt.mp included).left
    unfold minimum
    rw [if_neg included]
    exact ⟨fun valueRight =>
      ⟨Dedekind.le_trans valueRight reverse, valueRight⟩, fun member => member.2⟩

public theorem maximum_lt_iff {left right value : Carrier} :
    Dedekind.lt (maximum left right) value ↔
      Dedekind.lt left value ∧ Dedekind.lt right value := by
  classical
  by_cases included : Dedekind.le left right
  · unfold maximum
    rw [if_pos included]
    exact ⟨fun rightLess =>
      ⟨Dedekind.lt_of_le_of_lt included rightLess, rightLess⟩, fun member => member.2⟩
  · have reverse := (not_le_iff_lt.mp included).left
    unfold maximum
    rw [if_neg included]
    exact ⟨fun leftLess =>
      ⟨leftLess, Dedekind.lt_of_le_of_lt reverse leftLess⟩, fun member => member.1⟩

public theorem inter_ioc_ioi (lower upper boundary : Carrier) :
    Set.inter (Ioc lower upper) (Ioi boundary) =
      Ioc (maximum lower boundary) upper := by
  apply Set.ext
  intro value
  change ((Dedekind.lt lower value ∧ Dedekind.le value upper) ∧
    Dedekind.lt boundary value) ↔
      Dedekind.lt (maximum lower boundary) value ∧ Dedekind.le value upper
  rw [maximum_lt_iff]
  constructor
  · intro member
    exact ⟨⟨member.1.1, member.2⟩, member.1.2⟩
  · intro member
    exact ⟨⟨member.1.1, member.2⟩, member.1.2⟩

public theorem difference_ioc_ioi (lower upper boundary : Carrier) :
    Set.difference (Ioc lower upper) (Ioi boundary) =
      Ioc lower (minimum upper boundary) := by
  apply Set.ext
  intro value
  change ((Dedekind.lt lower value ∧ Dedekind.le value upper) ∧
    ¬Dedekind.lt boundary value) ↔
      Dedekind.lt lower value ∧ Dedekind.le value (minimum upper boundary)
  rw [not_lt_iff_le, le_minimum_iff]
  constructor
  · intro member
    exact ⟨member.1.1, member.1.2, member.2⟩
  · intro member
    exact ⟨⟨member.1, member.2.1⟩, member.2.2⟩

public theorem ioc_empty_of_le {lower upper : Carrier}
    (reverse : Dedekind.le upper lower) :
    Ioc lower upper = Set.empty := by
  apply Set.ext
  intro value
  constructor
  · intro member
    exact member.1.right (Dedekind.le_trans member.2 reverse)
  · intro member
    exact False.elim member

public theorem ioc_nonempty {lower upper : Carrier}
    (less : Dedekind.lt lower upper) : Set.Nonempty (Ioc lower upper) := by
  rcases Dedekind.exists_rational_between less with
    ⟨rational, lowerLess, lessUpper⟩
  exact ⟨Dedekind.selection.ofRat rational, lowerLess, lessUpper.left⟩

public theorem ioc_eq_empty_iff {lower upper : Carrier} :
    Ioc lower upper = Set.empty ↔ Dedekind.le upper lower := by
  constructor
  · intro empty
    rcases Dedekind.le_total upper lower with reverse | forward
    · exact reverse
    · by_cases reverse : Dedekind.le upper lower
      · exact reverse
      · have less : Dedekind.lt lower upper := ⟨forward, reverse⟩
        rcases ioc_nonempty less with ⟨value, member⟩
        rw [empty] at member
        exact False.elim member
  · exact ioc_empty_of_le

public theorem ioc_endpoints_eq {firstLower firstUpper secondLower secondUpper : Carrier}
    (firstNonempty : Dedekind.lt firstLower firstUpper)
    (secondNonempty : Dedekind.lt secondLower secondUpper)
    (equal : Ioc firstLower firstUpper = Ioc secondLower secondUpper) :
    firstLower = secondLower ∧ firstUpper = secondUpper := by
  have firstLowerSecondLower : Dedekind.le firstLower secondLower := by
    classical
    by_cases included : Dedekind.le firstLower secondLower
    · exact included
    have notIncluded : ¬Dedekind.le firstLower secondLower := included
    have secondLessFirst := not_le_iff_lt.mp notIncluded
    rcases ioc_nonempty firstNonempty with ⟨value, valueMember⟩
    have valueSecond : Ioc secondLower secondUpper value := by
      rw [← equal]
      exact valueMember
    have firstLowerLeSecondUpper :=
      Dedekind.le_trans valueMember.1.left valueSecond.2
    have firstLowerSecond : Ioc secondLower secondUpper firstLower :=
      ⟨secondLessFirst, firstLowerLeSecondUpper⟩
    have firstLowerFirst : Ioc firstLower firstUpper firstLower := by
      rw [equal]
      exact firstLowerSecond
    exact False.elim (Dedekind.lt_irrefl firstLower firstLowerFirst.1)
  have secondLowerFirstLower : Dedekind.le secondLower firstLower := by
    classical
    by_cases included : Dedekind.le secondLower firstLower
    · exact included
    have notIncluded : ¬Dedekind.le secondLower firstLower := included
    have firstLessSecond := not_le_iff_lt.mp notIncluded
    rcases ioc_nonempty secondNonempty with ⟨value, valueMember⟩
    have valueFirst : Ioc firstLower firstUpper value := by
      rw [equal]
      exact valueMember
    have secondLowerLeFirstUpper :=
      Dedekind.le_trans valueMember.1.left valueFirst.2
    have secondLowerFirst : Ioc firstLower firstUpper secondLower :=
      ⟨firstLessSecond, secondLowerLeFirstUpper⟩
    have secondLowerSecond : Ioc secondLower secondUpper secondLower := by
      rw [← equal]
      exact secondLowerFirst
    exact False.elim (Dedekind.lt_irrefl secondLower secondLowerSecond.1)
  have lowerEqual := Dedekind.le_antisymm
    firstLowerSecondLower secondLowerFirstLower
  have firstUpperSecondUpper : Dedekind.le firstUpper secondUpper := by
    classical
    by_cases included : Dedekind.le firstUpper secondUpper
    · exact included
    have notIncluded : ¬Dedekind.le firstUpper secondUpper := included
    have secondLessFirst := not_le_iff_lt.mp notIncluded
    have firstUpperFirst : Ioc firstLower firstUpper firstUpper :=
      ⟨firstNonempty, Dedekind.le_refl firstUpper⟩
    have firstUpperSecond : Ioc secondLower secondUpper firstUpper := by
      rw [← equal]
      exact firstUpperFirst
    exact False.elim (secondLessFirst.right firstUpperSecond.2)
  have secondUpperFirstUpper : Dedekind.le secondUpper firstUpper := by
    classical
    by_cases included : Dedekind.le secondUpper firstUpper
    · exact included
    have notIncluded : ¬Dedekind.le secondUpper firstUpper := included
    have firstLessSecond := not_le_iff_lt.mp notIncluded
    have secondUpperSecond : Ioc secondLower secondUpper secondUpper :=
      ⟨secondNonempty, Dedekind.le_refl secondUpper⟩
    have secondUpperFirst : Ioc firstLower firstUpper secondUpper := by
      rw [equal]
      exact secondUpperSecond
    exact False.elim (firstLessSecond.right secondUpperFirst.2)
  exact ⟨lowerEqual,
    Dedekind.le_antisymm firstUpperSecondUpper secondUpperFirstUpper⟩

end Problib.Measure.Real
