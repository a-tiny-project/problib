module

public import Problib.Real.Nonnegative

namespace Problib.Real

set_option autoImplicit false

public inductive ENNReal where
  | finite (value : NNReal)
  | top

namespace ENNReal

@[expose] public def le : ENNReal → ENNReal → Prop
  | _, .top => True
  | .top, .finite _ => False
  | .finite left, .finite right => NNReal.le left right

@[expose] public def lt (left right : ENNReal) : Prop :=
  le left right ∧ ¬le right left

@[expose] public def zero : ENNReal := .finite NNReal.zero

@[expose] public noncomputable def one : ENNReal := .finite NNReal.one

@[expose] public def Finite : ENNReal → Prop
  | .finite _ => True
  | .top => False

public theorem finite_injective : Function.Injective finite := by
  intro left right equal
  cases equal
  rfl

/-- An extended-nonnegative value bounded above by a finite value is finite. -/
public theorem finite_of_le {left right : ENNReal}
    (included : le left right) (rightFinite : Finite right) : Finite left := by
  cases right with
  | top => exact False.elim rightFinite
  | finite rightValue =>
      cases left with
      | top => exact False.elim included
      | finite leftValue => exact True.intro

public theorem finite_ne_top (value : NNReal) : finite value ≠ top := by
  intro equal
  cases equal

public theorem top_ne_finite (value : NNReal) : top ≠ finite value := by
  intro equal
  cases equal

public theorem eq_top_or_exists_finite (value : ENNReal) :
    value = top ∨ ∃ finiteValue, value = finite finiteValue := by
  cases value with
  | finite finiteValue => exact Or.inr ⟨finiteValue, rfl⟩
  | top => exact Or.inl rfl

public theorem exists_finite_of_finite {value : ENNReal}
    (finiteValue : Finite value) :
    ∃ underlying, value = finite underlying := by
  cases value with
  | finite underlying => exact ⟨underlying, rfl⟩
  | top => exact False.elim finiteValue

public theorem finite_iff_ne_top {value : ENNReal} :
    Finite value ↔ value ≠ top := by
  cases value with
  | finite underlying =>
      exact ⟨fun _ => finite_ne_top underlying, fun _ => True.intro⟩
  | top =>
      exact ⟨False.elim, fun notEqual => False.elim (notEqual rfl)⟩

public theorem le_refl (value : ENNReal) : le value value := by
  cases value with
  | finite underlying => exact NNReal.le_refl underlying
  | top => exact True.intro

public theorem le_trans {left middle right : ENNReal}
    (leftMiddle : le left middle) (middleRight : le middle right) :
    le left right := by
  cases left with
  | top =>
      cases middle with
      | finite _ => exact False.elim leftMiddle
      | top =>
          cases right with
          | finite _ => exact False.elim middleRight
          | top => exact True.intro
  | finite leftValue =>
      cases middle with
      | top =>
          cases right with
          | finite _ => exact False.elim middleRight
          | top => exact True.intro
      | finite middleValue =>
          cases right with
          | top => exact True.intro
          | finite rightValue =>
              exact NNReal.le_trans leftMiddle middleRight

public theorem le_antisymm {left right : ENNReal}
    (leftRight : le left right) (rightLeft : le right left) :
    left = right := by
  cases left with
  | top =>
      cases right with
      | finite _ => exact False.elim leftRight
      | top => rfl
  | finite leftValue =>
      cases right with
      | top => exact False.elim rightLeft
      | finite rightValue =>
          exact congrArg finite (NNReal.le_antisymm leftRight rightLeft)

public theorem le_total (left right : ENNReal) :
    le left right ∨ le right left := by
  cases left with
  | top => exact Or.inr True.intro
  | finite leftValue =>
      cases right with
      | top => exact Or.inl True.intro
      | finite rightValue => exact NNReal.le_total leftValue rightValue

public theorem le_top (value : ENNReal) : le value top :=
  True.intro

public theorem zero_le (value : ENNReal) : le zero value := by
  cases value with
  | finite underlying => exact NNReal.zero_le underlying
  | top => exact True.intro

public theorem top_le_iff {value : ENNReal} : le top value ↔ value = top := by
  cases value with
  | finite underlying =>
      exact ⟨False.elim, fun equal => False.elim (finite_ne_top underlying equal)⟩
  | top => exact ⟨fun _ => rfl, fun _ => True.intro⟩

public theorem le_zero_iff {value : ENNReal} : le value zero ↔ value = zero := by
  constructor
  · intro included
    exact le_antisymm included (zero_le value)
  · intro equal
    rw [equal]
    exact le_refl zero

public theorem eq_zero_of_le_zero {value : ENNReal} (included : le value zero) :
    value = zero :=
  le_zero_iff.mp included

public theorem zero_lt_top : lt zero top :=
  ⟨le_top zero, fun reverse => finite_ne_top NNReal.zero (top_le_iff.mp reverse)⟩

public theorem zero_lt_iff_ne_zero {value : ENNReal} :
    lt zero value ↔ value ≠ zero := by
  constructor
  · intro positive equal
    subst value
    exact positive.right positive.left
  · intro nonzero
    refine ⟨zero_le value, ?_⟩
    intro nonpositive
    exact nonzero (le_antisymm nonpositive (zero_le value))

public def linearOrder : Problib.Algebra.LinearOrderLaws ENNReal where
  le := le
  refl := le_refl
  trans := le_trans
  antisymm := le_antisymm
  total := le_total

private def finiteValues (set : ENNReal → Prop) : NNReal → Prop :=
  fun value => set (finite value)

private theorem finiteValues_nonempty (set : ENNReal → Prop)
    (nonempty : ∃ value, set value) (topAbsent : ¬set top) :
    ∃ value, finiteValues set value := by
  rcases nonempty with ⟨value, member⟩
  cases value with
  | finite underlying => exact ⟨underlying, member⟩
  | top => exact False.elim (topAbsent member)

public noncomputable def supremum (set : ENNReal → Prop) :
    ENNReal := by
  classical
  exact if containsTop : set top then top
  else if nonempty : ∃ value, set value then
    if bounded : ∃ upper : NNReal,
        ∀ value, finiteValues set value → NNReal.le value upper then
      finite (NNReal.sup (finiteValues set)
        (finiteValues_nonempty set nonempty containsTop) bounded)
    else top
  else zero

public theorem le_supremum {set : ENNReal → Prop} {value : ENNReal}
    (member : set value) : le value (supremum set) := by
  classical
  unfold supremum
  by_cases containsTop : set top
  · simp only [dif_pos containsTop]
    exact le_top value
  · simp only [dif_neg containsTop]
    have nonempty : ∃ candidate, set candidate := ⟨value, member⟩
    simp only [dif_pos nonempty]
    by_cases bounded : ∃ upper : NNReal,
        ∀ candidate, finiteValues set candidate → NNReal.le candidate upper
    · simp only [dif_pos bounded]
      cases value with
      | finite underlying =>
          exact NNReal.le_sup
            (finiteValues_nonempty set nonempty containsTop) bounded member
      | top => exact False.elim (containsTop member)
    · simp only [dif_neg bounded]
      exact le_top value

public theorem supremum_le {set : ENNReal → Prop} {upper : ENNReal}
    (isUpper : ∀ value, set value → le value upper) :
    le (supremum set) upper := by
  classical
  cases upper with
  | top => exact le_top (supremum set)
  | finite upperValue =>
      have topAbsent : ¬set top := by
        intro topMember
        exact isUpper top topMember
      have bounded : ∃ bound : NNReal,
          ∀ value, finiteValues set value → NNReal.le value bound :=
        ⟨upperValue, fun value member => isUpper (finite value) member⟩
      unfold supremum
      simp only [dif_neg topAbsent]
      by_cases nonempty : ∃ value, set value
      · simp only [dif_pos nonempty, dif_pos bounded]
        exact NNReal.sup_least
          (finiteValues_nonempty set nonempty topAbsent) bounded
          (fun value member => isUpper (finite value) member)
      · simp only [dif_neg nonempty]
        exact NNReal.zero_le upperValue

public theorem supremum_le_iff {set : ENNReal → Prop} {upper : ENNReal} :
    le (supremum set) upper ↔ ∀ value, set value → le value upper := by
  constructor
  · intro supremumUpper value member
    exact le_trans (le_supremum member) supremumUpper
  · exact supremum_le

public theorem supremum_mono {left right : ENNReal → Prop}
    (included : ∀ value, left value → right value) :
    le (supremum left) (supremum right) := by
  apply supremum_le
  intro value member
  exact le_supremum (included value member)

public theorem supremum_empty :
    supremum (fun _ : ENNReal => False) = zero := by
  apply le_antisymm
  · apply supremum_le
    intro value member
    exact False.elim member
  · exact zero_le _

public theorem supremum_eq_zero_iff {set : ENNReal → Prop} :
    supremum set = zero ↔ ∀ value, set value → value = zero := by
  constructor
  · intro equal value member
    apply eq_zero_of_le_zero
    rw [← equal]
    exact le_supremum member
  · intro allZero
    apply le_antisymm
    · apply supremum_le
      intro value member
      rw [allZero value member]
      exact le_refl zero
    · exact zero_le _

public theorem supremum_eq_top_of_member {set : ENNReal → Prop}
    (member : set top) : supremum set = top := by
  apply le_antisymm (le_top _)
  exact le_supremum member

@[expose] public noncomputable def infimum (set : ENNReal → Prop) :
    ENNReal :=
  supremum (fun lower => ∀ value, set value → le lower value)

public theorem infimum_le {set : ENNReal → Prop} {value : ENNReal}
    (member : set value) : le (infimum set) value := by
  unfold infimum
  apply supremum_le
  intro lower isLower
  exact isLower value member

public theorem le_infimum {set : ENNReal → Prop} {lower : ENNReal}
    (isLower : ∀ value, set value → le lower value) :
    le lower (infimum set) := by
  unfold infimum
  exact le_supremum isLower

public theorem le_infimum_iff {set : ENNReal → Prop} {lower : ENNReal} :
    le lower (infimum set) ↔ ∀ value, set value → le lower value := by
  constructor
  · intro lowerInfimum value member
    exact le_trans lowerInfimum (infimum_le member)
  · exact le_infimum

public theorem infimum_mono {left right : ENNReal → Prop}
    (included : ∀ value, left value → right value) :
    le (infimum right) (infimum left) := by
  apply le_infimum
  intro value member
  exact infimum_le (included value member)

public theorem exists_greater_of_lt_supremum {set : ENNReal → Prop}
    {lower : ENNReal} (less : lt lower (supremum set)) :
    ∃ value, set value ∧ lt lower value := by
  classical
  apply Classical.byContradiction
  intro noWitness
  have lowerUpper : ∀ value, set value → le value lower := by
    intro value member
    by_cases included : le value lower
    · exact included
    · have reverse := Or.resolve_left (le_total value lower) included
      exact False.elim (noWitness ⟨value, member, reverse, included⟩)
  exact less.right (supremum_le lowerUpper)

public theorem exists_less_of_infimum_lt {set : ENNReal → Prop}
    {upper : ENNReal} (less : lt (infimum set) upper) :
    ∃ value, set value ∧ lt value upper := by
  classical
  apply Classical.byContradiction
  intro noWitness
  have upperLower : ∀ value, set value → le upper value := by
    intro value member
    by_cases included : le upper value
    · exact included
    · have reverse := Or.resolve_left (le_total upper value) included
      exact False.elim (noWitness ⟨value, member, reverse, included⟩)
  exact less.right (le_infimum upperLower)

end ENNReal

end Problib.Real
