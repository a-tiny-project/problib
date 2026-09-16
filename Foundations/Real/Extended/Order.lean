module

public import Foundations.Real.Nonnegative

namespace Foundations.Real

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

public theorem finiteInjective : Function.Injective finite := by
  intro left right equal
  cases equal
  rfl

/-- An extended-nonnegative value bounded above by a finite value is finite. -/
public theorem finiteOfLe {left right : ENNReal}
    (included : le left right) (rightFinite : Finite right) : Finite left := by
  cases right with
  | top => exact False.elim rightFinite
  | finite rightValue =>
      cases left with
      | top => exact False.elim included
      | finite leftValue => exact True.intro

public theorem finiteNeTop (value : NNReal) : finite value ≠ top := by
  intro equal
  cases equal

public theorem topNeFinite (value : NNReal) : top ≠ finite value := by
  intro equal
  cases equal

public theorem eqTopOrExistsFinite (value : ENNReal) :
    value = top ∨ ∃ finiteValue, value = finite finiteValue := by
  cases value with
  | finite finiteValue => exact Or.inr ⟨finiteValue, rfl⟩
  | top => exact Or.inl rfl

public theorem existsFiniteOfFinite {value : ENNReal}
    (finiteValue : Finite value) :
    ∃ underlying, value = finite underlying := by
  cases value with
  | finite underlying => exact ⟨underlying, rfl⟩
  | top => exact False.elim finiteValue

public theorem finiteIffNeTop {value : ENNReal} :
    Finite value ↔ value ≠ top := by
  cases value with
  | finite underlying =>
      exact ⟨fun _ => finiteNeTop underlying, fun _ => True.intro⟩
  | top =>
      exact ⟨False.elim, fun notEqual => False.elim (notEqual rfl)⟩

public theorem leRefl (value : ENNReal) : le value value := by
  cases value with
  | finite underlying => exact NNReal.leRefl underlying
  | top => exact True.intro

public theorem leTrans {left middle right : ENNReal}
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
              exact NNReal.leTrans leftMiddle middleRight

public theorem leAntisymm {left right : ENNReal}
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
          exact congrArg finite (NNReal.leAntisymm leftRight rightLeft)

public theorem leTotal (left right : ENNReal) :
    le left right ∨ le right left := by
  cases left with
  | top => exact Or.inr True.intro
  | finite leftValue =>
      cases right with
      | top => exact Or.inl True.intro
      | finite rightValue => exact NNReal.leTotal leftValue rightValue

public theorem leTop (value : ENNReal) : le value top :=
  True.intro

public theorem zeroLe (value : ENNReal) : le zero value := by
  cases value with
  | finite underlying => exact NNReal.zeroLe underlying
  | top => exact True.intro

public theorem topLeIff {value : ENNReal} : le top value ↔ value = top := by
  cases value with
  | finite underlying =>
      exact ⟨False.elim, fun equal => False.elim (finiteNeTop underlying equal)⟩
  | top => exact ⟨fun _ => rfl, fun _ => True.intro⟩

public theorem leZeroIff {value : ENNReal} : le value zero ↔ value = zero := by
  constructor
  · intro included
    exact leAntisymm included (zeroLe value)
  · intro equal
    rw [equal]
    exact leRefl zero

public theorem eqZeroOfLeZero {value : ENNReal} (included : le value zero) :
    value = zero :=
  leZeroIff.mp included

public theorem zeroLtTop : lt zero top :=
  ⟨leTop zero, fun reverse => finiteNeTop NNReal.zero (topLeIff.mp reverse)⟩

public theorem zeroLtIffNeZero {value : ENNReal} :
    lt zero value ↔ value ≠ zero := by
  constructor
  · intro positive equal
    subst value
    exact positive.right positive.left
  · intro nonzero
    refine ⟨zeroLe value, ?_⟩
    intro nonpositive
    exact nonzero (leAntisymm nonpositive (zeroLe value))

public def linearOrder : Foundations.Algebra.LinearOrderLaws ENNReal where
  le := le
  refl := leRefl
  trans := leTrans
  antisymm := leAntisymm
  total := leTotal

private def finiteValues (set : ENNReal → Prop) : NNReal → Prop :=
  fun value => set (finite value)

private theorem finiteValuesNonempty (set : ENNReal → Prop)
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
        (finiteValuesNonempty set nonempty containsTop) bounded)
    else top
  else zero

public theorem leSupremum {set : ENNReal → Prop} {value : ENNReal}
    (member : set value) : le value (supremum set) := by
  classical
  unfold supremum
  by_cases containsTop : set top
  · simp only [dif_pos containsTop]
    exact leTop value
  · simp only [dif_neg containsTop]
    have nonempty : ∃ candidate, set candidate := ⟨value, member⟩
    simp only [dif_pos nonempty]
    by_cases bounded : ∃ upper : NNReal,
        ∀ candidate, finiteValues set candidate → NNReal.le candidate upper
    · simp only [dif_pos bounded]
      cases value with
      | finite underlying =>
          exact NNReal.leSup
            (finiteValuesNonempty set nonempty containsTop) bounded member
      | top => exact False.elim (containsTop member)
    · simp only [dif_neg bounded]
      exact leTop value

public theorem supremumLe {set : ENNReal → Prop} {upper : ENNReal}
    (isUpper : ∀ value, set value → le value upper) :
    le (supremum set) upper := by
  classical
  cases upper with
  | top => exact leTop (supremum set)
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
        exact NNReal.supLeast
          (finiteValuesNonempty set nonempty topAbsent) bounded
          (fun value member => isUpper (finite value) member)
      · simp only [dif_neg nonempty]
        exact NNReal.zeroLe upperValue

public theorem supremumLeIff {set : ENNReal → Prop} {upper : ENNReal} :
    le (supremum set) upper ↔ ∀ value, set value → le value upper := by
  constructor
  · intro supremumUpper value member
    exact leTrans (leSupremum member) supremumUpper
  · exact supremumLe

public theorem supremumMono {left right : ENNReal → Prop}
    (included : ∀ value, left value → right value) :
    le (supremum left) (supremum right) := by
  apply supremumLe
  intro value member
  exact leSupremum (included value member)

public theorem supremumEmpty :
    supremum (fun _ : ENNReal => False) = zero := by
  apply leAntisymm
  · apply supremumLe
    intro value member
    exact False.elim member
  · exact zeroLe _

public theorem supremumEqZeroIff {set : ENNReal → Prop} :
    supremum set = zero ↔ ∀ value, set value → value = zero := by
  constructor
  · intro equal value member
    apply eqZeroOfLeZero
    rw [← equal]
    exact leSupremum member
  · intro allZero
    apply leAntisymm
    · apply supremumLe
      intro value member
      rw [allZero value member]
      exact leRefl zero
    · exact zeroLe _

public theorem supremumEqTopOfMember {set : ENNReal → Prop}
    (member : set top) : supremum set = top := by
  apply leAntisymm (leTop _)
  exact leSupremum member

@[expose] public noncomputable def infimum (set : ENNReal → Prop) :
    ENNReal :=
  supremum (fun lower => ∀ value, set value → le lower value)

public theorem infimumLe {set : ENNReal → Prop} {value : ENNReal}
    (member : set value) : le (infimum set) value := by
  unfold infimum
  apply supremumLe
  intro lower isLower
  exact isLower value member

public theorem leInfimum {set : ENNReal → Prop} {lower : ENNReal}
    (isLower : ∀ value, set value → le lower value) :
    le lower (infimum set) := by
  unfold infimum
  exact leSupremum isLower

public theorem leInfimumIff {set : ENNReal → Prop} {lower : ENNReal} :
    le lower (infimum set) ↔ ∀ value, set value → le lower value := by
  constructor
  · intro lowerInfimum value member
    exact leTrans lowerInfimum (infimumLe member)
  · exact leInfimum

public theorem infimumMono {left right : ENNReal → Prop}
    (included : ∀ value, left value → right value) :
    le (infimum right) (infimum left) := by
  apply leInfimum
  intro value member
  exact infimumLe (included value member)

public theorem existsGreaterOfLtSupremum {set : ENNReal → Prop}
    {lower : ENNReal} (less : lt lower (supremum set)) :
    ∃ value, set value ∧ lt lower value := by
  classical
  apply Classical.byContradiction
  intro noWitness
  have lowerUpper : ∀ value, set value → le value lower := by
    intro value member
    by_cases included : le value lower
    · exact included
    · have reverse := Or.resolve_left (leTotal value lower) included
      exact False.elim (noWitness ⟨value, member, reverse, included⟩)
  exact less.right (supremumLe lowerUpper)

public theorem existsLessOfInfimumLt {set : ENNReal → Prop}
    {upper : ENNReal} (less : lt (infimum set) upper) :
    ∃ value, set value ∧ lt value upper := by
  classical
  apply Classical.byContradiction
  intro noWitness
  have upperLower : ∀ value, set value → le upper value := by
    intro value member
    by_cases included : le upper value
    · exact included
    · have reverse := Or.resolve_left (leTotal upper value) included
      exact False.elim (noWitness ⟨value, member, reverse, included⟩)
  exact less.right (leInfimum upperLower)

end ENNReal

end Foundations.Real
