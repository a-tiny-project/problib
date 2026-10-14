module

public import Problib.Measure.Additive.Supremum
public import Problib.Measure.Kernel.Iteration.Algebra
import Problib.Measure.Integral.Lebesgue.Measure

set_option autoImplicit false

/-! Pointwise increasing limits of measurable kernels. -/

namespace Problib.Measure.Kernel

open Problib.Real

universe u v w

variable {alpha : Type u} {beta : Type v}
  {source : Space alpha} {target : Space beta}

/-- The kernel limit of an increasing countable chain. -/
@[expose] public noncomputable def iSupIncreasing
    (kernels : Nat → Kernel source target)
    (monotone : ∀ index, le (kernels index) (kernels (index + 1))) :
    Kernel source target where
  toFun := fun input => Measure.iSupIncreasing (fun index => kernels index input)
    (fun index set measurable => monotone index input set measurable)
  measurable := by
    intro set setMeasurable
    have equal : (fun input =>
        Measure.iSupIncreasing (fun index => kernels index input)
          (fun index region regionMeasurable =>
            monotone index input region regionMeasurable) set) =
        (fun input => ENNReal.iSup (fun index => kernels index input set)) := by
      funext input
      exact Measure.iSupIncreasing_apply_measurable _ _ setMeasurable
    rw [equal]
    exact ENNRealMeasurable.iSup fun index =>
      (kernels index).measurable setMeasurable

/-- Evaluation at an input yields the increasing supremum measure. -/
@[simp] public theorem iSupIncreasing_apply
    (kernels : Nat → Kernel source target)
    (monotone : ∀ index, le (kernels index) (kernels (index + 1)))
    (input : alpha) :
    iSupIncreasing kernels monotone input =
      Measure.iSupIncreasing (fun index => kernels index input)
        (fun index set measurable => monotone index input set measurable) := rfl

/-- Evaluation on a measurable set is the supremum of the chain's masses. -/
public theorem iSupIncreasing_apply_measurable
    (kernels : Nat → Kernel source target)
    (monotone : ∀ index, le (kernels index) (kernels (index + 1)))
    (input : alpha) {set : Set beta} (measurable : target.Measurable set) :
    iSupIncreasing kernels monotone input set =
      ENNReal.iSup (fun index => kernels index input set) :=
  Measure.iSupIncreasing_apply_measurable (fun index => kernels index input)
    (fun index region regionMeasurable => monotone index input region regionMeasurable)
    measurable

/-- Every stage lies below the increasing limit. -/
public theorem le_iSupIncreasing
    (kernels : Nat → Kernel source target)
    (monotone : ∀ index, le (kernels index) (kernels (index + 1)))
    (index : Nat) : le (kernels index) (iSupIncreasing kernels monotone) := by
  intro input set measurable
  rw [iSupIncreasing_apply_measurable kernels monotone input measurable]
  exact ENNReal.le_iSup (fun stage => kernels stage input set) index

/-- A common upper bound also bounds the increasing limit. -/
public theorem iSupIncreasing_le
    (kernels : Nat → Kernel source target)
    (monotone : ∀ index, le (kernels index) (kernels (index + 1)))
    (upper : Kernel source target)
    (bounded : ∀ index, le (kernels index) upper) :
    le (iSupIncreasing kernels monotone) upper := by
  intro input set measurable
  rw [iSupIncreasing_apply_measurable kernels monotone input measurable]
  exact ENNReal.iSup_le fun index => bounded index input set measurable

/-- Any two stages of an increasing kernel chain are ordered. -/
public theorem chain_le
    (kernels : Nat → Kernel source target)
    (monotone : ∀ index, le (kernels index) (kernels (index + 1)))
    {first second : Nat} (included : first ≤ second) :
    le (kernels first) (kernels second) := by
  induction included with
  | refl => exact le_refl _
  | step _ induction => exact le_trans induction (monotone _)

/-- A measurable output map preserves pointwise kernel order. -/
public theorem map_le {resultType : Type w} {result : Space resultType}
    {first second : Kernel source target}
    (function : beta → resultType) (measurable : MeasurableMap target result function)
    (included : le first second) :
    le (first.map function measurable) (second.map function measurable) := by
  intro input set setMeasurable
  rw [Kernel.map_apply, Kernel.map_apply,
    (first input).map_apply function measurable setMeasurable,
    (second input).map_apply function measurable setMeasurable]
  exact included input _ (measurable setMeasurable)

/-- Mapping an increasing kernel limit maps its pointwise supremum. -/
public theorem map_iSupIncreasing {resultType : Type w} {result : Space resultType}
    (kernels : Nat → Kernel source target)
    (increasing : ∀ index, le (kernels index) (kernels (index + 1)))
    (function : beta → resultType) (measurable : MeasurableMap target result function) :
    (iSupIncreasing kernels increasing).map function measurable =
      iSupIncreasing (fun index => (kernels index).map function measurable)
        (fun index => map_le function measurable (increasing index)) := by
  apply Kernel.ext_measurable
  intro input set setMeasurable
  rw [Kernel.map_apply,
    (iSupIncreasing kernels increasing input).map_apply function measurable setMeasurable,
    iSupIncreasing_apply_measurable kernels increasing input (measurable setMeasurable),
    iSupIncreasing_apply_measurable _ _ input setMeasurable]
  apply congrArg ENNReal.iSup
  funext index
  exact ((kernels index input).map_apply function measurable setMeasurable).symm

/-- Left addition preserves an increasing kernel limit. -/
public theorem add_iSupIncreasing
    (fixed : Kernel source target) (kernels : Nat → Kernel source target)
    (monotone : ∀ index, le (kernels index) (kernels (index + 1))) :
    Kernel.add fixed (iSupIncreasing kernels monotone) =
      iSupIncreasing (fun index => Kernel.add fixed (kernels index))
        (fun index => add_le_add (le_refl fixed) (monotone index)) := by
  apply Kernel.ext_measurable
  intro input set measurable
  rw [Kernel.add_apply, Measure.add_apply_measurable _ _ measurable,
    iSupIncreasing_apply_measurable kernels monotone input measurable,
    iSupIncreasing_apply_measurable _ _ input measurable]
  simp only [Kernel.add_apply, Measure.add_apply_measurable _ _ measurable]
  exact ENNReal.add_iSup _ _

/-- Kernel composition on the right preserves an increasing limit. -/
public theorem comp_iSupIncreasing_right {middleType : Type w}
    {middle : Space middleType} (first : Kernel source middle)
    (kernels : Nat → Kernel middle target)
    (monotone : ∀ index, le (kernels index) (kernels (index + 1))) :
    first.comp (iSupIncreasing kernels monotone) =
      iSupIncreasing (fun index => first.comp (kernels index))
        (fun index => comp_le_comp_right first (monotone index)) := by
  apply Kernel.ext_measurable
  intro input set measurable
  rw [comp_apply_measurable first (iSupIncreasing kernels monotone) input measurable,
    iSupIncreasing_apply_measurable _ _ input measurable]
  simp only [comp_apply_measurable first _ input measurable]
  have equal : (fun value => iSupIncreasing kernels monotone value set) =
      (fun value => ENNReal.iSup (fun index => kernels index value set)) := by
    funext value
    exact iSupIncreasing_apply_measurable kernels monotone value measurable
  rw [equal]
  exact lintegral_iSup (first input) (fun index value => kernels index value set)
    (fun index => (kernels index).measurable measurable)
    (fun index value => monotone index value set measurable)

/-- Kernel composition on the left preserves an increasing limit. -/
public theorem comp_iSupIncreasing_left {middleType : Type w}
    {middle : Space middleType} (kernels : Nat → Kernel source middle)
    (monotone : ∀ index, le (kernels index) (kernels (index + 1)))
    (second : Kernel middle target) :
    (iSupIncreasing kernels monotone).comp second =
      iSupIncreasing (fun index => (kernels index).comp second)
        (fun index => comp_le_comp_left (monotone index) second) := by
  apply Kernel.ext_measurable
  intro input set measurable
  rw [comp_apply_measurable _ second input measurable,
    iSupIncreasing_apply, iSupIncreasing_apply_measurable _ _ input measurable]
  simp only [comp_apply_measurable _ second input measurable]
  exact lintegral_iSupIncreasing_measure (fun value => second value set)
    (fun index => kernels index input)
    (fun index region regionMeasurable => monotone index input region regionMeasurable)

/-- Two increasing kernels may grow together through composition. -/
public theorem comp_iSupIncreasing_diagonal {middleType : Type w}
    {middle : Space middleType}
    (first : Nat → Kernel source middle)
    (firstMonotone : ∀ index, le (first index) (first (index + 1)))
    (second : Nat → Kernel middle target)
    (secondMonotone : ∀ index, le (second index) (second (index + 1))) :
    (iSupIncreasing first firstMonotone).comp
        (iSupIncreasing second secondMonotone) =
      iSupIncreasing (fun index => (first index).comp (second index))
        (fun index => le_trans
          (comp_le_comp_left (firstMonotone index) (second index))
          (comp_le_comp_right (first (index + 1)) (secondMonotone index))) := by
  let diagonal := fun index => (first index).comp (second index)
  let increasing := fun index => le_trans
    (comp_le_comp_left (firstMonotone index) (second index))
    (comp_le_comp_right (first (index + 1)) (secondMonotone index))
  change (iSupIncreasing first firstMonotone).comp
      (iSupIncreasing second secondMonotone) =
    iSupIncreasing diagonal increasing
  apply le_antisymm
  · rw [comp_iSupIncreasing_right]
    apply iSupIncreasing_le
    intro secondIndex
    rw [comp_iSupIncreasing_left]
    apply iSupIncreasing_le
    intro firstIndex
    let index := max firstIndex secondIndex
    exact le_trans
      (le_trans
        (comp_le_comp_left
          (chain_le first firstMonotone (Nat.le_max_left firstIndex secondIndex))
          (second secondIndex))
        (comp_le_comp_right (first index)
          (chain_le second secondMonotone (Nat.le_max_right firstIndex secondIndex))))
      (le_iSupIncreasing diagonal increasing index)
  · apply iSupIncreasing_le
    intro index
    exact le_trans
      (comp_le_comp_left (le_iSupIncreasing first firstMonotone index)
        (second index))
      (comp_le_comp_right (iSupIncreasing first firstMonotone)
        (le_iSupIncreasing second secondMonotone index))

/-- A common finite mass bound makes the increasing limit uniformly finite. -/
public theorem IsFinite.iSupIncreasing_of_bound
    (kernels : Nat → Kernel source target)
    (monotone : ∀ index, le (kernels index) (kernels (index + 1)))
    (bound : ENNReal) (finite : ENNReal.Finite bound)
    (bounded : ∀ index input, ENNReal.le (kernels index input Set.univ) bound) :
    IsFinite (iSupIncreasing kernels monotone) := by
  refine ⟨⟨bound, finite, ?_⟩⟩
  intro input
  rw [iSupIncreasing_apply_measurable kernels monotone input target.univ]
  exact ENNReal.iSup_le fun index => bounded index input

/-- Finite prefixes of a countable family of kernel increments. -/
@[expose] public noncomputable def prefixSum
    (increments : Nat → Kernel source target) : Nat → Kernel source target
  | 0 => Kernel.zero source target
  | count + 1 => Kernel.add (prefixSum increments count) (increments count)

/-- A finite prefix depends only on the increments before its bound. -/
public theorem prefixSum_congr {first second : Nat → Kernel source target}
    (count : Nat) (equal : ∀ index, index < count → first index = second index) :
    prefixSum first count = prefixSum second count := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [prefixSum, prefixSum,
        induction (fun index earlier => equal index (Nat.lt_trans earlier (Nat.lt_succ_self count))),
        equal count (Nat.lt_succ_self count)]

/-- Output mapping commutes with each finite prefix of increments. -/
public theorem map_prefixSum {resultType : Type w} {result : Space resultType}
    (increments : Nat → Kernel source target) (count : Nat)
    (function : beta → resultType) (measurable : MeasurableMap target result function) :
    (prefixSum increments count).map function measurable =
      prefixSum (fun index => (increments index).map function measurable) count := by
  induction count with
  | zero =>
      change (Kernel.zero source target).map function measurable = Kernel.zero source result
      apply Kernel.ext
      intro input
      exact Measure.map_zero function measurable
  | succ count induction =>
      change (Kernel.add (prefixSum increments count) (increments count)).map
          function measurable =
        Kernel.add (prefixSum (fun index => (increments index).map function measurable) count)
          ((increments count).map function measurable)
      apply Kernel.ext
      intro input
      change (Measure.add (prefixSum increments count input) (increments count input)).map
          function measurable =
        Measure.add
          (prefixSum (fun index => (increments index).map function measurable) count input)
          ((increments count input).map function measurable)
      rw [Measure.map_add]
      exact congrArg (fun measure : Measure result =>
        Measure.add measure ((increments count).map function measurable input))
        (congrArg (fun kernel : Kernel source result => kernel input) induction)

/-- A prefix evaluates to the partial sum of its increments. -/
public theorem prefixSum_apply_measurable
    (increments : Nat → Kernel source target) (count : Nat)
    (input : alpha) {set : Set beta} (measurable : target.Measurable set) :
    prefixSum increments count input set =
      ENNReal.partialSum (fun index => increments index input set) count := by
  induction count with
  | zero =>
      rw [prefixSum, Kernel.zero_apply, Measure.zero_apply, ENNReal.partialSum]
  | succ count induction =>
      rw [prefixSum, Kernel.add_apply,
        Measure.add_apply_measurable _ _ measurable, induction, ENNReal.partialSum]

/-- Every later prefix includes the previous one. -/
public theorem prefixSum_monotone
    (increments : Nat → Kernel source target) (count : Nat) :
    le (prefixSum increments count) (prefixSum increments (count + 1)) := by
  intro input set measurable
  rw [prefixSum_apply_measurable increments count input measurable,
    prefixSum_apply_measurable increments (count + 1) input measurable]
  exact ENNReal.partialSum_step _ count

/-- Finite prefixes of s-finite kernel increments remain s-finite. -/
public noncomputable def IsSFinite.prefixSumFinite
    (increments : Nat → Kernel source target)
    (finite : ∀ index, IsSFinite (increments index)) (count : Nat) :
    IsSFinite (prefixSum increments count) := by
  induction count with
  | zero => exact IsSFinite.zero source target
  | succ count induction => exact IsSFinite.add induction (finite count)

/-- The new composition paths at the next diagonal prefix. -/
@[expose] public noncomputable def diagonalPrefixIncrement {middleType : Type w}
    {middle : Space middleType}
    (first : Nat → Kernel source middle)
    (second : Nat → Kernel middle target) (count : Nat) :
    Kernel source target :=
  Kernel.add
    ((prefixSum first count).comp (second count))
    ((first count).comp (prefixSum second (count + 1)))

/-- A diagonal composition prefix is the sum of its newly completed paths. -/
public theorem comp_prefixSum_eq_prefixSum_diagonalPrefixIncrement
    {middleType : Type w} {middle : Space middleType}
    (first : Nat → Kernel source middle)
    (second : Nat → Kernel middle target) (count : Nat) :
    (prefixSum first count).comp (prefixSum second count) =
      prefixSum (diagonalPrefixIncrement first second) count := by
  induction count with
  | zero =>
      change (Kernel.zero source middle).comp (Kernel.zero middle target) =
        Kernel.zero source target
      exact zero_comp _
  | succ count induction =>
      change (Kernel.add (prefixSum first count) (first count)).comp
          (Kernel.add (prefixSum second count) (second count)) =
        Kernel.add (prefixSum (diagonalPrefixIncrement first second) count)
          (diagonalPrefixIncrement first second count)
      rw [add_comp_distrib, comp_add_distrib, induction, add_assoc]
      rfl

/-- The path increment at a diagonal stage is s-finite when both input
increment families are s-finite. -/
public noncomputable def IsSFinite.diagonalPrefixIncrement
    {middleType : Type w} {middle : Space middleType}
    (first : Nat → Kernel source middle)
    (second : Nat → Kernel middle target)
    (firstFinite : ∀ index, IsSFinite (first index))
    (secondFinite : ∀ index, IsSFinite (second index))
    (count : Nat) :
    IsSFinite (diagonalPrefixIncrement first second count) :=
  IsSFinite.add
    (IsSFinite.comp (IsSFinite.prefixSumFinite first firstFinite count)
      (secondFinite count))
    (IsSFinite.comp (firstFinite count)
      (IsSFinite.prefixSumFinite second secondFinite (count + 1)))

/-- The sum of increments is the supremum of their finite prefixes. -/
public theorem sum_eq_iSupIncreasing_prefixSum
    (increments : Nat → Kernel source target) :
    Kernel.sum increments =
      iSupIncreasing (prefixSum increments) (prefixSum_monotone increments) := by
  apply Kernel.ext_measurable
  intro input set measurable
  rw [Kernel.sum_apply, Measure.sum_apply _ measurable,
    iSupIncreasing_apply_measurable _ _ input measurable]
  unfold ENNReal.tsum
  apply congrArg ENNReal.iSup
  funext count
  exact (prefixSum_apply_measurable increments count input measurable).symm

/-- S-finiteness transfers to a chain identified with cumulative s-finite increments. -/
public noncomputable def IsSFinite.ofPrefixSum
    (kernels : Nat → Kernel source target)
    (monotone : ∀ index, le (kernels index) (kernels (index + 1)))
    (increments : Nat → Kernel source target)
    (finite : ∀ index, IsSFinite (increments index))
    (prefix_eq : ∀ index, kernels index = prefixSum increments index) :
    IsSFinite (iSupIncreasing kernels monotone) := by
  have equal : iSupIncreasing kernels monotone =
      iSupIncreasing (prefixSum increments) (prefixSum_monotone increments) := by
    apply Kernel.ext_measurable
    intro input set measurable
    rw [iSupIncreasing_apply_measurable kernels monotone input measurable,
      iSupIncreasing_apply_measurable _ _ input measurable]
    apply congrArg ENNReal.iSup
    funext index
    exact congrArg (fun kernel : Kernel source target => kernel input set) (prefix_eq index)
  rw [equal, ← sum_eq_iSupIncreasing_prefixSum]
  exact IsSFinite.sum increments finite

/-- The diagonal limit of two increasing kernel chains is s-finite when each
chain has cumulative s-finite increments. The output increments collect the
composition paths first completed at each common depth. -/
public noncomputable def IsSFinite.compIncreasingOfPrefixSum
    {middleType : Type w} {middle : Space middleType}
    (first : Nat → Kernel source middle)
    (firstMonotone : ∀ index, le (first index) (first (index + 1)))
    (second : Nat → Kernel middle target)
    (secondMonotone : ∀ index, le (second index) (second (index + 1)))
    (firstIncrements : Nat → Kernel source middle)
    (secondIncrements : Nat → Kernel middle target)
    (firstFinite : ∀ index, IsSFinite (firstIncrements index))
    (secondFinite : ∀ index, IsSFinite (secondIncrements index))
    (firstPrefix : ∀ index, first index = prefixSum firstIncrements index)
    (secondPrefix : ∀ index, second index = prefixSum secondIncrements index) :
    IsSFinite
      ((iSupIncreasing first firstMonotone).comp
        (iSupIncreasing second secondMonotone)) := by
  rw [comp_iSupIncreasing_diagonal]
  exact IsSFinite.ofPrefixSum
    (fun index => (first index).comp (second index))
    (fun index => le_trans
      (comp_le_comp_left (firstMonotone index) (second index))
      (comp_le_comp_right (first (index + 1)) (secondMonotone index)))
    (Kernel.diagonalPrefixIncrement firstIncrements secondIncrements)
    (IsSFinite.diagonalPrefixIncrement firstIncrements secondIncrements
      firstFinite secondFinite)
    (fun index => by
      rw [firstPrefix index, secondPrefix index]
      exact comp_prefixSum_eq_prefixSum_diagonalPrefixIncrement
        firstIncrements secondIncrements index)

end Problib.Measure.Kernel
