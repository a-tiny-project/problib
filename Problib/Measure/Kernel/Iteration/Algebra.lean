module

public import Problib.Measure.Kernel.Composition
public import Problib.Measure.Kernel.Basic
public import Problib.Real.Series.Tail
import Problib.Measure.Kernel.Composition.Bind
import Problib.Measure.Integral.Lebesgue.Algebra
import Problib.Measure.Integral.Lebesgue.Measure

set_option autoImplicit false

namespace Problib.Measure

open Problib.Real

universe u v w x

namespace Kernel

variable {alpha : Type u} {beta : Type v} {gamma : Type w} {delta : Type x}
  {source : Space alpha} {middle : Space beta} {target : Space gamma}

/-- Pointwise ordering of kernels on measurable sets. -/
@[expose] public def le (left right : Kernel source target) : Prop :=
  ∀ input set, target.Measurable set → ENNReal.le (left input set) (right input set)

public theorem le_refl (kernel : Kernel source target) : le kernel kernel :=
  fun _ _ _ => ENNReal.le_refl _

public theorem le_trans {first second third : Kernel source target}
    (firstSecond : le first second) (secondThird : le second third) :
    le first third :=
  fun input set measurable =>
    ENNReal.le_trans (firstSecond input set measurable) (secondThird input set measurable)

public theorem le_antisymm {left right : Kernel source target}
    (leftRight : le left right) (rightLeft : le right left) : left = right := by
  apply Kernel.ext_measurable
  intro input set measurable
  exact ENNReal.le_antisymm (leftRight input set measurable) (rightLeft input set measurable)

public theorem zero_le (kernel : Kernel source target) :
    le (Kernel.zero source target) kernel := by
  intro input set measurable
  rw [Kernel.zero_apply, Measure.zero_apply]
  exact ENNReal.zero_le _

public theorem add_assoc (first second third : Kernel source target) :
    Kernel.add (Kernel.add first second) third =
      Kernel.add first (Kernel.add second third) := by
  apply Kernel.ext
  intro input
  rw [Kernel.add_apply, Kernel.add_apply, Kernel.add_apply, Kernel.add_apply]
  exact Measure.add_assoc (first input) (second input) (third input)

public theorem zero_add (kernel : Kernel source target) :
    Kernel.add (Kernel.zero source target) kernel = kernel := by
  apply Kernel.ext
  intro input
  rw [Kernel.add_apply, Kernel.zero_apply, Measure.zero_add]

public theorem add_zero (kernel : Kernel source target) :
    Kernel.add kernel (Kernel.zero source target) = kernel := by
  apply Kernel.ext
  intro input
  rw [Kernel.add_apply, Kernel.zero_apply, Measure.add_zero]

public theorem comp_zero (step : Kernel source middle) :
    step.comp (Kernel.zero middle target) = Kernel.zero source target := by
  apply Kernel.ext
  intro input
  rw [Kernel.comp_apply, Measure.bind_zero]
  rfl

public theorem zero_comp (kernel : Kernel middle target) :
    (Kernel.zero source middle).comp kernel = Kernel.zero source target := by
  apply Kernel.ext
  intro input
  rw [Kernel.comp_apply, Kernel.zero_apply, Measure.zero_bind]
  rfl

public theorem add_le_add {left₁ right₁ left₂ right₂ : Kernel source target}
    (first : le left₁ right₁) (second : le left₂ right₂) :
    le (Kernel.add left₁ left₂) (Kernel.add right₁ right₂) := by
  intro input set measurable
  rw [Kernel.add_apply, Kernel.add_apply,
    Measure.add_apply_measurable _ _ measurable,
    Measure.add_apply_measurable _ _ measurable]
  exact ENNReal.add_le_add (first input set measurable) (second input set measurable)

public theorem comp_le_comp_right (step : Kernel source middle)
    {left right : Kernel middle target} (included : le left right) :
    le (step.comp left) (step.comp right) := by
  intro input set measurable
  rw [Kernel.comp_apply_measurable _ _ _ measurable,
    Kernel.comp_apply_measurable _ _ _ measurable]
  apply lintegral_mono (step input)
  intro value
  exact included value set measurable

public theorem comp_le_comp_left {left right : Kernel source middle}
    (included : le left right) (continuation : Kernel middle target) :
    le (left.comp continuation) (right.comp continuation) := by
  intro input set measurable
  rw [Kernel.comp_apply_measurable _ _ _ measurable,
    Kernel.comp_apply_measurable _ _ _ measurable]
  exact lintegral_mono_measure (fun value => continuation value set)
    (left input) (right input) (included input)

public theorem comp_add_distrib (step : Kernel source middle)
    (left right : Kernel middle target) :
    step.comp (Kernel.add left right) =
      Kernel.add (step.comp left) (step.comp right) := by
  apply Kernel.ext
  intro input
  apply Measure.ext
  intro set setMeasurable
  rw [comp_apply_measurable _ _ _ setMeasurable,
    Kernel.add_apply, Measure.add_apply_measurable _ _ setMeasurable,
    comp_apply_measurable _ _ _ setMeasurable,
    comp_apply_measurable _ _ _ setMeasurable]
  have equal : (fun value => (Kernel.add left right) value set) =
      (fun value => ENNReal.add (left value set) (right value set)) := by
    funext value
    rw [Kernel.add_apply, Measure.add_apply_measurable _ _ setMeasurable]
  rw [equal]
  exact lintegral_add (step input) (left.measurable setMeasurable) (right.measurable setMeasurable)

public theorem add_comp_distrib (left right : Kernel source middle)
    (continuation : Kernel middle target) :
    (Kernel.add left right).comp continuation =
      Kernel.add (left.comp continuation) (right.comp continuation) := by
  apply Kernel.ext
  intro input
  rw [Kernel.comp_apply, Kernel.add_apply, Measure.add_bind,
    Kernel.add_apply, Kernel.comp_apply, Kernel.comp_apply]

/-- Countable sums of kernels distribute over composition on the right. -/
public theorem comp_sum_right (first : Kernel source middle)
    (kernels : Nat → Kernel middle target) :
    first.comp (Kernel.sum kernels) =
      Kernel.sum (fun index => first.comp (kernels index)) := by
  apply Kernel.ext
  intro input
  rw [Kernel.comp_apply, Kernel.sum_apply]
  exact Measure.bind_sum_right (first input) kernels

/-- Countable sums of kernels distribute over composition on the left. -/
public theorem comp_sum_left (kernels : Nat → Kernel source middle)
    (second : Kernel middle target) :
    (Kernel.sum kernels).comp second =
      Kernel.sum (fun index => (kernels index).comp second) := by
  apply Kernel.ext
  intro input
  rw [Kernel.comp_apply, Kernel.sum_apply, Kernel.sum_apply]
  exact Measure.bind_sum_left (fun index => kernels index input) second

/-- Countable kernel sums unfold by splitting the initial term. -/
public theorem sum_split_head (kernels : Nat → Kernel source target) :
    Kernel.sum kernels =
      Kernel.add (kernels 0) (Kernel.sum (fun index => kernels (index + 1))) := by
  apply Kernel.ext_measurable
  intro input set setMeasurable
  rw [Kernel.sum_apply, Kernel.add_apply, Kernel.sum_apply,
    Measure.sum_apply _ setMeasurable,
    Measure.add_apply_measurable _ _ setMeasurable,
    Measure.sum_apply _ setMeasurable]
  have tailEq := ENNReal.partialSum_add_tail
    (fun index => kernels index input set) 1
  rw [ENNReal.partialSum, ENNReal.partialSum, ENNReal.zero_add] at tailEq
  rw [← tailEq]
  apply congrArg (ENNReal.add _)
  have indexShift : (fun index => kernels (1 + index) input set) =
      (fun index => kernels (index + 1) input set) := by
    funext index
    rw [Nat.add_comm 1 index]
  rw [indexShift]

end Kernel

end Problib.Measure
