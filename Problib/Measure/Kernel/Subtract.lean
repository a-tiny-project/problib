module

public import Problib.Measure.Kernel.Iteration.Algebra
public import Problib.Measure.Additive.Subtract
public import Problib.Measure.Extended.Algebra.Binary

set_option autoImplicit false

namespace Problib.Measure.Kernel

open Problib.Real

universe u v
variable {α : Type u} {β : Type v}
  {source : Space α} {target : Space β}

/-- Fiberwise subtraction of a finite dominated subkernel. -/
@[expose] public noncomputable def subtract {left right : Kernel source target}
    (rightFinite : ∀ input, Measure.IsFinite (right input))
    (included : ∀ input set, target.Measurable set →
      ENNReal.le (right input set) (left input set)) :
    Kernel source target where
  toFun := fun input => Measure.subtract (rightFinite input) (included input)
  measurable := by
    intro set setMeasurable
    have difference := ENNRealMeasurable.sub
      (left.measurable setMeasurable) (right.measurable setMeasurable)
    have equal : (fun input =>
        Measure.subtract (rightFinite input) (included input) set) =
        (fun input => ENNReal.sub (left input set) (right input set)) := by
      funext input
      exact Measure.subtract_apply (rightFinite input)
        (included input) setMeasurable
    rw [equal]
    exact difference

public theorem subtract_apply {left right : Kernel source target}
    (rightFinite : ∀ input, Measure.IsFinite (right input))
    (included : ∀ input set, target.Measurable set →
      ENNReal.le (right input set) (left input set))
    (input : α) {set : Set β} (setMeasurable : target.Measurable set) :
    subtract rightFinite included input set =
      ENNReal.sub (left input set) (right input set) :=
  Measure.subtract_apply (rightFinite input) (included input) setMeasurable

public theorem subtract_add {left right : Kernel source target}
    (rightFinite : ∀ input, Measure.IsFinite (right input))
    (included : ∀ input set, target.Measurable set →
      ENNReal.le (right input set) (left input set)) :
    Kernel.add (subtract rightFinite included) right = left := by
  apply Kernel.ext
  intro input
  rw [Kernel.add_apply]
  exact Measure.subtract_add (rightFinite input) (included input)

public theorem subtract_unique {left right remainder : Kernel source target}
    (rightFinite : ∀ input, Measure.IsFinite (right input))
    (included : ∀ input set, target.Measurable set →
      ENNReal.le (right input set) (left input set))
    (sum : Kernel.add remainder right = left) :
    remainder = subtract rightFinite included := by
  apply Kernel.ext
  intro input
  exact Measure.subtract_unique (rightFinite input) (included input)
    (by simpa only [Kernel.add_apply] using congrArg (fun K => K input) sum)

public theorem subtract_le {left right : Kernel source target}
    (rightFinite : ∀ input, Measure.IsFinite (right input))
    (included : ∀ input set, target.Measurable set →
      ENNReal.le (right input set) (left input set)) :
    Kernel.le (subtract rightFinite included) left := by
  intro input set _
  exact Measure.subtract_le (rightFinite input) (included input) set

end Problib.Measure.Kernel
