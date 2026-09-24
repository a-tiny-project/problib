module

public import Problib.Measure.Kernel.Supremum
public import Problib.Measure.Kernel.Iteration.Basic

set_option autoImplicit false

/-! Least fixed points of monotone, countably continuous kernel operators. -/

namespace Problib.Measure.Kernel

open Problib.Real

universe u v

variable {alpha : Type u} {beta : Type v}
  {source : Space alpha} {target : Space beta}

/-- An operator that preserves the supremum of every increasing kernel chain. -/
public structure OmegaContinuous
    (operator : Kernel source target → Kernel source target) : Prop where
  monotone : ∀ {left right}, le left right → le (operator left) (operator right)
  continuous : ∀ (kernels : Nat → Kernel source target)
      (increasing : ∀ index, le (kernels index) (kernels (index + 1))),
    operator (iSupIncreasing kernels increasing) =
      iSupIncreasing (fun index => operator (kernels index))
        (fun index => monotone (increasing index))

/-- Exiting now or taking one step is continuous in the continuation kernel. -/
public theorem OmegaContinuous.linear (step : Kernel source source)
    (exit : Kernel source target) :
    OmegaContinuous (fun continuation => Kernel.add exit (step.comp continuation)) := by
  refine ⟨?_, ?_⟩
  · intro left right included
    exact add_le_add (le_refl exit) (comp_le_comp_right step included)
  · intro kernels increasing
    rw [comp_iSupIncreasing_right step kernels increasing]
    exact add_iSupIncreasing exit
      (fun index => step.comp (kernels index))
      (fun index => comp_le_comp_right step (increasing index))

/-- Apply an operator a finite number of times, beginning at the zero kernel. -/
@[expose] public noncomputable def fixedPointApproximant
    (operator : Kernel source target → Kernel source target) :
    Nat → Kernel source target
  | 0 => Kernel.zero source target
  | count + 1 => operator (fixedPointApproximant operator count)

/-- Each additional unfolding adds to a positive operator's approximant. -/
public theorem fixedPointApproximant_monotone
    (operator : Kernel source target → Kernel source target)
    (monotone : ∀ {left right}, le left right → le (operator left) (operator right))
    (count : Nat) :
    le (fixedPointApproximant operator count)
      (fixedPointApproximant operator (count + 1)) := by
  induction count with
  | zero => exact zero_le _
  | succ count induction => exact monotone induction

/-- The supremum of the finite zero-based unfoldings. -/
@[expose] public noncomputable def leastFixedPoint
    (operator : Kernel source target → Kernel source target)
    (continuous : OmegaContinuous operator) : Kernel source target :=
  iSupIncreasing (fixedPointApproximant operator)
    (fixedPointApproximant_monotone operator continuous.monotone)

/-- The least fixed point evaluates as the supremum of finite unfoldings. -/
public theorem leastFixedPoint_apply_measurable
    (operator : Kernel source target → Kernel source target)
    (continuous : OmegaContinuous operator) (input : alpha)
    {set : Set beta} (measurable : target.Measurable set) :
    leastFixedPoint operator continuous input set =
      ENNReal.iSup (fun count => fixedPointApproximant operator count input set) :=
  iSupIncreasing_apply_measurable _ _ input measurable

/-- The supremum satisfies its one-step unfolding equation. -/
public theorem leastFixedPoint_unfold
    (operator : Kernel source target → Kernel source target)
    (continuous : OmegaContinuous operator) :
    operator (leastFixedPoint operator continuous) =
      leastFixedPoint operator continuous := by
  let approximants := fixedPointApproximant operator
  let increasing := fixedPointApproximant_monotone operator continuous.monotone
  change operator (iSupIncreasing approximants increasing) =
    iSupIncreasing approximants increasing
  rw [continuous.continuous approximants increasing]
  apply le_antisymm
  · apply iSupIncreasing_le
    intro count
    exact le_iSupIncreasing approximants increasing (count + 1)
  · apply iSupIncreasing_le
    intro count
    cases count with
    | zero => exact zero_le _
    | succ count =>
        exact le_iSupIncreasing (fun index => operator (approximants index))
          (fun index => continuous.monotone (increasing index)) count

/-- Every pre-fixed point bounds the supremum of the zero-based unfoldings. -/
public theorem leastFixedPoint_least
    (operator : Kernel source target → Kernel source target)
    (continuous : OmegaContinuous operator)
    (candidate : Kernel source target)
    (prefixed : le (operator candidate) candidate) :
    le (leastFixedPoint operator continuous) candidate := by
  apply iSupIncreasing_le
  intro count
  induction count with
  | zero => exact zero_le candidate
  | succ count induction =>
      exact le_trans (continuous.monotone induction) prefixed

/-- The countable exit-path loop is the least fixed point of its linear
continuation operator. -/
public theorem leastFixedPoint_linear_eq_loop (step : Kernel source source)
    (exit : Kernel source target) :
    leastFixedPoint (fun continuation => Kernel.add exit (step.comp continuation))
      (OmegaContinuous.linear step exit) = loop step exit := by
  apply le_antisymm
  · apply leastFixedPoint_least
    rw [← loop_unfold step exit]
    exact le_refl _
  · apply loop_least
    rw [leastFixedPoint_unfold
      (fun continuation => Kernel.add exit (step.comp continuation))
      (OmegaContinuous.linear step exit)]
    exact le_refl _

/-- An operator whose finite unfoldings are cumulative s-finite increments
has an s-finite least fixed point. The increment presentation is essential:
monotonicity alone supplies no constructive decomposition. -/
public noncomputable def IsSFinite.leastFixedPointOfPrefixSum
    (operator : Kernel source target → Kernel source target)
    (continuous : OmegaContinuous operator)
    (increments : Nat → Kernel source target)
    (finite : ∀ index, IsSFinite (increments index))
    (prefix_eq : ∀ index,
      fixedPointApproximant operator index = prefixSum increments index) :
    IsSFinite (leastFixedPoint operator continuous) :=
  IsSFinite.ofPrefixSum
    (fixedPointApproximant operator)
    (fixedPointApproximant_monotone operator continuous.monotone)
    increments finite prefix_eq

end Problib.Measure.Kernel
