module

public import Problib.Measure.Kernel.Iteration.Algebra

set_option autoImplicit false

namespace Problib.Measure

open Problib.Real

universe u v w x

namespace Kernel

variable {alpha : Type u} {beta : Type v} {gamma : Type w} {delta : Type x}
  {source : Space alpha} {middle : Space beta} {target : Space gamma}

/-- Repeated composition powers of an endokernel. -/
@[expose] public noncomputable def iterate (kernel : Kernel source source) :
    Nat → Kernel source source
  | 0 => Kernel.deterministic (fun value => value) (MeasurableMap.identity source)
  | count + 1 => kernel.comp (iterate kernel count)

@[simp] public theorem iterate_zero (kernel : Kernel source source) :
    iterate kernel 0 =
      Kernel.deterministic (fun value => value) (MeasurableMap.identity source) :=
  rfl

@[simp] public theorem iterate_succ (kernel : Kernel source source) (count : Nat) :
    iterate kernel (count + 1) = kernel.comp (iterate kernel count) :=
  rfl

public theorem iterate_succ_right (kernel : Kernel source source) (count : Nat) :
    iterate kernel (count + 1) = (iterate kernel count).comp kernel := by
  induction count with
  | zero =>
      rw [iterate_succ, iterate_zero, comp_deterministic]
      apply Kernel.ext
      intro input
      rw [map_apply, Measure.map_id, deterministic_comp_apply]
  | succ count induction =>
      change kernel.comp (iterate kernel (count + 1)) =
        (kernel.comp (iterate kernel count)).comp kernel
      rw [induction, comp_assoc]

/-- Unbounded probabilistic iteration kernel defined as the countable sum of exit paths. -/
@[expose] public noncomputable def loop (step : Kernel source source)
    (exit : Kernel source target) : Kernel source target :=
  Kernel.sum (fun count => (iterate step count).comp exit)

@[simp] public theorem loop_apply (step : Kernel source source)
    (exit : Kernel source target) (input : alpha) :
    loop step exit input =
      Measure.sum (fun count => ((iterate step count).comp exit) input) :=
  rfl

/-- Successive exit approximants summing finite execution prefixes. -/
@[expose] public noncomputable def prefixApproximant (step : Kernel source source)
    (exit : Kernel source target) : Nat → Kernel source target
  | 0 => Kernel.zero source target
  | count + 1 => Kernel.add (prefixApproximant step exit count)
      ((iterate step count).comp exit)

@[simp] public theorem prefixApproximant_zero (step : Kernel source source)
    (exit : Kernel source target) :
    prefixApproximant step exit 0 = Kernel.zero source target :=
  rfl

@[simp] public theorem prefixApproximant_succ (step : Kernel source source)
    (exit : Kernel source target) (count : Nat) :
    prefixApproximant step exit (count + 1) =
      Kernel.add (prefixApproximant step exit count)
        ((iterate step count).comp exit) :=
  rfl

/-- Successive approximants obtained by iterating the unfolding operator from zero. -/
@[expose] public noncomputable def stepApproximant (step : Kernel source source)
    (exit : Kernel source target) : Nat → Kernel source target
  | 0 => Kernel.zero source target
  | count + 1 => Kernel.add exit (step.comp (stepApproximant step exit count))

@[simp] public theorem stepApproximant_zero (step : Kernel source source)
    (exit : Kernel source target) :
    stepApproximant step exit 0 = Kernel.zero source target :=
  rfl

@[simp] public theorem stepApproximant_succ (step : Kernel source source)
    (exit : Kernel source target) (count : Nat) :
    stepApproximant step exit (count + 1) =
      Kernel.add exit (step.comp (stepApproximant step exit count)) :=
  rfl

/-- Step unfolding relation for finite exit prefixes. -/
public theorem prefixApproximant_step_unfold (step : Kernel source source)
    (exit : Kernel source target) (count : Nat) :
    prefixApproximant step exit (count + 1) =
      Kernel.add exit (step.comp (prefixApproximant step exit count)) := by
  induction count with
  | zero =>
      rw [prefixApproximant_succ, prefixApproximant_zero, zero_add]
      rw [comp_zero, add_zero]
      apply Kernel.ext
      intro input
      rw [comp_apply, iterate_zero, deterministic_apply, Measure.dirac_bind]
  | succ count induction =>
      rw [prefixApproximant_succ, prefixApproximant_succ step exit count,
        comp_add_distrib, ← add_assoc, ← induction]
      apply congrArg (Kernel.add (prefixApproximant step exit (count + 1)))
      rw [iterate_succ, comp_assoc]

/-- Finite exit prefixes agree with successive approximants from zero. -/
public theorem prefixApproximant_eq_stepApproximant (step : Kernel source source)
    (exit : Kernel source target) (count : Nat) :
    prefixApproximant step exit count = stepApproximant step exit count := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [stepApproximant_succ, ← induction, ← prefixApproximant_step_unfold]

/-- Pointwise evaluation of prefix approximants matches partial sums on measurable sets. -/
public theorem prefixApproximant_apply_measurable (step : Kernel source source)
    (exit : Kernel source target) (count : Nat) (input : alpha)
    {set : Set gamma} (setMeasurable : target.Measurable set) :
    prefixApproximant step exit count input set =
      ENNReal.partialSum (fun index => ((iterate step index).comp exit) input set) count := by
  induction count with
  | zero =>
      rw [prefixApproximant_zero, Kernel.zero_apply, Measure.zero_apply,
        ENNReal.partialSum]
  | succ count induction =>
      rw [prefixApproximant_succ, Kernel.add_apply,
        Measure.add_apply_measurable _ _ setMeasurable,
        induction, ENNReal.partialSum]

/-- The constructed loop is the pointwise supremum of its finite prefix approximants. -/
public theorem loop_eq_iSup_prefixApproximant (step : Kernel source source)
    (exit : Kernel source target) (input : alpha)
    {set : Set gamma} (setMeasurable : target.Measurable set) :
    loop step exit input set =
      ENNReal.iSup (fun count => prefixApproximant step exit count input set) := by
  rw [loop_apply, Measure.sum_apply _ setMeasurable]
  unfold ENNReal.tsum
  apply congrArg ENNReal.iSup
  funext count
  exact (prefixApproximant_apply_measurable step exit count input setMeasurable).symm

/-- Increasing the finite execution horizon only adds exit paths. -/
public theorem prefixApproximant_monotone (step : Kernel source source)
    (exit : Kernel source target) {first second : Nat} (included : first ≤ second) :
    le (prefixApproximant step exit first) (prefixApproximant step exit second) := by
  intro input set measurable
  rw [prefixApproximant_apply_measurable step exit first input measurable,
    prefixApproximant_apply_measurable step exit second input measurable]
  exact ENNReal.partialSum_monotone _ included

public theorem prefixApproximant_le_loop (step : Kernel source source)
    (exit : Kernel source target) (count : Nat) :
    le (prefixApproximant step exit count) (loop step exit) := by
  intro input set measurable
  rw [loop_eq_iSup_prefixApproximant step exit input measurable]
  exact ENNReal.le_iSup (fun index => prefixApproximant step exit index input set) count

/-- Unfolding equation for the loop kernel. -/
public theorem loop_unfold (step : Kernel source source)
    (exit : Kernel source target) :
    loop step exit = Kernel.add exit (step.comp (loop step exit)) := by
  unfold loop
  rw [comp_sum_right, sum_split_head]
  apply Kernel.ext
  intro input
  rw [Kernel.add_apply, Kernel.add_apply]
  congr 1
  · change ((iterate step 0).comp exit) input = exit input
    rw [iterate_zero, comp_apply, deterministic_apply, Measure.dirac_bind]
  · change (Kernel.sum fun index => (iterate step (index + 1)).comp exit) input =
      (Kernel.sum fun index => step.comp ((iterate step index).comp exit)) input
    rw [Kernel.sum_apply, Kernel.sum_apply]
    apply congrArg Measure.sum
    funext index
    rw [iterate_succ, comp_assoc]

/-- The constructed loop is the least pre-fixed point of R + Q comp X <= X. -/
public theorem loop_least (step : Kernel source source)
    (exit : Kernel source target) (candidate : Kernel source target)
    (prefixed : le (Kernel.add exit (step.comp candidate)) candidate) :
    le (loop step exit) candidate := by
  have stepBounded : ∀ count, le (stepApproximant step exit count) candidate := by
    intro count
    induction count with
    | zero =>
        rw [stepApproximant_zero]
        exact zero_le candidate
    | succ count induction =>
        rw [stepApproximant_succ]
        exact le_trans (add_le_add (le_refl exit) (comp_le_comp_right step induction)) prefixed
  intro input set setMeasurable
  rw [loop_eq_iSup_prefixApproximant step exit input setMeasurable]
  apply ENNReal.iSup_le
  intro count
  rw [prefixApproximant_eq_stepApproximant]
  exact stepBounded count input set setMeasurable

namespace IsSFinite

/-- Repeated composition preserves constructive s-finiteness. -/
public noncomputable def iterate {kernel : Kernel source source}
    (finite : IsSFinite kernel) (count : Nat) : IsSFinite (Kernel.iterate kernel count) := by
  induction count with
  | zero => exact IsSFinite.deterministic (fun value => value) (MeasurableMap.identity source)
  | succ count induction => exact IsSFinite.comp finite induction

/-- S-finite steps and exits construct a globally s-finite iteration loop. -/
public noncomputable def loop {step : Kernel source source}
    {exit : Kernel source target} (stepFinite : IsSFinite step)
    (exitFinite : IsSFinite exit) : IsSFinite (Kernel.loop step exit) := by
  unfold Kernel.loop
  apply IsSFinite.sum
  intro count
  exact IsSFinite.comp (iterate stepFinite count) exitFinite

end IsSFinite

end Kernel

end Problib.Measure
