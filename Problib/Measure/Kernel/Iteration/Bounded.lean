module

public import Problib.Measure.Kernel.Iteration.Termination
public import Problib.Measure.Kernel.Iteration.Laws
public import Problib.Measure.Kernel.Composition.Transport
public import Problib.Measure.Space.Sum

set_option autoImplicit false

namespace Problib.Measure.Kernel
open Problib.Real
universe u v
variable {alpha : Type u} {beta : Type v}
  {source : Space alpha} {target : Space beta}

/-- A bounded loop reports the retained state on exhaustion, or an output on success. -/
@[expose] public noncomputable def boundedLoop (step : Kernel source source)
    (exit : Kernel source target) (count : Nat) : Kernel source (Space.sum source target) :=
  Kernel.add ((iterate step count).map Sum.inl (MeasurableMap.inl source target))
    ((prefixApproximant step exit count).map Sum.inr (MeasurableMap.inr source target))

/-- The outcome measure keeps the continuing and delivered measures in disjoint branches. -/
public theorem boundedLoop_apply (step : Kernel source source)
    (exit : Kernel source target) (count : Nat) (input : alpha)
    {region : Set (Sum alpha beta)} (measurable : (Space.sum source target).Measurable region) :
    boundedLoop step exit count input region =
      ENNReal.add (iterate step count input (Set.preimage Sum.inl region))
        (prefixApproximant step exit count input (Set.preimage Sum.inr region)) := by
  unfold boundedLoop
  rw [Kernel.add_apply, Measure.add_apply_measurable _ _ measurable,
    map_apply, map_apply, Measure.map_apply _ _ _ measurable,
    Measure.map_apply _ _ _ measurable]

/-- Exhaustion retains exactly the residual transition measure. -/
public theorem boundedLoop_exhausted (step : Kernel source source)
    (exit : Kernel source target) (count : Nat) (input : alpha)
    {region : Set alpha} (measurable : source.Measurable region) :
    boundedLoop step exit count input (Sum.elim region (fun _ => False)) =
      iterate step count input region := by
  rw [boundedLoop_apply step exit count input (show
    (Space.sum source target).Measurable (Sum.elim region (fun _ => False)) from
      ⟨measurable, target.empty⟩)]
  change ENNReal.add (iterate step count input region)
    (prefixApproximant step exit count input Set.empty) = _
  rw [Measure.empty_apply, ENNReal.add_zero]

/-- Successful outcomes retain exactly the finite exit prefix. -/
public theorem boundedLoop_succeeded (step : Kernel source source)
    (exit : Kernel source target) (count : Nat) (input : alpha)
    {region : Set beta} (measurable : target.Measurable region) :
    boundedLoop step exit count input (Sum.elim (fun _ => False) region) =
      prefixApproximant step exit count input region := by
  rw [boundedLoop_apply step exit count input (show
    (Space.sum source target).Measurable (Sum.elim (fun _ => False) region) from
      ⟨source.empty, measurable⟩)]
  change ENNReal.add (iterate step count input Set.empty)
    (prefixApproximant step exit count input region) = _
  rw [Measure.empty_apply, ENNReal.zero_add]

/-- A zero budget reports the initial state without running an attempt. -/
public theorem boundedLoop_zero (step : Kernel source source)
    (exit : Kernel source target) :
    boundedLoop step exit 0 =
      Kernel.deterministic Sum.inl (MeasurableMap.inl source target) := by
  apply Kernel.ext
  intro input
  unfold boundedLoop
  rw [Kernel.add_apply, map_apply, map_apply, prefixApproximant_zero,
    Kernel.zero_apply, Measure.map_zero, Measure.add_zero,
    iterate_zero, deterministic_apply, Measure.map_dirac, deterministic_apply]

/-- Without an exit, the entire residual measure is reported as exhausted. -/
public theorem boundedLoop_zero_exit (step : Kernel source source) (count : Nat) :
    boundedLoop step (Kernel.zero source target) count =
      (iterate step count).map Sum.inl (MeasurableMap.inl source target) := by
  apply Kernel.ext
  intro input
  unfold boundedLoop
  rw [Kernel.add_apply, map_apply, map_apply, prefixApproximant_zero_exit,
    Kernel.zero_apply, Measure.map_zero, Measure.add_zero]

/-- One attempt either exits or spends one unit of the remaining budget. -/
public theorem boundedLoop_succ (step : Kernel source source)
    (exit : Kernel source target) (count : Nat) :
    boundedLoop step exit (count + 1) =
      Kernel.add (exit.map Sum.inr (MeasurableMap.inr source target))
        (step.comp (boundedLoop step exit count)) := by
  unfold boundedLoop
  rw [iterate_succ, prefixApproximant_step_unfold, comp_map, comp_add_distrib]
  apply Kernel.ext
  intro input
  rw [Kernel.add_apply, Kernel.add_apply, Kernel.add_apply,
    map_apply, Kernel.add_apply, Measure.map_add]
  have mapped := congrArg (fun kernel : Kernel source (Space.sum source target) => kernel input)
    (comp_map step (prefixApproximant step exit count) Sum.inr
      (MeasurableMap.inr source target))
  rw [map_apply] at mapped
  rw [mapped, ← Measure.add_assoc, Measure.add_comm
    ((step.comp ((iterate step count).map Sum.inl (MeasurableMap.inl source target))) input),
    Measure.add_assoc]
  rfl

/-- Reporting exhaustion conserves total probability for every finite budget. -/
public theorem boundedLoop_isProbability (step : Kernel source source)
    (exit : Kernel source target)
    (conservative : ∀ input,
      ENNReal.add (step input Set.univ) (exit input Set.univ) = ENNReal.one)
    (count : Nat) (input : alpha) : Measure.IsProbability (boundedLoop step exit count input) := by
  constructor
  rw [boundedLoop_apply step exit count input (Space.sum source target).univ,
    Set.preimage_univ, Set.preimage_univ, ENNReal.add_comm]
  exact prefix_mass_eq_one step exit conservative count input

end Problib.Measure.Kernel
