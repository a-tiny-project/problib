module

public import Problib.Measure.Kernel.Iteration
public import Problib.Measure.Normalization

set_option autoImplicit false

namespace Problib.Measure.Kernel
open Problib.Real
universe u v
variable {alpha : Type u} {beta : Type v}
  {source : Space alpha} {target : Space beta}

/-- A retry retains the parameter and multiplies its continuing mass by its rejection weight. -/
@[expose] public noncomputable def retry (weight : alpha → ENNReal)
    (measurable : ENNRealMeasurable source weight) : Kernel source source where
  toFun := fun input => Measure.smul (weight input) (Measure.dirac source input)
  measurable := by
    intro set setMeasurable
    have product := measurable.mul
      ((Kernel.deterministic (fun input => input) (MeasurableMap.identity source)).measurable
        setMeasurable)
    have same : (fun input =>
        Measure.smul (weight input) (Measure.dirac source input) set) =
        (fun input => ENNReal.mul (weight input) (Measure.dirac source input set)) := by
      funext input
      exact Measure.smul_apply_measurable _ _ setMeasurable
    rw [same]
    exact product

@[simp] public theorem retry_apply (weight : alpha → ENNReal)
    (measurable : ENNRealMeasurable source weight) (input : alpha) :
    retry weight measurable input = Measure.smul (weight input) (Measure.dirac source input) := rfl

public theorem retry_mass (weight : alpha → ENNReal)
    (measurable : ENNRealMeasurable source weight) (input : alpha) :
    retry weight measurable input Set.univ = weight input := by
  rw [retry_apply, Measure.smul_apply_measurable _ _ source.univ,
    Measure.dirac_apply_univ, ENNReal.mul_one]

/-- Composing a retry with any continuation scales that continuation at the retained parameter. -/
public theorem retry_comp_apply (weight : alpha → ENNReal)
    (measurable : ENNRealMeasurable source weight) (continuation : Kernel source target)
    (input : alpha) :
    (retry weight measurable).comp continuation input =
      Measure.smul (weight input) (continuation input) := by
  rw [comp_apply, retry_apply, Measure.smul_bind, Measure.dirac_bind]

public theorem retry_prefix_succ (weight : alpha → ENNReal)
    (measurable : ENNRealMeasurable source weight) (exit : Kernel source target)
    (count : Nat) (input : alpha) :
    prefixApproximant (retry weight measurable) exit (count + 1) input =
      Measure.add (exit input)
        (Measure.smul (weight input)
          (prefixApproximant (retry weight measurable) exit count input)) := by
  rw [prefixApproximant_step_unfold, Kernel.add_apply, retry_comp_apply]

public theorem retry_residual_succ (weight : alpha → ENNReal)
    (measurable : ENNRealMeasurable source weight) (count : Nat) (input : alpha) :
    iterate (retry weight measurable) (count + 1) input =
      Measure.smul (weight input) (iterate (retry weight measurable) count input) := by
  rw [iterate_succ, retry_comp_apply]

public theorem retry_residual_mass_succ (weight : alpha → ENNReal)
    (measurable : ENNRealMeasurable source weight) (count : Nat) (input : alpha) :
    iterate (retry weight measurable) (count + 1) input Set.univ =
      ENNReal.mul (weight input)
        (iterate (retry weight measurable) count input Set.univ) := by
  rw [retry_residual_succ, Measure.smul_apply_measurable _ _ source.univ]

public theorem retry_conservative (weight : alpha → ENNReal)
    (measurable : ENNRealMeasurable source weight) (exit : Kernel source target)
    (conservative : ∀ input,
      ENNReal.add (weight input) (exit input Set.univ) = ENNReal.one) (input : alpha) :
    ENNReal.add (retry weight measurable input Set.univ) (exit input Set.univ) = ENNReal.one := by
  rw [retry_mass]
  exact conservative input

public theorem retry_isFinite (weight : alpha → ENNReal)
    (measurable : ENNRealMeasurable source weight) (exit : Kernel source target)
    (conservative : ∀ input,
      ENNReal.add (weight input) (exit input Set.univ) = ENNReal.one) :
    IsFinite (retry weight measurable) ∧ IsFinite exit := by
  apply substochastic_isFinite
  intro input
  rw [retry_conservative weight measurable exit conservative input]
  exact ENNReal.le_refl _

/-- Finite output bounds justify canceling the retry contribution in the unfolding equation. -/
public theorem loop_retry_reconstruct (weight : alpha → ENNReal)
    (measurable : ENNRealMeasurable source weight) (exit : Kernel source target)
    (conservative : ∀ input,
      ENNReal.add (weight input) (exit input Set.univ) = ENNReal.one) (input : alpha) :
    Measure.smul (exit input Set.univ) (loop (retry weight measurable) exit input) =
      exit input := by
  have bounded : ∀ value, ENNReal.le
      (ENNReal.add (retry weight measurable value Set.univ) (exit value Set.univ))
      ENNReal.one := by
    intro value
    rw [retry_conservative weight measurable exit conservative value]
    exact ENNReal.le_refl _
  have loopFinite := (loop_isFinite (retry weight measurable) exit bounded).measure input
  have weightFinite := ((retry_isFinite weight measurable exit conservative).1.measure input).univ_finite
  rw [retry_mass] at weightFinite
  have fixed := congrArg (fun kernel : Kernel source target => kernel input)
    (loop_unfold (retry weight measurable) exit)
  rw [Kernel.add_apply, retry_comp_apply] at fixed
  apply Measure.add_right_cancel_of_finite (loopFinite.smul (weight input) weightFinite)
  rw [← fixed]
  apply Measure.ext
  intro set setMeasurable
  rw [Measure.add_apply_measurable _ _ setMeasurable,
    Measure.smul_apply_measurable _ _ setMeasurable,
    Measure.smul_apply_measurable _ _ setMeasurable]
  rw [ENNReal.mul_comm (exit input Set.univ), ENNReal.mul_comm (weight input),
    ← ENNReal.mul_add, ENNReal.add_comm (exit input Set.univ), conservative input,
    ENNReal.mul_one]

public theorem retry_exit_normalizable (weight : alpha → ENNReal)
    (measurable : ENNRealMeasurable source weight) (exit : Kernel source target)
    (conservative : ∀ input,
      ENNReal.add (weight input) (exit input Set.univ) = ENNReal.one)
    (input : alpha) (positive : ENNReal.lt ENNReal.zero (exit input Set.univ)) :
    Measure.IsNormalizable (exit input) :=
  ⟨(retry_isFinite weight measurable exit conservative).2.measure input,
    ENNReal.zero_lt_iff_ne_zero.mp positive⟩

/-- Positive acceptance at the current parameter identifies unbounded retry with its normalized exit law. -/
public theorem loop_retry_eq_normalize (weight : alpha → ENNReal)
    (measurable : ENNRealMeasurable source weight) (exit : Kernel source target)
    (conservative : ∀ input,
      ENNReal.add (weight input) (exit input Set.univ) = ENNReal.one)
    (input : alpha) (positive : ENNReal.lt ENNReal.zero (exit input Set.univ)) :
    loop (retry weight measurable) exit input =
      Measure.normalize (exit input)
        (retry_exit_normalizable weight measurable exit conservative input positive) := by
  symm
  apply Measure.normalize_eq_of_smul_eq
  exact loop_retry_reconstruct weight measurable exit conservative input

public theorem loop_retry_isProbability (weight : alpha → ENNReal)
    (measurable : ENNRealMeasurable source weight) (exit : Kernel source target)
    (conservative : ∀ input,
      ENNReal.add (weight input) (exit input Set.univ) = ENNReal.one)
    (input : alpha) (positive : ENNReal.lt ENNReal.zero (exit input Set.univ)) :
    Measure.IsProbability (loop (retry weight measurable) exit input) := by
  rw [loop_retry_eq_normalize weight measurable exit conservative input positive]
  exact Measure.normalize_isProbability _ _

public theorem retry_vanishingContinuation (weight : alpha → ENNReal)
    (measurable : ENNRealMeasurable source weight) (exit : Kernel source target)
    (conservative : ∀ input,
      ENNReal.add (weight input) (exit input Set.univ) = ENNReal.one)
    (positive : ∀ input, ENNReal.lt ENNReal.zero (exit input Set.univ)) :
    VanishingContinuation (retry weight measurable) := by
  apply (loop_mass_one_everywhere_iff (retry weight measurable) exit
    (retry_conservative weight measurable exit conservative)).mp
  intro input
  exact (loop_retry_isProbability weight measurable exit conservative input (positive input)).univ_eq_one

end Problib.Measure.Kernel
