module

public import Problib.Measure.Kernel.Rejection.Basic
public import Problib.Real.Extended.Power

set_option autoImplicit false

namespace Problib.Measure.Kernel
open Problib.Real
universe u v
variable {alpha : Type u} {beta : Type v}
  {source : Space alpha} {target : Space beta}

/-- Parameter-preserving retries leave a geometric multiple of the initial point mass. -/
public theorem retry_residual (weight : alpha → ENNReal)
    (measurable : ENNRealMeasurable source weight) (count : Nat) (input : alpha) :
    iterate (retry weight measurable) count input =
      Measure.smul (ENNReal.pow (weight input) count) (Measure.dirac source input) := by
  induction count with
  | zero => rw [iterate_zero, deterministic_apply, ENNReal.pow, Measure.one_smul]
  | succ count induction =>
    rw [retry_residual_succ, induction, Measure.smul_smul, ENNReal.pow]

/-- Exhausting the whole budget has mass `q^count`, where `q` is rejection mass. -/
public theorem boundedLoop_retry_exhausted (weight : alpha → ENNReal)
    (measurable : ENNRealMeasurable source weight) (exit : Kernel source target)
    (count : Nat) (input : alpha) :
    boundedLoop (retry weight measurable) exit count input
        (Sum.elim Set.univ (fun _ => False)) =
      ENNReal.pow (weight input) count := by
  rw [boundedLoop_exhausted _ _ _ _ source.univ, retry_residual,
    Measure.smul_apply_measurable _ _ source.univ, Measure.dirac_apply_univ, ENNReal.mul_one]

/-- Every finite successful prefix is its own mass times the unbounded rejection law.
This equality also holds at zero budget or zero acceptance, when the prefix is zero. -/
public theorem retry_prefix_reconstruct (weight : alpha → ENNReal)
    (measurable : ENNRealMeasurable source weight) (exit : Kernel source target)
    (conservative : ∀ input,
      ENNReal.add (weight input) (exit input Set.univ) = ENNReal.one)
    (count : Nat) (input : alpha) :
    Measure.smul (prefixApproximant (retry weight measurable) exit count input Set.univ)
        (loop (retry weight measurable) exit input) =
      prefixApproximant (retry weight measurable) exit count input := by
  induction count with
  | zero =>
    rw [prefixApproximant_zero, Kernel.zero_apply, Measure.zero_apply, Measure.zero_smul]
  | succ count induction =>
    have reconstruct := loop_retry_reconstruct weight measurable exit conservative input
    apply Measure.ext
    intro region regionMeasurable
    have initial := congrArg (fun measure : Measure target => measure region) reconstruct
    have previous := congrArg (fun measure : Measure target => measure region) induction
    rw [Measure.smul_apply_measurable _ _ regionMeasurable] at initial previous
    rw [retry_prefix_succ, Measure.add_apply_measurable _ _ target.univ,
      Measure.smul_apply_measurable _ _ target.univ,
      Measure.smul_apply_measurable _ _ regionMeasurable,
      Measure.add_apply_measurable _ _ regionMeasurable,
      Measure.smul_apply_measurable _ _ regionMeasurable,
      ENNReal.mul_comm _ (loop (retry weight measurable) exit input region), ENNReal.mul_add,
      ENNReal.mul_comm (loop (retry weight measurable) exit input region) (exit input Set.univ),
      ENNReal.mul_comm (loop (retry weight measurable) exit input region) (ENNReal.mul _ _),
      ENNReal.mul_assoc, initial, previous]

/-- Positive acceptance and at least one attempt make the successful prefix normalizable. -/
public theorem retry_prefix_normalizable (weight : alpha → ENNReal)
    (measurable : ENNRealMeasurable source weight) (exit : Kernel source target)
    (conservative : ∀ input,
      ENNReal.add (weight input) (exit input Set.univ) = ENNReal.one)
    (count : Nat) (input : alpha) (positive : ENNReal.lt ENNReal.zero (exit input Set.univ)) :
    Measure.IsNormalizable (prefixApproximant (retry weight measurable) exit (count + 1) input) := by
  have bounded := prefix_mass_eq_one (retry weight measurable) exit
    (retry_conservative weight measurable exit conservative) (count + 1) input
  have included := ENNReal.add_le_add_left
    (ENNReal.zero_le (iterate (retry weight measurable) (count + 1) input Set.univ))
    (prefixApproximant (retry weight measurable) exit (count + 1) input Set.univ)
  rw [ENNReal.add_zero, bounded] at included
  refine ⟨⟨ENNReal.finite_of_le included True.intro⟩, ?_⟩
  intro vanished
  have initial := prefixApproximant_monotone (retry weight measurable) exit
    (show 1 ≤ count + 1 by omega) input Set.univ target.univ
  have first : prefixApproximant (retry weight measurable) exit 1 input = exit input := by
    rw [prefixApproximant_step_unfold, prefixApproximant_zero, comp_zero, add_zero]
  rw [first, vanished] at initial
  exact positive.2 initial

/-- Conditioning on finite-budget success has exactly the unbounded rejection law. -/
public theorem normalize_retry_prefix_eq_loop (weight : alpha → ENNReal)
    (measurable : ENNRealMeasurable source weight) (exit : Kernel source target)
    (conservative : ∀ input,
      ENNReal.add (weight input) (exit input Set.univ) = ENNReal.one)
    (count : Nat) (input : alpha) (positive : ENNReal.lt ENNReal.zero (exit input Set.univ)) :
    Measure.normalize (prefixApproximant (retry weight measurable) exit (count + 1) input)
        (retry_prefix_normalizable weight measurable exit conservative count input positive) =
      loop (retry weight measurable) exit input :=
  Measure.normalize_eq_of_smul_eq _ _ _
    (retry_prefix_reconstruct weight measurable exit conservative (count + 1) input)

/-- The conditional successful law is independent of the positive attempt budget. -/
public theorem normalize_retry_prefix_eq_normalize_exit (weight : alpha → ENNReal)
    (measurable : ENNRealMeasurable source weight) (exit : Kernel source target)
    (conservative : ∀ input,
      ENNReal.add (weight input) (exit input Set.univ) = ENNReal.one)
    (count : Nat) (input : alpha) (positive : ENNReal.lt ENNReal.zero (exit input Set.univ)) :
    Measure.normalize (prefixApproximant (retry weight measurable) exit (count + 1) input)
        (retry_prefix_normalizable weight measurable exit conservative count input positive) =
      Measure.normalize (exit input)
        (retry_exit_normalizable weight measurable exit conservative input positive) := by
  rw [normalize_retry_prefix_eq_loop weight measurable exit conservative count input positive,
    loop_retry_eq_normalize weight measurable exit conservative input positive]

end Problib.Measure.Kernel
