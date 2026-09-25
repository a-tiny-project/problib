module

public import Problib.Measure.Additive.Counting
public import Problib.Measure.Necessity.Density
public import Problib.Measure.Integral.Lebesgue.Algebra
public import Problib.Real.Approximation

set_option autoImplicit false

open Problib.Real Problib.Measure
open Problib.Real.Construction

namespace Problib.Measure.Necessity.Integral

universe u

/-- Concrete strictly positive scalar reciprocals 1/(index + 1) in ENNReal. -/
@[expose] public noncomputable def reciprocal (index : Nat) : ENNReal :=
  ENNReal.ofReal (Dedekind.inverse (Dedekind.selection.ofRat (Nat.succ index : Rat)))

private theorem reciprocal_nonzero (index : Nat) : reciprocal index ≠ ENNReal.zero := by
  intro equal
  exact (Dedekind.inverse_of_positive_positive (Dedekind.ofRat_succ_positive index)).2
    (ENNReal.ofReal_eq_zero_iff.mp equal)

private theorem reciprocal_antitone {first second : Nat} (included : first ≤ second) :
    ENNReal.le (reciprocal second) (reciprocal first) := by
  rcases Nat.lt_or_eq_of_le included with less | equal
  · apply ENNReal.ofReal_monotone
    apply (Dedekind.inverse_lt_inverse_of_positive
      (Dedekind.ofRat_succ_positive first) (Dedekind.ofRat_succ_positive second) ?_).1
    exact (Dedekind.ofRat_lt_iff (Nat.succ first : Rat) (Nat.succ second : Rat)).mpr
      (Rat.natCast_lt_natCast.mpr (Nat.succ_lt_succ less))
  · rw [equal]
    exact ENNReal.le_refl _

private theorem reciprocal_infimum : ENNReal.iInf reciprocal = ENNReal.zero := by
  classical
  apply Classical.byContradiction
  intro nonzero
  have finite : ENNReal.Finite (ENNReal.iInf reciprocal) :=
    ENNReal.finite_of_le (ENNReal.iInf_le reciprocal 0) (ENNReal.ofReal_finite _)
  have positive : Dedekind.lt Dedekind.zero (ENNReal.toReal (ENNReal.iInf reciprocal)) := by
    simpa only [ENNReal.toReal_zero] using
      (ENNReal.toReal_lt_toReal_iff (show ENNReal.Finite ENNReal.zero from True.intro) finite).mpr
        (ENNReal.zero_lt_iff_ne_zero.mpr nonzero)
  rcases Dedekind.exists_positive_inverse_below positive with ⟨index, indexPositive, below⟩
  cases index with
  | zero =>
      change Dedekind.lt Dedekind.zero (Dedekind.selection.ofRat (0 : Rat)) at indexPositive
      rw [Dedekind.ofRat_zero] at indexPositive
      exact Dedekind.lt_irrefl _ indexPositive
  | succ predecessor =>
      apply below.2
      have included := (ENNReal.toReal_le_toReal_iff finite (ENNReal.ofReal_finite _)).mpr
        (ENNReal.iInf_le reciprocal predecessor)
      simpa only [reciprocal, ENNReal.toReal_ofReal
        (Dedekind.inverse_of_positive_positive (Dedekind.ofRat_succ_positive predecessor)).1]
        using included

/-- Constant functions taking value 1/(index + 1) everywhere on an arbitrary
space. -/
@[expose] public noncomputable def functions {α : Type u} (index : Nat) (_ : α) : ENNReal := reciprocal index

/-- The constant reciprocal functions are measurable. -/
public theorem functions_measurable {α : Type u} (space : Space α) (index : Nat) :
    ENNRealMeasurable space (functions index) :=
  ENNRealMeasurable.constant _ _

/-- The constant reciprocal functions decrease pointwise as index grows. -/
public theorem functions_antitone {α : Type u} {first second : Nat}
    (included : first ≤ second) (input : α) :
    ENNReal.le (functions second input) (functions first input) := reciprocal_antitone included

/-- The constant reciprocal functions take finite values everywhere. -/
public theorem functions_finite {α : Type u} (index : Nat) (input : α) :
    ENNReal.Finite (functions index input) := ENNReal.ofReal_finite _

/-- The constant reciprocal functions take strictly positive values
everywhere. -/
public theorem functions_positive {α : Type u} (index : Nat) (input : α) :
    ENNReal.lt ENNReal.zero (functions index input) :=
  ENNReal.zero_lt_iff_ne_zero.mpr (reciprocal_nonzero index)

/-- The pointwise infimum of the constant reciprocal functions is zero. -/
public theorem functions_iInf_zero {α : Type u} (input : α) :
    ENNReal.iInf (fun index => functions index input) = ENNReal.zero :=
  reciprocal_infimum

/-- Under any measure with infinite total mass, each reciprocal constant has
infinite lower integral. -/
public theorem functions_integral_top {α : Type u} {space : Space α} (measure : Measure space)
    (infiniteMass : measure Set.univ = ENNReal.top) (index : Nat) :
    lintegral measure (functions index) = ENNReal.top := by
  change lintegral measure (fun _ => reciprocal index) = ENNReal.top
  rw [lintegral_const, infiniteMass, ENNReal.mul_top_of_ne_zero (reciprocal_nonzero index)]

/-- The lower integral of the pointwise infimum of the reciprocal constants is
zero. -/
public theorem limit_integral_zero {α : Type u} {space : Space α} (measure : Measure space) :
    lintegral measure
      (fun input => ENNReal.iInf (fun index => functions index input)) = ENNReal.zero := by
  have equal : (fun input : α => ENNReal.iInf (fun index => functions index input)) =
      (fun _ => ENNReal.zero) := funext fun _ => reciprocal_infimum
  rw [equal, lintegral_zero]

/-- The reciprocal-constant sequence refutes continuity of the lower integral
from above under any measure with infinite total mass. -/
public theorem continuity_from_above_fails {α : Type u} {space : Space α} (measure : Measure space)
    (infiniteMass : measure Set.univ = ENNReal.top) :
    lintegral measure
        (fun input => ENNReal.iInf (fun index => functions index input)) ≠
      ENNReal.iInf (fun index => lintegral measure (functions index)) := by
  rw [limit_integral_zero]
  have equal : (fun index => lintegral measure (functions index)) =
      (fun _ => ENNReal.top) := funext (functions_integral_top measure infiniteMass)
  rw [equal, ENNReal.iInf_const]
  exact Ne.symm (ENNReal.top_ne_finite NNReal.zero)

/-- Counting measure on Nat refutes continuity of the lower integral from above
without a finite-integral term despite sigma-finiteness. -/
public theorem counting_counterexample :
    lintegral Measure.counting
        (fun input => ENNReal.iInf (fun index => functions index input)) ≠
      ENNReal.iInf (fun index => lintegral Measure.counting (functions index)) :=
  continuity_from_above_fails Measure.counting Measure.counting_univ

/-- Counting measure on Nat refutes unconditional integral subtraction exchange
for constant functions two and one. -/
public theorem subtraction_counterexample :
    lintegral Measure.counting (fun _ => ENNReal.sub
      (ENNReal.add ENNReal.one ENNReal.one) ENNReal.one) ≠
    ENNReal.sub
      (lintegral Measure.counting (fun _ => ENNReal.add ENNReal.one ENNReal.one))
      (lintegral Measure.counting (fun _ => ENNReal.one)) := by
  have doubleNonzero : ENNReal.add ENNReal.one ENNReal.one ≠ ENNReal.zero :=
    fun equal => ENNReal.one_ne_zero (ENNReal.add_eq_zero_iff.mp equal).1
  simp only [lintegral_const, Measure.counting_univ,
    ENNReal.add_sub_cancel_right (show ENNReal.Finite ENNReal.one from True.intro),
    ENNReal.mul_top_of_ne_zero ENNReal.one_ne_zero,
    ENNReal.mul_top_of_ne_zero doubleNonzero, ENNReal.sub_self]
  exact ENNReal.top_ne_finite NNReal.zero

/-- The one-point infinite-atom reference refutes continuity of the lower
integral from above without a finite-integral term. -/
public theorem infinite_atom_counterexample :
    lintegral Density.reference
        (fun input => ENNReal.iInf (fun index => functions index input)) ≠
      ENNReal.iInf (fun index => lintegral Density.reference (functions index)) :=
  continuity_from_above_fails Density.reference Density.reference_univ

end Problib.Measure.Necessity.Integral
