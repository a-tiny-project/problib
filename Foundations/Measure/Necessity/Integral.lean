module

public import Foundations.Measure.Additive.Counting
public import Foundations.Measure.Necessity.Density
public import Foundations.Measure.Integral.Lebesgue.Algebra
public import Foundations.Real.Approximation

set_option autoImplicit false

open Foundations.Real Foundations.Measure
open Foundations.Real.Construction

namespace Foundations.Measure.Necessity.Integral

universe u

/-- Concrete strictly positive scalar reciprocals 1/(index + 1) in ENNReal. -/
@[expose] public noncomputable def reciprocal (index : Nat) : ENNReal :=
  ENNReal.ofReal (Dedekind.inverse (Dedekind.selection.ofRat (Nat.succ index : Rat)))

private theorem denominatorPositive (index : Nat) :
    Dedekind.lt Dedekind.zero (Dedekind.selection.ofRat (Nat.succ index : Rat)) := by
  rw [← Dedekind.ofRatZero]
  exact (Dedekind.ofRatLtIff 0 (Nat.succ index : Rat)).mpr
    (Rat.natCast_pos.mpr (Nat.zero_lt_succ index))

private theorem reciprocalNonzero (index : Nat) : reciprocal index ≠ ENNReal.zero := by
  intro equal
  exact (Dedekind.inverseOfPositivePositive (denominatorPositive index)).2
    (ENNReal.ofRealEqZeroIff.mp equal)

private theorem reciprocalAntitone {first second : Nat} (included : first ≤ second) :
    ENNReal.le (reciprocal second) (reciprocal first) := by
  rcases Nat.lt_or_eq_of_le included with less | equal
  · apply ENNReal.ofRealMonotone
    apply (Dedekind.inverseLtInverseOfPositive
      (denominatorPositive first) (denominatorPositive second) ?_).1
    exact (Dedekind.ofRatLtIff (Nat.succ first : Rat) (Nat.succ second : Rat)).mpr
      (Rat.natCast_lt_natCast.mpr (Nat.succ_lt_succ less))
  · rw [equal]
    exact ENNReal.leRefl _

private theorem reciprocalInfimum : ENNReal.iInf reciprocal = ENNReal.zero := by
  classical
  apply Classical.byContradiction
  intro nonzero
  have finite : ENNReal.Finite (ENNReal.iInf reciprocal) :=
    ENNReal.finiteOfLe (ENNReal.iInfLe reciprocal 0) (ENNReal.ofRealFinite _)
  have positive : Dedekind.lt Dedekind.zero (ENNReal.toReal (ENNReal.iInf reciprocal)) := by
    simpa only [ENNReal.toRealZero] using
      (ENNReal.toRealLtToRealIff (show ENNReal.Finite ENNReal.zero from True.intro) finite).mpr
        (ENNReal.zeroLtIffNeZero.mpr nonzero)
  rcases Dedekind.existsPositiveInverseBelow positive with ⟨index, indexPositive, below⟩
  cases index with
  | zero =>
      change Dedekind.lt Dedekind.zero (Dedekind.selection.ofRat (0 : Rat)) at indexPositive
      rw [Dedekind.ofRatZero] at indexPositive
      exact Dedekind.ltIrrefl _ indexPositive
  | succ predecessor =>
      apply below.2
      have included := (ENNReal.toRealLeToRealIff finite (ENNReal.ofRealFinite _)).mpr
        (ENNReal.iInfLe reciprocal predecessor)
      simpa only [reciprocal, ENNReal.toRealOfReal
        (Dedekind.inverseOfPositivePositive (denominatorPositive predecessor)).1] using included

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
    ENNReal.le (functions second input) (functions first input) := reciprocalAntitone included

/-- The constant reciprocal functions take finite values everywhere. -/
public theorem functions_finite {α : Type u} (index : Nat) (input : α) :
    ENNReal.Finite (functions index input) := ENNReal.ofRealFinite _

/-- The constant reciprocal functions take strictly positive values
everywhere. -/
public theorem functions_positive {α : Type u} (index : Nat) (input : α) :
    ENNReal.lt ENNReal.zero (functions index input) :=
  ENNReal.zeroLtIffNeZero.mpr (reciprocalNonzero index)

/-- The pointwise infimum of the constant reciprocal functions is zero. -/
public theorem functions_iInf_zero {α : Type u} (input : α) :
    ENNReal.iInf (fun index => functions index input) = ENNReal.zero :=
  reciprocalInfimum

/-- Under any measure with infinite total mass, each reciprocal constant has
infinite lower integral. -/
public theorem functions_integral_top {α : Type u} {space : Space α} (measure : Measure space)
    (infiniteMass : measure Set.univ = ENNReal.top) (index : Nat) :
    lintegral measure (functions index) = ENNReal.top := by
  change lintegral measure (fun _ => reciprocal index) = ENNReal.top
  rw [lintegral_const, infiniteMass, ENNReal.mulTopOfNeZero (reciprocalNonzero index)]

/-- The lower integral of the pointwise infimum of the reciprocal constants is
zero. -/
public theorem limit_integral_zero {α : Type u} {space : Space α} (measure : Measure space) :
    lintegral measure
      (fun input => ENNReal.iInf (fun index => functions index input)) = ENNReal.zero := by
  have equal : (fun input : α => ENNReal.iInf (fun index => functions index input)) =
      (fun _ => ENNReal.zero) := funext fun _ => reciprocalInfimum
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
  rw [equal, ENNReal.iInfConst]
  exact Ne.symm (ENNReal.topNeFinite NNReal.zero)

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
    fun equal => ENNReal.oneNeZero (ENNReal.addEqZeroIff.mp equal).1
  simp only [lintegral_const, Measure.counting_univ,
    ENNReal.addSubCancelRight (show ENNReal.Finite ENNReal.one from True.intro),
    ENNReal.mulTopOfNeZero ENNReal.oneNeZero,
    ENNReal.mulTopOfNeZero doubleNonzero, ENNReal.subSelf]
  exact ENNReal.topNeFinite NNReal.zero

/-- The one-point infinite-atom reference refutes continuity of the lower
integral from above without a finite-integral term. -/
public theorem infinite_atom_counterexample :
    lintegral Density.reference
        (fun input => ENNReal.iInf (fun index => functions index input)) ≠
      ENNReal.iInf (fun index => lintegral Density.reference (functions index)) :=
  continuity_from_above_fails Density.reference Density.reference_univ

end Foundations.Measure.Necessity.Integral
