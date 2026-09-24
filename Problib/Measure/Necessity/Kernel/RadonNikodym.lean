module

public import Problib.Measure.Kernel.Density.Basic
public import Problib.Measure.Decomposition.RadonNikodym.Basic
public import Problib.Measure.Integral.Density.Algebra
public import Problib.Measure.Necessity.Measurability
public import Problib.Measure.Necessity.Density
public import Problib.Measure.Kernel.RadonNikodym
public import Problib.Measure.Kernel.Finite
public import Problib.Measure.StandardBorel.Countable

set_option autoImplicit false

/-!
# Kernel Radon-Nikodym necessity counterexamples and fixtures

Mechanizes necessity witnesses for kernel Radon-Nikodym selection. Arbitrary choices
of destination-fiber derivatives for a constant probability kernel on indiscrete
`Bool` may fail joint measurability due to choices on a null output point. In
addition, ordinary absolute continuity is not enough for infinite-atom references.
Empty-source selection remains inhabited. Ordinary almost-everywhere uniqueness
also fails for infinite-atom references.
-/

namespace Problib.Measure.Necessity.Kernel.RadonNikodym

open Problib.Real

universe u v

/-- Constant Dirac reference kernel on indiscrete `Bool`. -/
public noncomputable def reference :
    Problib.Measure.Kernel (Space.indiscrete Bool) (Space.discrete Bool) :=
  Problib.Measure.Kernel.const (Space.indiscrete Bool)
    (Measure.dirac (Space.discrete Bool) true)

/-- Candidate bivariate density choosing a nonmeasurable slice on a null output point. -/
public noncomputable def density (input output : Bool) : ENNReal :=
  if output then ENNReal.one else Measurability.function input

/-- Destination-fiber Radon-Nikodym derivative certificate at each input point. -/
public noncomputable def separateDerivative (input : Bool) :
    Measure.RadonNikodymDerivative (reference input) (reference input) where
  density := density input
  density_measurable := fun _ => True.intro
  reconstruct := by
    have equal : (reference input).AEEq (density input) (fun _ => ENNReal.one) := by
      change (Measure.dirac (Space.discrete Bool) true)
        (fun output => ¬density input output = ENNReal.one) = ENNReal.zero
      exact Measure.dirac_apply_of_not_mem (Space.discrete Bool) true True.intro
        (by simp [density])
    change reference input = (reference input).withDensity (density input)
    rw [Measure.withDensity_congr_ae equal, (reference input).withDensity_one]

/-- The candidate bivariate density fails joint measurability. -/
public theorem density_not_jointly_measurable :
    ¬ENNRealMeasurable (Space.product (Space.indiscrete Bool) (Space.discrete Bool))
      (fun pair => density pair.1 pair.2) := by
  intro measurable
  have sliceMap : MeasurableMap (Space.indiscrete Bool)
      (Space.product (Space.indiscrete Bool) (Space.discrete Bool))
      (fun input => (input, false)) :=
    Space.pair_measurable (MeasurableMap.identity _)
      (MeasurableMap.constant _ _ false)
  have restricted := measurable.comp sliceMap
  exact Measurability.function_not_measurable (by simpa only [density, Bool.false_eq_true,
    if_false] using restricted)

/-- Arbitrary choices of destination-fiber derivatives for a probability kernel
can fail joint measurability. The counterexample refutes automatic joint measurability
of arbitrary choices of destination-fiber derivatives, without refuting existence
of some measurable version. -/
public theorem probability_fibers_do_not_validate_separate_choice :
    (∀ input, Measure.IsProbability (reference input)) ∧
      (∀ input, Measure.IsDensity (reference input) (reference input) (density input)) ∧
      ¬ENNRealMeasurable (Space.product (Space.indiscrete Bool) (Space.discrete Bool))
        (fun pair => (separateDerivative pair.1).density pair.2) :=
  ⟨fun _ => Measure.IsProbability.dirac _ _, fun input => (separateDerivative input).reconstruct,
    density_not_jointly_measurable⟩

/-- Ordinary absolute continuity is not enough for kernel derivative existence
under an s-finite reference kernel with an infinite atom. -/
public theorem ordinary_absolute_continuity_insufficient :
    ∃ kernel base : Problib.Measure.Kernel (Space.discrete Unit) (Space.discrete Unit),
      Nonempty (Problib.Measure.Kernel.IsSFinite kernel) ∧
        Nonempty (Problib.Measure.Kernel.IsSFinite base) ∧
        (∀ input, Measure.AbsolutelyContinuous (kernel input) (base input)) ∧
        ¬Nonempty (Problib.Measure.Kernel.RadonNikodymDerivative kernel base) := by
  let kernel := Problib.Measure.Kernel.const (Space.discrete Unit)
    (Measure.dirac (Space.discrete Unit) ())
  let base := Problib.Measure.Kernel.const (Space.discrete Unit) Density.reference
  refine ⟨kernel, base,
    ⟨Problib.Measure.Kernel.IsSFinite.const _
      (Measure.SFinite.ofFinite (Measure.IsFinite.dirac _ _))⟩,
    ⟨Problib.Measure.Kernel.IsSFinite.const _ Density.reference_sFinite⟩,
    fun _ => Density.dirac_absolutelyContinuous, ?_⟩
  rintro ⟨derivative⟩
  exact Density.dirac_has_no_density (derivative.density ()) (derivative.reconstruct ())

/-- Kernel Radon-Nikodym derivative selection over an empty source is inhabited. -/
public noncomputable def empty_source_derivative {β : Type} (target : Space β)
    (kernel base : Problib.Measure.Kernel (Space.discrete Empty) target) :
    Problib.Measure.Kernel.RadonNikodymDerivative kernel base :=
  Problib.Measure.Kernel.RadonNikodymDerivative.ofCountableSource
    (fun input => Empty.elim input) (fun input _ _ => Empty.elim input)
    (fun input => Empty.elim input) (fun input => Empty.elim input)
    (fun input => Empty.elim input)

/-- Ordinary almost-everywhere uniqueness fails for s-finite reference kernels
with infinite atoms. -/
public theorem infinite_reference_does_not_ensure_ae_uniqueness :
    ∃ kernel : Problib.Measure.Kernel (Space.discrete Unit) (Space.discrete Unit),
      Nonempty (Problib.Measure.Kernel.IsSFinite kernel) ∧
        ∃ left right : Problib.Measure.Kernel.RadonNikodymDerivative kernel kernel,
          ¬(∀ input, (kernel input).AEEq (left.density input) (right.density input)) := by
  let kernel := Problib.Measure.Kernel.const (Space.discrete Unit) Density.reference
  let left : Measure.RadonNikodymDerivative Density.reference Density.reference := {
    density := fun _ => ENNReal.one
    density_measurable := ENNRealMeasurable.constant _ _
    reconstruct := (Density.reference_withDensity_nonzero _ ENNReal.one_ne_zero).symm
  }
  let right : Measure.RadonNikodymDerivative Density.reference Density.reference := {
    density := fun _ => Density.two
    density_measurable := ENNRealMeasurable.constant _ _
    reconstruct := (Density.reference_withDensity_nonzero _ Density.two_ne_zero).symm
  }
  refine ⟨kernel, ⟨Problib.Measure.Kernel.IsSFinite.const _ Density.reference_sFinite⟩,
    Problib.Measure.Kernel.RadonNikodymDerivative.const left _,
    Problib.Measure.Kernel.RadonNikodymDerivative.const right _, ?_⟩
  intro equal
  exact Density.densities_not_ae_equal (equal ())

/-- Construction fixture showing that the standard-Borel kernel Radon-Nikodym
constructor succeeds on discrete `Bool` with Dirac fibers.
This contrasts with the failure of arbitrary non-measurable fiber choices. -/
public noncomputable def selected_probability_density :
    Problib.Measure.Kernel.RadonNikodymDerivative reference reference :=
  Problib.Measure.Kernel.RadonNikodymDerivative.ofStandardBorel
    (StandardBorel.ofNatInjection (fun value : Bool => if value then 1 else 0)
      (by intro left right equal; cases left <;> cases right <;> simp_all))
    (Problib.Measure.Kernel.IsSFinite.const _
      (Measure.SFinite.ofFinite (Measure.IsFinite.dirac _ _)))
    (Problib.Measure.Kernel.IsSFinite.const _
      (Measure.SFinite.ofFinite (Measure.IsFinite.dirac _ _)))
    (fun input => Measure.ZeroInfinityAbsolutelyContinuous.refl (reference input))

/-- Standard-Borel destinations do not remove the necessity of zero-infinity
absolute continuity: ordinary absolute continuity remains insufficient for kernel
Radon-Nikodym derivatives even on standard-Borel spaces. -/
public theorem standardBorel_does_not_remove_zero_infinity_premise :
    Nonempty (StandardBorel (Space.discrete Unit)) ∧
      ∃ kernel base : Problib.Measure.Kernel (Space.discrete Unit) (Space.discrete Unit),
        Nonempty (Problib.Measure.Kernel.IsSFinite kernel) ∧
          Nonempty (Problib.Measure.Kernel.IsSFinite base) ∧
          (∀ input, Measure.AbsolutelyContinuous (kernel input) (base input)) ∧
          ¬Nonempty (Problib.Measure.Kernel.RadonNikodymDerivative kernel base) :=
  ⟨⟨StandardBorel.unit⟩, ordinary_absolute_continuity_insufficient⟩

/-- Fixture verifying that the standard-Borel kernel constructor correctly handles
vacuous empty source spaces without carrier nonemptiness assumptions. -/
public noncomputable def standardBorel_empty_source_derivative {β : Type v}
    {target : Space β} (presentation : StandardBorel target)
    (kernel base : Problib.Measure.Kernel (Space.discrete Empty) target) :
    Problib.Measure.Kernel.RadonNikodymDerivative kernel base :=
  Problib.Measure.Kernel.RadonNikodymDerivative.ofStandardBorel presentation
    (Problib.Measure.Kernel.IsSFinite.ofFiniteFibers (fun input => Empty.elim input))
    (Problib.Measure.Kernel.IsSFinite.ofFiniteFibers (fun input => Empty.elim input))
    (fun input => Empty.elim input)

/-- Fixture verifying that the standard-Borel kernel constructor correctly handles
empty target spaces with zero kernels. -/
public noncomputable def standardBorel_empty_target_derivative
    {α : Type u} {β : Type v} (source : Space α) (target : Space β) (empty : ¬Nonempty β) :
    Problib.Measure.Kernel.RadonNikodymDerivative
      (Problib.Measure.Kernel.zero source target) (Problib.Measure.Kernel.zero source target) :=
  Problib.Measure.Kernel.RadonNikodymDerivative.ofStandardBorel (StandardBorel.ofEmpty empty)
    (Problib.Measure.Kernel.IsSFinite.zero source target)
    (Problib.Measure.Kernel.IsSFinite.zero source target)
    (fun _ => Measure.ZeroInfinityAbsolutelyContinuous.refl (Measure.zero target))

/-- Extended nonnegative real density ratios cannot reconstruct finite positive
target mass from incompatible infinite reference mass.
This confirms that factorability cannot be removed. -/
public theorem densityRatio_requires_factorable_infinite_mass :
    ENNReal.mul ENNReal.top (ENNReal.densityRatio ENNReal.one ENNReal.top) ≠ ENNReal.one := by
  rw [ENNReal.densityRatio,
    if_neg (show ENNReal.top ≠ ENNReal.zero from ENNReal.top_ne_finite NNReal.zero), if_pos rfl,
    if_neg ENNReal.one_ne_zero, ENNReal.mul_one]
  exact ENNReal.top_ne_finite NNReal.one

end Problib.Measure.Necessity.Kernel.RadonNikodym
