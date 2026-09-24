module

public import Problib.Measure.Kernel.Generator
public import Problib.Measure.Distribution.Uniqueness
public import Problib.Measure.Extended.Conversion

set_option autoImplicit false

namespace Problib.Measure.Kernel

open Problib.Real
open Problib.Measure.Real

universe u
variable {α : Type u} {source : Space α}

/-- Construct a measurable probability kernel on `unitBorel` from
parameter-indexed distribution functions with measurable parameter slices. -/
@[expose] public noncomputable def ofDistributionFunction (family : α → DistributionFunction)
    (slices : ∀ point, MeasurableMap source unitBorel
      (fun input => (family input).function point)) : Kernel source unitBorel :=
  ofGenerator (fun input => (family input).measure)
    (fun input => (family input).measure_isProbability.to_finite)
    (by
      have same : (fun input => (family input).measure Set.univ) = (fun _ => ENNReal.one) :=
        funext fun input => (family input).measure_isProbability.univ_eq_one
      rw [same]
      exact ENNRealMeasurable.constant source ENNReal.one)
    unitInitials unitBorel_generated_initials unitInitials_pi
    (by
      rintro initial ⟨point, rfl⟩
      have same : (fun input => (family input).measure (unitInitial point)) =
          (fun input => ENNReal.ofReal ((family input).function point).val) :=
        funext fun input => (family input).measure_initial point
      rw [same]
      exact ofReal_measurable.comp (MeasurableMap.comp unitInclusion_measurable (slices point)))

@[simp] public theorem ofDistributionFunction_apply (family : α → DistributionFunction)
    (slices : ∀ point, MeasurableMap source unitBorel
      (fun input => (family input).function point)) (input : α) :
    ofDistributionFunction family slices input = (family input).measure := rfl

public theorem ofDistributionFunction_isProbability (family : α → DistributionFunction)
    (slices : ∀ point, MeasurableMap source unitBorel
      (fun input => (family input).function point)) (input : α) :
    Measure.IsProbability (ofDistributionFunction family slices input) :=
  (family input).measure_isProbability

public theorem ofDistributionFunction_initial (family : α → DistributionFunction)
    (slices : ∀ point, MeasurableMap source unitBorel
      (fun input => (family input).function point)) (input : α) (point : UnitInterval) :
    ofDistributionFunction family slices input (unitInitial point) =
      ENNReal.ofReal ((family input).function point).val :=
  (family input).measure_initial point

/-- The constructed distribution kernel is uniformly finite with common bound
one. -/
public theorem ofDistributionFunction_isFinite (family : α → DistributionFunction)
    (slices : ∀ point, MeasurableMap source unitBorel
      (fun input => (family input).function point)) :
    IsFinite (ofDistributionFunction family slices) := by
  refine ⟨⟨ENNReal.one, True.intro, ?_⟩⟩
  intro input
  rw [(ofDistributionFunction_isProbability family slices input).univ_eq_one]
  exact ENNReal.le_refl _

/-- Any competing kernel agreeing on initial intervals equals
`ofDistributionFunction`. -/
public theorem ofDistributionFunction_unique (family : α → DistributionFunction)
    (slices : ∀ point, MeasurableMap source unitBorel
      (fun input => (family input).function point))
    (competitor : Kernel source unitBorel)
    (initials : ∀ input point, competitor input (unitInitial point) =
      ENNReal.ofReal ((family input).function point).val) :
    competitor = ofDistributionFunction family slices := by
  apply Kernel.ext
  intro input
  exact (family input).measure_unique (initials input)

end Problib.Measure.Kernel
