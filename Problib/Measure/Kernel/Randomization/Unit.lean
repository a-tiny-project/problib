module

public import Problib.Measure.Kernel.Randomization.Basic
public import Problib.Measure.Distribution.Bounds.Measurable
public import Problib.Measure.Distribution.Joint
public import Problib.Measure.Distribution.Uniqueness
public import Problib.Measure.Extended.Unit.Basis
public import Problib.Measure.Real.Continuity

set_option autoImplicit false

namespace Problib.Measure.Kernel.Randomizer

open Problib.Measure.Real Problib.Real Problib.Real.Construction

universe u

public section

variable {alpha : Type u} {source : Space alpha}

namespace Unit

/-- Clamps kernel masses of rational initial intervals to the unit interval. -/
@[expose] noncomputable def bounds (kernel : Kernel source unitBorel) (index : Nat) (input : alpha) : UnitInterval :=
  unitClamp (kernel input (unitInitial (unitRationalBasis index)))

/-- Rational interval mass bounds are measurable functions of the parameter. -/
theorem bounds_measurable (kernel : Kernel source unitBorel) (index : Nat) :
    MeasurableMap source unitBorel (bounds kernel index) :=
  MeasurableMap.comp unitClamp_measurable
    (kernel.measurable (unitInitial_measurable (unitRationalBasis index))).measurableMap

/-- Reconstructs a cumulative distribution function on the unit interval from rational bounds. -/
@[expose] noncomputable def distribution (kernel : Kernel source unitBorel) (input : alpha) : DistributionFunction :=
  DistributionFunction.ofUpperBounds unitRationalBasis (fun index => bounds kernel index input)

/-- Distribution function slices are measurable functions of the parameter. -/
theorem distribution_slices (kernel : Kernel source unitBorel) (point : UnitInterval) :
    MeasurableMap source unitBorel (fun input => (distribution kernel input).function point) :=
  DistributionFunction.ofUpperBounds_measurable unitRationalBasis (bounds kernel) (bounds_measurable kernel) point

/-- Under normalization of every fiber, the induced distribution measure equals the kernel fiber. -/
theorem distribution_measure (kernel : Kernel source unitBorel)
    (normalized : ∀ input, Measure.IsProbability (kernel input)) (input : alpha) :
    (distribution kernel input).measure = kernel input := by
  apply finite_measure_ext_unitInitial (distribution kernel input).measure_isProbability.to_finite
    (normalized input).to_finite
  intro point
  apply ENNReal.le_antisymm
  · apply le_measure_unitInitial_of_right_dense (normalized input).to_finite unitRationalBasis
      (fun _ _ less => by
        rcases exists_unitRationalBasis_between less with ⟨index, above, below⟩
        exact ⟨index, above, below.1⟩) point
    · rw [(normalized input).univ_eq_one]
      exact (distribution kernel input).measure_isProbability.apply_le_one _
    · intro index active
      rw [DistributionFunction.measure_initial]
      have below := DistributionFunction.ofUpperBounds_le unitRationalBasis
        (fun index => bounds kernel index input) point index active
      have embedded := ENNReal.ofReal_monotone below
      change ENNReal.le _ (ENNReal.ofReal (unitClamp
        (kernel input (unitInitial (unitRationalBasis index)))).val) at embedded
      rw [ofReal_unitClamp_of_le ((normalized input).apply_le_one _)] at embedded
      exact embedded
  · rw [DistributionFunction.measure_initial]
    have below := DistributionFunction.le_ofUpperBounds unitRationalBasis
      (fun index => bounds kernel index input) point (unitClamp (kernel input (unitInitial point)))
      (fun index active => unitClamp_mono (kernel input |>.mono
        (fun _ included => Dedekind.le_trans included active.1)))
    have embedded := ENNReal.ofReal_monotone below
    rw [ofReal_unitClamp_of_le ((normalized input).apply_le_one _)] at embedded
    exact embedded

/-- Quantile decoder mapping a parameter and Uniform seed to the unit interval. -/
@[expose] noncomputable def decoder (kernel : Kernel source unitBorel) (pair : alpha × UnitInterval) : UnitInterval :=
  (distribution kernel pair.1).quantile pair.2

/-- The quantile decoder is jointly measurable on the product of parameter and unit-Borel spaces. -/
theorem decoder_measurable (kernel : Kernel source unitBorel) :
    MeasurableMap (Space.product source unitBorel) unitBorel (decoder kernel) :=
  DistributionFunction.quantile_jointly_measurable (distribution kernel) (distribution_slices kernel)

/-- Pushforward of the Uniform measure along the quantile decoder recovers the normalized kernel fiber. -/
theorem decoder_law (kernel : Kernel source unitBorel)
    (normalized : ∀ input, Measure.IsProbability (kernel input)) (input : alpha) :
    uniform01.map (fun seed => decoder kernel (input, seed))
      (distribution kernel input).quantile_measurable = kernel input :=
  distribution_measure kernel normalized input

end Unit

/-- Constructs an exact Uniform randomizer for any probability kernel into the Borel unit interval. -/
@[expose] noncomputable def ofUnitInterval (kernel : Kernel source unitBorel)
    (normalized : ∀ input, Measure.IsProbability (kernel input)) : Randomizer kernel where
  function := Unit.decoder kernel
  measurable := Unit.decoder_measurable kernel
  law := Unit.decoder_law kernel normalized

end

end Problib.Measure.Kernel.Randomizer
