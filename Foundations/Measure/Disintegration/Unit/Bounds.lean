module

public import Foundations.Measure.Additive.Marginal
public import Foundations.Measure.Decomposition.RadonNikodym.Unit
public import Foundations.Measure.Extended.Unit.Basis
public import Foundations.Measure.Kernel.Distribution.Bounds

set_option autoImplicit false

namespace Foundations.Measure.Measure.UnitDisintegration

open Foundations.Real
open Foundations.Real.Construction
open Foundations.Measure.Real

universe u

variable {beta : Type u} {target : Space beta}

/-- The restricted second marginal of a joint measure evaluated on the product
of an initial interval and a parameter region. -/
@[expose] public noncomputable def initialMarginal
    (joint : Measure (Space.product unitBorel target)) (point : UnitInterval) :
    Measure target :=
  secondMarginal (joint.restrict (Set.preimage Prod.fst (unitInitial point)))

/-- Initial marginal mass equals the joint measure of the product rectangle
formed by the initial interval and the parameter region. -/
public theorem initialMarginal_apply
    (joint : Measure (Space.product unitBorel target)) (point : UnitInterval)
    {region : Set beta} (measurable : target.Measurable region) :
    initialMarginal joint point region = joint (Set.product (unitInitial point) region) := by
  rw [initialMarginal, secondMarginal_apply _ measurable,
    joint.restrict_apply _ (Space.second_measurable unitBorel target measurable)]
  apply congrArg joint
  apply Set.ext
  intro value
  exact ⟨fun member => ⟨member.2, member.1⟩, fun member => ⟨member.2, member.1⟩⟩

/-- Initial marginal mass is bounded above by the second marginal mass of the
parameter region. -/
public theorem initialMarginal_le
    (joint : Measure (Space.product unitBorel target)) (point : UnitInterval)
    (region : Set beta) (measurable : target.Measurable region) :
    ENNReal.le (initialMarginal joint point region) (secondMarginal joint region) := by
  rw [initialMarginal_apply joint point measurable, secondMarginal_apply joint measurable]
  exact joint.mono (fun _ member => member.2)

/-- Initial marginal measure is monotonic in the initial-interval endpoint. -/
public theorem initialMarginal_mono
    (joint : Measure (Space.product unitBorel target)) {left right : UnitInterval}
    (included : Dedekind.le left.val right.val)
    (region : Set beta) (measurable : target.Measurable region) :
    ENNReal.le (initialMarginal joint left region) (initialMarginal joint right region) := by
  rw [initialMarginal_apply joint left measurable, initialMarginal_apply joint right measurable]
  exact joint.mono (fun _ member => ⟨Dedekind.leTrans member.1 included, member.2⟩)

/-- At endpoint one the initial marginal recovers the full second marginal. -/
public theorem initialMarginal_one (joint : Measure (Space.product unitBorel target)) :
    initialMarginal joint unitOne = secondMarginal joint := by
  rw [initialMarginal, unitInitial_one, Set.preimage_univ, restrict_univ]

private noncomputable def bounds (joint : Measure (Space.product unitBorel target))
    (finite : SigmaFinite (secondMarginal joint)) (index : Nat) : beta → UnitInterval :=
  unitDensity finite (initialMarginal_le joint (unitRationalBasis index))

private theorem bounds_measurable (joint : Measure (Space.product unitBorel target))
    (finite : SigmaFinite (secondMarginal joint)) (index : Nat) :
    MeasurableMap target unitBorel (bounds joint finite index) :=
  unitDensity_measurable finite (initialMarginal_le joint (unitRationalBasis index))

/-- The conditional distribution kernel on the unit interval constructed from
distribution upper bounds at countable rational thresholds. -/
public noncomputable def conditional (joint : Measure (Space.product unitBorel target))
    (finite : SigmaFinite (secondMarginal joint)) : Kernel target unitBorel :=
  Kernel.ofDistributionBounds unitRationalBasis (bounds joint finite) (bounds_measurable joint finite)

/-- The conditional distribution kernel is a probability measure on every
parameter fiber. -/
public theorem conditional_isProbability (joint : Measure (Space.product unitBorel target))
    (finite : SigmaFinite (secondMarginal joint)) (input : beta) :
    IsProbability (conditional joint finite input) :=
  Kernel.ofDistributionBounds_isProbability _ _ _ input

/-- The conditional distribution kernel has uniform finite mass bounded by
one. -/
public theorem conditional_isFinite (joint : Measure (Space.product unitBorel target))
    (finite : SigmaFinite (secondMarginal joint)) : Kernel.IsFinite (conditional joint finite) :=
  Kernel.ofDistributionBounds_isFinite _ _ _

/-- Integrated conditional initial-interval mass is bounded above by the initial
marginal at any strictly greater rational basis threshold. -/
public theorem conditional_initial_le
    (joint : Measure (Space.product unitBorel target))
    (finite : SigmaFinite (secondMarginal joint)) (point : UnitInterval) (index : Nat)
    (active : Dedekind.lt point.val (unitRationalBasis index).val)
    {region : Set beta} (measurable : target.Measurable region) :
    ENNReal.le (lintegral ((secondMarginal joint).restrict region)
      (fun input => conditional joint finite input (unitInitial point)))
      (initialMarginal joint (unitRationalBasis index) region) := by
  rw [(unitDensity_reconstruct finite
    (initialMarginal_le joint (unitRationalBasis index))).apply measurable]
  exact lintegral_mono _ (fun input => Kernel.ofDistributionBounds_initial_le
    unitRationalBasis (bounds joint finite) (bounds_measurable joint finite) input point index active)

/-- Initial marginal mass is bounded above by the integrated conditional
initial-interval mass through countable almost-everywhere density ordering. -/
public theorem le_conditional_initial
    (joint : Measure (Space.product unitBorel target))
    (finite : SigmaFinite (secondMarginal joint)) (point : UnitInterval)
    {region : Set beta} (measurable : target.Measurable region) :
    ENNReal.le (initialMarginal joint point region)
      (lintegral ((secondMarginal joint).restrict region)
        (fun input => conditional joint finite input (unitInitial point))) := by
  have simultaneous : (secondMarginal joint).AE (fun input => ∀ index,
      Dedekind.lt point.val (unitRationalBasis index).val →
        Dedekind.le (unitDensity finite (initialMarginal_le joint point) input).val
          (bounds joint finite index input).val) := by
    apply ae_all_iff.mpr
    intro index
    classical
    by_cases active : Dedekind.lt point.val (unitRationalBasis index).val
    · exact (unitDensity_ae_mono finite (initialMarginal_le joint point)
        (initialMarginal_le joint (unitRationalBasis index))
        (initialMarginal_mono joint active.1)).mono (fun _ bound _ => bound)
    · exact ae_of_forall (fun _ impossible => False.elim (active impossible))
  rw [(unitDensity_reconstruct finite (initialMarginal_le joint point)).apply measurable]
  apply lintegral_mono_ae
  apply (simultaneous.restrict region).mono
  intro input bounded
  change ENNReal.le (ENNReal.ofReal (unitDensity finite (initialMarginal_le joint point) input).val)
    (Kernel.ofDistributionBounds unitRationalBasis (bounds joint finite)
      (bounds_measurable joint finite) input (unitInitial point))
  rw [Kernel.ofDistributionBounds_initial]
  exact ENNReal.ofRealMonotone (DistributionFunction.le_ofUpperBounds unitRationalBasis
    (fun index => bounds joint finite index input) point
    (unitDensity finite (initialMarginal_le joint point) input) bounded)

end Foundations.Measure.Measure.UnitDisintegration
