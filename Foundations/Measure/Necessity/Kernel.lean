module

public import Foundations.Measure.Necessity.Kernel.Finite
public import Foundations.Measure.Necessity.Kernel.Composition
public import Foundations.Measure.Kernel.Distribution
public import Foundations.Measure.Distribution.Example

set_option autoImplicit false

namespace Foundations.Measure.Necessity.Kernel

open Foundations.Real
open Foundations.Real.Construction
open Foundations.Measure.Real

/-- Distribution family on `Bool` switching between uniform identity and a
Dirac mass located at zero. -/
@[expose] public noncomputable def switchFamily : Bool → DistributionFunction
  | false => DistributionFunction.identity
  | true => DistributionFunction.atomZero

/-- No measurable kernel over indiscrete `Bool` can reproduce `switchFamily`
initial values. -/
public theorem switchFamily_no_kernel
    (candidate : Kernel (Space.indiscrete Bool) unitBorel)
    (initials : ∀ input point, candidate input (unitInitial point) =
      ENNReal.ofReal ((switchFamily input).function point).val) : False := by
  let zeroRegion := Set.preimage (fun input => candidate input (unitInitial unitZero))
    (ennrealIic ENNReal.zero)
  have regionMeasurable : (Space.indiscrete Bool).Measurable zeroRegion :=
    (candidate.measurable (unitInitialMeasurable unitZero)).iic ENNReal.zero
  have zeroMember : zeroRegion false := by
    change ENNReal.le (candidate false (unitInitial unitZero)) ENNReal.zero
    rw [initials]
    change ENNReal.le (ENNReal.ofReal Dedekind.zero) ENNReal.zero
    rw [ENNReal.ofRealZero]
    exact ENNReal.leRefl _
  have oneAbsent : ¬zeroRegion true := by
    intro included
    change ENNReal.le (candidate true (unitInitial unitZero)) ENNReal.zero at included
    rw [initials] at included
    change ENNReal.le (ENNReal.ofReal Dedekind.one) ENNReal.zero at included
    rw [show ENNReal.ofReal Dedekind.one = ENNReal.one from
      ENNReal.ofRealToRealFinite NNReal.one] at included
    exact ENNReal.oneNeZero (ENNReal.eqZeroOfLeZero included)
  rcases (Space.indiscrete_measurable_iff zeroRegion).mp regionMeasurable with empty | whole
  · rw [empty] at zeroMember
    exact zeroMember
  · apply oneAbsent
    rw [whole]
    exact True.intro

/-- Probability kernel on discrete `Bool` with continuous uniform fiber at
`false` and Dirac fiber at `true`. -/
@[expose] public noncomputable def switchKernel : Kernel (Space.discrete Bool) unitBorel :=
  Foundations.Measure.Kernel.ofDistributionFunction switchFamily
    (fun _ => MeasurableMap.fromDiscrete _ _)

public theorem switchKernel_false : switchKernel false = uniform01 :=
  DistributionFunction.identity_measure

public theorem switchKernel_true :
    switchKernel true = Measure.dirac unitBorel unitZero :=
  DistributionFunction.atomZero_measure

end Foundations.Measure.Necessity.Kernel
