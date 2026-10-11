module

public import Problib.Measure.Uniform
public import Problib.Measure.Real.Moment
public import Problib.Measure.Integral.Real.Nonnegative

set_option autoImplicit false

/-! The mean of the uniform law on the unit interval is one half. It is the
first moment of Lebesgue volume on (0, 1], read through the inclusion of the
unit interval, since the closed and half-open intervals differ only at a null
endpoint. -/

namespace Problib.Measure.Real

open Problib.Real
open Problib.Real.Construction.Dedekind

/-- A closed and a half-open interval differ only at their null lower endpoint. -/
public theorem icc_aeEq_ioc (a b : Carrier) : volume.AEEq (Icc a b) (Ioc a b) := by
  apply Measure.NullSet.mono (show volume.NullSet (Set.singleton a) from volume_singleton a)
  intro x differs
  change x = a
  apply Classical.byContradiction
  intro unequal
  apply differs
  apply propext
  constructor
  · intro member
    exact ⟨⟨member.1, fun reverse => unequal (le_antisymm reverse member.1)⟩, member.2⟩
  · intro member
    exact ⟨member.1.1, member.2⟩

/-- The lower integral of the identity under the uniform law is one half. -/
public theorem uniform01_lintegral_ofReal :
    lintegral uniform01 (fun point => ENNReal.ofReal point.val) =
      ENNReal.ofReal (div one (selection.ofRat 2)) := by
  have mapped := lintegral_map uniform01 unitInclusion unitInclusion_measurable
    ofReal_measurable
  rw [uniform01_map_unitInclusion] at mapped
  refine mapped.symm.trans ?_
  rw [restrictedUnit, unitSet, Measure.restrict_congr_ae (icc_aeEq_ioc zero one),
    first_moment one one_nonnegative, mul_one]

/-- The uniform law on the unit interval has mean one half. -/
public theorem uniform01_mean :
    HasRealIntegral uniform01 (fun point => point.val) (div one (selection.ofRat 2)) := by
  refine HasRealIntegral.of_lintegral_ofReal unitInclusion_measurable
    (fun point => point.property.1) ?_ uniform01_lintegral_ofReal
  exact le_of_lt (div_positive one_positive ofRat_two_positive)

end Problib.Measure.Real
