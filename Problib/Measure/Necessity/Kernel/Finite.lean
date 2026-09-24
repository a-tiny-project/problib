module

public import Problib.Measure.Kernel.Finite

set_option autoImplicit false

namespace Problib.Measure.Necessity.Kernel

open Problib.Real

/-- Kernel on discrete `Nat` with finite fibers that lacks any uniform finite
bound across inputs. -/
@[expose] public noncomputable def unbounded : Kernel (Space.discrete Nat) (Space.discrete Unit) where
  toFun index := Measure.smul (ENNReal.rationalBasis index)
    (Measure.dirac (Space.discrete Unit) ())
  measurable := by
    intro set setMeasurable threshold
    exact True.intro

/-- Every individual fiber measure of `unbounded` is finite. -/
public theorem unbounded_fibers_finite (index : Nat) : Measure.IsFinite (unbounded index) :=
  Measure.IsFinite.smul (ENNReal.rationalBasis index) (ENNReal.rationalBasis_finite index)
    (Measure.IsFinite.dirac (Space.discrete Unit) ())

/-- Total mass of `unbounded` at each input equals the corresponding rational
basis value. -/
public theorem unbounded_mass (index : Nat) :
    unbounded index Set.univ = ENNReal.rationalBasis index := by
  change Measure.smul (ENNReal.rationalBasis index)
    (Measure.dirac (Space.discrete Unit) ()) Set.univ = _
  rw [Measure.smul_apply_measurable _ _ (Space.discrete Unit).univ,
    Measure.dirac_apply_univ, ENNReal.mul_one]

/-- Refute existence of a common finite bound across all inputs for
`unbounded`. -/
public theorem unbounded_not_finite : ¬Kernel.IsFinite unbounded := by
  rintro ⟨bound, finite, bounded⟩
  have below : ENNReal.lt bound ENNReal.top :=
    ⟨ENNReal.le_top _, fun reverse =>
      (ENNReal.finite_iff_ne_top.mp finite) (ENNReal.top_le_iff.mp reverse)⟩
  rcases ENNReal.exists_rationalBasis_between below with ⟨index, above, _⟩
  have contradiction := bounded index
  rw [unbounded_mass] at contradiction
  exact above.2 contradiction

/-- Construct an s-finite certificate for `unbounded` through `ofFiniteFibers`. -/
public noncomputable def unbounded_sFinite : Kernel.IsSFinite unbounded :=
  Problib.Measure.Kernel.IsSFinite.ofFiniteFibers unbounded_fibers_finite

end Problib.Measure.Necessity.Kernel
