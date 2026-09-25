module

public import Problib.Measure.Kernel.Finite
public import Problib.Measure.Kernel.Composition
import Problib.Measure.Integral.Density.Algebra
import Problib.Measure.Integral.Density.Change
import Problib.Measure.Integral.Lebesgue.Measure
import Problib.Measure.Integral.Lebesgue.Transport
import Problib.Real.Series.Error

set_option autoImplicit false

open Problib.Real Problib.Measure
open Problib.Real.Construction

namespace Problib.Measure.Necessity.Kernel.Composition

private noncomputable def weights : Nat → ENNReal :=
  Classical.choose (ENNReal.exists_positive_summable_error ENNReal.one True.intro ENNReal.one_positive)

private theorem weights_positive (index : Nat) : ENNReal.lt ENNReal.zero (weights index) :=
  (Classical.choose_spec
    (ENNReal.exists_positive_summable_error ENNReal.one True.intro ENNReal.one_positive)).1 index

private theorem weights_bound : ENNReal.le (ENNReal.tsum weights) ENNReal.one :=
  (Classical.choose_spec
    (ENNReal.exists_positive_summable_error ENNReal.one True.intro ENNReal.one_positive)).2

private theorem weights_finite (index : Nat) : ENNReal.Finite (weights index) :=
  ENNReal.finite_of_le (ENNReal.le_trans (ENNReal.term_le_tsum weights index) weights_bound) True.intro

private noncomputable def reciprocal (index : Nat) : ENNReal :=
  ENNReal.ofReal (Dedekind.inverse (ENNReal.toReal (weights index)))

private theorem reciprocal_finite (index : Nat) : ENNReal.Finite (reciprocal index) :=
  ENNReal.ofReal_finite _

private theorem cancellation (index : Nat) :
    ENNReal.mul (weights index) (reciprocal index) = ENNReal.one := by
  rcases ENNReal.exists_finite_of_finite (weights_finite index) with ⟨value, equal⟩
  have positive := weights_positive index
  rw [equal] at positive
  change Dedekind.lt Dedekind.zero (NNReal.toReal value) at positive
  rw [reciprocal, equal]
  change ENNReal.finite (NNReal.mul value
    (NNReal.ofReal (Dedekind.inverse (NNReal.toReal value)))) = ENNReal.finite NNReal.one
  apply congrArg ENNReal.finite
  apply NNReal.ext
  rw [NNReal.toReal_mul, NNReal.toReal_ofReal
    (Dedekind.inverse_of_positive_positive positive).1, NNReal.toReal_one]
  exact Dedekind.mul_inverse_cancel_of_positive positive

private noncomputable def atoms (index : Nat) : Measure (Space.discrete Nat) :=
  Measure.smul (weights index) (Measure.dirac (Space.discrete Nat) index)

private noncomputable def reference : Measure (Space.discrete Nat) := Measure.sum atoms

private theorem reference_mass : reference Set.univ = ENNReal.tsum weights := by
  rw [reference, Measure.sum_apply _ (Space.discrete Nat).univ]
  apply congrArg ENNReal.tsum
  funext index
  change Measure.smul (weights index) (Measure.dirac (Space.discrete Nat) index) Set.univ = _
  rw [Measure.smul_apply_measurable _ _ (Space.discrete Nat).univ,
    Measure.dirac_apply_univ, ENNReal.mul_one]

private theorem reference_finite : Measure.IsFinite reference := by
  constructor
  rw [reference_mass]
  exact ENNReal.finite_of_le weights_bound True.intro

/-- Uniformly finite constant kernel on discrete `Unit` targeting discrete
`Nat`. -/
public noncomputable def first : Kernel (Space.discrete Unit) (Space.discrete Nat) :=
  Kernel.const _ reference

/-- Prove that `first` is uniformly finite. -/
public theorem first_finite : Kernel.IsFinite first :=
  Kernel.IsFinite.const _ reference_finite

/-- Measurable kernel on discrete `Nat` with finite individual fibers scaled by
reciprocal weights. -/
public noncomputable def second : Kernel (Space.discrete Nat) (Space.discrete Unit) where
  toFun index := Measure.smul (reciprocal index) (Measure.dirac (Space.discrete Unit) ())
  measurable := by
    intro set setMeasurable threshold
    exact True.intro

/-- Prove that every individual fiber measure of `second` is finite. -/
public theorem second_fibers_finite (index : Nat) : Measure.IsFinite (second index) :=
  Measure.IsFinite.smul (reciprocal index) (reciprocal_finite index)
    (Measure.IsFinite.dirac (Space.discrete Unit) ())

private theorem second_mass (index : Nat) : second index Set.univ = reciprocal index := by
  change Measure.smul (reciprocal index) (Measure.dirac (Space.discrete Unit) ()) Set.univ = _
  rw [Measure.smul_apply_measurable _ _ (Space.discrete Unit).univ,
    Measure.dirac_apply_univ, ENNReal.mul_one]

private theorem atom_integral (index : Nat) : lintegral (atoms index) reciprocal = ENNReal.one := by
  change lintegral (Measure.smul (weights index)
    (Measure.dirac (Space.discrete Nat) index)) reciprocal = _
  rw [← Measure.withDensity_const]
  rw [lintegral_withDensity _ (ENNRealMeasurable.constant _ _) (by
    intro threshold
    exact True.intro)]
  rw [lintegral_dirac _ _ (by intro threshold; exact True.intro)]
  exact cancellation index

private theorem reference_integral : lintegral reference reciprocal = ENNReal.top := by
  change lintegral (Measure.sum atoms) reciprocal = _
  rw [lintegral_sum_measure]
  have equal : (fun index => lintegral (atoms index) reciprocal) =
      (fun _ => ENNReal.one) := funext atom_integral
  rw [equal, ENNReal.tsum_const_of_ne_zero ENNReal.one_ne_zero]

/-- Prove that the composite kernel `first.comp second` assigns infinite total
mass at every input. -/
public theorem composition_mass (input : Unit) :
    first.comp second input Set.univ = ENNReal.top := by
  rw [Kernel.comp_apply, Measure.bind_apply _ _ (Space.discrete Unit).univ]
  change lintegral reference (fun index => second index Set.univ) = _
  rw [funext second_mass]
  exact reference_integral

/-- Refute universal closure of finite individual fibers under kernel
composition. -/
public theorem composition_not_finite_fibers :
    ¬(∀ input, Measure.IsFinite (first.comp second input)) := by
  intro finite
  have impossible := (finite ()).univ_finite
  rw [composition_mass] at impossible
  exact impossible

/-- Construct an s-finite certificate for the composite kernel
`first.comp second`. -/
public noncomputable def composition_sFinite : Kernel.IsSFinite (first.comp second) :=
  first_finite.toSFinite.comp (Kernel.IsSFinite.ofFiniteFibers second_fibers_finite)

end Problib.Measure.Necessity.Kernel.Composition
