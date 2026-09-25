module

public import Problib.Inference.Sequential
set_option autoImplicit false

/-! Necessity for sequential stages.

`SeqRN` alone constrains support: the target is absolutely continuous against
the source bound through the proposal (`seq_rn_absolutely_continuous`). These
examples show the constraint is real and the only one. Identity propagation
cannot move a point mass to another point, whatever the increment
(`identity_seq_rn_absurd`). A proposal that moves the mass there can, with
weight one (`constant_seq_rn`). A zero source forces a zero target
(`seq_rn_zero_source`). -/

namespace Problib.Inference.Necessity.Sequential

open Problib.Real Problib.Measure

public section

/-- Booleans with every set measurable. -/
abbrev bools : Space Bool := Space.discrete Bool

/-- Every extended-valued function on a discrete space is measurable. -/
theorem discrete_ennrealMeasurable {α : Type} (function : α → ENNReal) :
    ENNRealMeasurable (Space.discrete α) function :=
  fun _ => True.intro

/-- The indicator of `true`. -/
@[expose] noncomputable def atTrue (value : Bool) : ENNReal := if value then ENNReal.one else ENNReal.zero

/-- Identity propagation cannot carry δ_false to δ_true for any increment. At
the indicator of `{true}`, the left side is `ω(false, false) · 0` and the right
side is one. -/
theorem identity_seq_rn_absurd (increment : Bool × Bool → NNReal) :
    ¬SeqRN (Measure.dirac bools false) (Measure.dirac bools true)
      (Kernel.deterministic (fun value => value) (MeasurableMap.identity bools)) increment := by
  intro rn
  have equation := rn atTrue (discrete_ennrealMeasurable atTrue)
  rw [lintegral_dirac bools false (discrete_ennrealMeasurable _), Kernel.deterministic_apply,
    lintegral_dirac bools false (discrete_ennrealMeasurable _),
    lintegral_dirac bools true (discrete_ennrealMeasurable _)] at equation
  change ENNReal.mul (ENNReal.finite (increment (false, false))) ENNReal.zero = ENNReal.one
    at equation
  rw [ENNReal.mul_zero] at equation
  exact ENNReal.one_ne_zero equation.symm

/-- A proposal that always draws `true`, with weight one, carries δ_false to
δ_true. -/
theorem constant_seq_rn :
    SeqRN (Measure.dirac bools false) (Measure.dirac bools true)
      (Kernel.const bools (Measure.dirac bools true)) (fun _ => NNReal.one) := by
  intro function measurable
  rw [lintegral_dirac bools false (discrete_ennrealMeasurable _), Kernel.const_apply,
    lintegral_dirac bools true (discrete_ennrealMeasurable _),
    lintegral_dirac bools true measurable]
  exact ENNReal.one_mul (function true)

/-- A zero source forces a zero target, whatever the proposal and increment. -/
theorem seq_rn_zero_source {α β : Type} {space : Space α} {result : Space β}
    {target : Measure result} {proposal : Kernel space result} {increment : α × β → NNReal}
    (rn : SeqRN (Measure.zero space) target proposal increment) :
    target = Measure.zero result := by
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  rw [← rn function measurable, lintegral_zero_measure, lintegral_zero_measure]

end

end Problib.Inference.Necessity.Sequential
