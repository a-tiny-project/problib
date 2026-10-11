import Problib.Inference.Sequential.Flow
import Problib.Inference.Necessity.Weighting

set_option autoImplicit false

/-! Finite witnesses for Feynman–Kac flows. A fair Boolean draw weighed by `1` or `2`, then a flip
weighed by `3` or `1` on its output, induces mass `3` at `false` and `1/2` at `true`, so its
evidence is `7/2`. A zero potential gives the zero measure before an infinite one. A potential read
at the input of a flip and the same potential read at its output give different masses. -/

namespace Problib.Inference.FeynmanKac.Witnesses

open Problib.Real Problib.Measure Problib.Inference
open Problib.Inference.Necessity.Weighting

section

/-- A weight read from a Boolean. -/
noncomputable def weight (low high : Rat) (lowNonnegative : 0 ≤ low) (highNonnegative : 0 ≤ high)
    (value : Bool) : ENNReal :=
  if value then ENNReal.ofRat high highNonnegative else ENNReal.ofRat low lowNonnegative

/-- Flip a Boolean and weigh the pair by `potential`. -/
noncomputable def flip (potential : Bool × Bool → ENNReal)
    (measurable : ENNRealMeasurable (Space.product bools bools) potential) : Stage bools bools where
  proposal := Kernel.deterministic not (MeasurableMap.from_discrete bools not)
  proposalFinite := Kernel.IsSFinite.deterministic not (MeasurableMap.from_discrete bools not)
  potential := potential
  potentialMeasurable := measurable

/-- A flip weighed at its output. -/
noncomputable def flipOut (reading : Bool → ENNReal) : Stage bools bools :=
  flip (fun pair => reading pair.2)
    ((ENNRealMeasurable.from_discrete reading).comp (Space.second_measurable bools bools))

/-- A flip weighed at its input. -/
noncomputable def flipIn (reading : Bool → ENNReal) : Stage bools bools :=
  flip (fun pair => reading pair.1)
    ((ENNRealMeasurable.from_discrete reading).comp (Space.first_measurable bools bools))

/-- A fair Boolean draw from the one point, weighed `1` at `false` and `2` at `true`. -/
noncomputable def draw : Stage point bools where
  proposal := Kernel.const point (fair bools false true)
  proposalFinite := Kernel.IsSFinite.ofMarkov fun _ => fair_probability bools false true
  potential := fun pair => weight 1 2 (by decide +kernel) (by decide +kernel) pair.2
  potentialMeasurable :=
    (ENNRealMeasurable.from_discrete _).comp (Space.second_measurable point bools)

/-- The draw, then a flip weighed `3` at `false` and `1` at `true`: three spaces, two distinct. -/
noncomputable def twoStage : Flow point bools :=
  Flow.stage draw (Flow.stage (flipOut (weight 3 1 (by decide +kernel) (by decide +kernel)))
    (Flow.empty bools))

theorem flip_test (potential : Bool × Bool → ENNReal)
    (measurable : ENNRealMeasurable (Space.product bools bools) potential) (input : Bool)
    (function : Bool → ENNReal) :
    lintegral ((Flow.stage (flip potential measurable) (Flow.empty bools)).induced
        (Measure.dirac bools input)) function =
      ENNReal.mul (potential (input, !input)) (function (!input)) := by
  rw [Flow.lintegral_induced _ _ (ENNRealMeasurable.from_discrete function),
    lintegral_dirac bools input (ENNRealMeasurable.from_discrete _)]
  show lintegral (Measure.dirac bools (!input))
    (fun output => ENNReal.mul (potential (input, output)) (function output)) = _
  rw [lintegral_dirac bools (!input) (ENNRealMeasurable.from_discrete _)]

/-- The convention is observable: from `false`, a flip weighed at its output reads the weight at
`true`, and weighed at its input reads it at `false`. -/
theorem flipOut_test (reading function : Bool → ENNReal) :
    lintegral ((Flow.stage (flipOut reading) (Flow.empty bools)).induced
      (Measure.dirac bools false)) function = ENNReal.mul (reading true) (function true) :=
  flip_test _ _ false function

theorem flipIn_test (reading function : Bool → ENNReal) :
    lintegral ((Flow.stage (flipIn reading) (Flow.empty bools)).induced
      (Measure.dirac bools false)) function = ENNReal.mul (reading false) (function true) :=
  flip_test _ _ false function

/-- The empty flow keeps the mass of its initial measure. -/
theorem empty_evidence : (Flow.empty bools).evidence (fair bools false true) = ENNReal.one :=
  (fair_probability bools false true).univ_eq_one

/-- A zero potential gives the zero measure, though the next is infinite. -/
theorem zero_then_top (initial : Measure bools) :
    (Flow.stage (flipOut fun _ => ENNReal.zero)
      (Flow.stage (flipOut fun _ => ENNReal.top) (Flow.empty bools))).induced initial =
        Measure.zero bools :=
  Flow.induced_zero_stage _ _ (fun _ => rfl) initial

/-- Every test against the two-stage flow, before any arithmetic. -/
theorem twoStage_test (function : Bool → ENNReal) :
    lintegral (twoStage.induced (Measure.dirac point ())) function =
      ENNReal.mul halfMass (ENNReal.add
        (ENNReal.mul (ENNReal.ofRat 1 (by decide +kernel))
          (ENNReal.mul (ENNReal.ofRat 1 (by decide +kernel)) (function true)))
        (ENNReal.mul (ENNReal.ofRat 2 (by decide +kernel))
          (ENNReal.mul (ENNReal.ofRat 3 (by decide +kernel)) (function false)))) := by
  rw [Flow.lintegral_induced _ _ (ENNRealMeasurable.from_discrete function),
    lintegral_dirac point () (ENNRealMeasurable.from_discrete _)]
  show lintegral (fair bools false true) (fun drawn => ENNReal.mul (draw.potential ((), drawn))
    (lintegral (Measure.dirac bools (!drawn)) (fun output => ENNReal.mul
      (weight 3 1 (by decide +kernel) (by decide +kernel) output) (function output)))) = _
  rw [lintegral_fair bools false true (ENNRealMeasurable.from_discrete _),
    lintegral_dirac bools (!false) (ENNRealMeasurable.from_discrete _),
    lintegral_dirac bools (!true) (ENNRealMeasurable.from_discrete _)]
  rfl

/-- The terminal mass at `false` is `3`. -/
theorem twoStage_false : lintegral (twoStage.induced (Measure.dirac point ()))
    (fun value => bif value then ENNReal.zero else ENNReal.one) =
      ENNReal.ofRat 3 (by decide +kernel) := by
  rw [twoStage_test, Bool.cond_true, Bool.cond_false, ENNReal.mul_zero, ENNReal.mul_zero,
    ENNReal.zero_add, ENNReal.mul_one,
    ← ENNReal.ofRat_mul 2 3 (by decide +kernel) (by decide +kernel)]
  exact half_ofRat (2 * 3) 3 _ _ (by decide +kernel)

/-- The terminal mass at `true` is `1/2`. -/
theorem twoStage_true : lintegral (twoStage.induced (Measure.dirac point ()))
    (fun value => bif value then ENNReal.one else ENNReal.zero) =
      ENNReal.ofRat (1 / 2) (by decide +kernel) := by
  rw [twoStage_test, Bool.cond_true, Bool.cond_false, ENNReal.mul_zero, ENNReal.mul_zero,
    ENNReal.add_zero, ENNReal.mul_one,
    ← ENNReal.ofRat_mul 1 1 (by decide +kernel) (by decide +kernel)]
  exact half_ofRat (1 * 1) (1 / 2) _ _ (by decide +kernel)

/-- The evidence is `7/2`. -/
theorem twoStage_evidence : twoStage.evidence (Measure.dirac point ()) =
    ENNReal.ofRat (7 / 2) (by decide +kernel) := by
  have total := lintegral_const (twoStage.induced (Measure.dirac point ())) ENNReal.one
  rw [ENNReal.one_mul, twoStage_test] at total
  rw [Flow.evidence, ← total, ENNReal.mul_one, ENNReal.mul_one,
    ← ENNReal.ofRat_mul 1 1 (by decide +kernel) (by decide +kernel),
    ← ENNReal.ofRat_mul 2 3 (by decide +kernel) (by decide +kernel)]
  exact half_sum_ofRat (1 * 1) (2 * 3) (7 / 2) _ _ _ (by decide +kernel)

end

end Problib.Inference.FeynmanKac.Witnesses
