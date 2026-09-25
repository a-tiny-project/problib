module

public import Problib.Inference.Population
public import Problib.Inference.Necessity.Weighting
set_option autoImplicit false

/-! Necessity for population steps.

Invariance of each kernel in a family does not make a state-dependent choice
among them invariant. On the fair coin, keeping the state and swapping it are
both invariant, but keeping at `false` and swapping at `true` sends all mass to
`false` (`adaptive_selection_not_invariant`). So a rejuvenation chosen by the
population needs its own stage identity, and `empirical_rejuvenate` takes one
fixed kernel. A kernel invariant for one target is not invariant for another:
redrawing a fair Boolean keeps the fair coin and destroys `δ_true`
(`stale_rejuvenation_not_invariant`). A one-lane population of weight one reads
both statements directly. -/

namespace Problib.Inference.Necessity.Population

open Problib.Real Problib.Measure
open Problib.Inference.Necessity.Weighting (bools fair halfMass halfMass_ne_zero fair_probability)

public section

/-- The fair coin. -/
@[expose] noncomputable def coin : Measure bools := fair bools false true

/-- Every map out of a discrete space is measurable. -/
theorem discrete_map_measurable {α β : Type} {target : Space β} (function : α → β) :
    MeasurableMap (Space.discrete α) target function :=
  fun _ => True.intro

/-- Keep the state. -/
@[expose] noncomputable def keep : Kernel bools bools :=
  Kernel.deterministic (fun value => value) (discrete_map_measurable _)

/-- Swap the state. -/
@[expose] noncomputable def swap : Kernel bools bools :=
  Kernel.deterministic (fun value => !value) (discrete_map_measurable _)

/-- Keep at `false` and swap at `true`: a choice between two invariant kernels
made by the state itself. -/
@[expose] noncomputable def selected : Kernel bools bools :=
  Kernel.deterministic (fun value => if value then !value else value) (discrete_map_measurable _)

/-- Keeping and swapping each preserve the fair coin, and the selection agrees
with one of them at every state, but the selection sends the coin to
`δ_false`. -/
theorem adaptive_selection_not_invariant :
    KernelInvariant coin keep ∧ KernelInvariant coin swap ∧
      (∀ value, selected value = if value then swap value else keep value) ∧
      ¬KernelInvariant coin selected := by
  have trueMeasurable : bools.Measurable (fun value : Bool => value = true) :=
    Space.discrete_measurable _
  refine ⟨?_, ?_, fun value => by cases value <;> rfl, fun invariant => ?_⟩
  · show coin.bind keep = coin
    rw [keep, Measure.bind_deterministic, coin, fair, Measure.map_smul, Measure.map_add,
      Measure.map_dirac, Measure.map_dirac]
    exact discrete_map_measurable _
  · show coin.bind swap = coin
    rw [swap, Measure.bind_deterministic, coin, fair, Measure.map_smul, Measure.map_add,
      Measure.map_dirac, Measure.map_dirac]
    show Measure.smul halfMass
        (Measure.add (Measure.dirac bools true) (Measure.dirac bools false)) = _
    rw [Measure.add_comm]
    exact discrete_map_measurable _
  · have bound : coin.bind selected = coin := invariant
    have atTrue : (coin.bind selected) (fun value => value = true) =
        coin (fun value => value = true) := by
      rw [bound]
    rw [selected, Measure.bind_deterministic, coin, fair, Measure.map_smul, Measure.map_add,
      Measure.map_dirac, Measure.map_dirac, Measure.smul_apply_measurable _ _ trueMeasurable,
      Measure.smul_apply_measurable _ _ trueMeasurable,
      Measure.add_apply_measurable _ _ trueMeasurable,
      Measure.add_apply_measurable _ _ trueMeasurable,
      Measure.dirac_apply_of_not_mem _ _ trueMeasurable (by decide),
      Measure.dirac_apply_of_not_mem _ _ trueMeasurable (by decide),
      Measure.dirac_apply_of_not_mem _ _ trueMeasurable (by decide),
      Measure.dirac_apply_of_mem _ _ trueMeasurable rfl, ENNReal.zero_add, ENNReal.zero_add,
      ENNReal.mul_zero, ENNReal.mul_one] at atTrue
    · exact halfMass_ne_zero atTrue.symm
    · exact discrete_map_measurable _

/-- Redraw a fair Boolean, whatever the state. -/
@[expose] noncomputable def redraw : Kernel bools bools := Kernel.const bools coin

/-- The redraw keeps the fair coin and does not keep `δ_true`. -/
theorem stale_rejuvenation_not_invariant :
    KernelInvariant coin redraw ∧ ¬KernelInvariant (Measure.dirac bools true) redraw := by
  have falseMeasurable : bools.Measurable (fun value : Bool => value = false) :=
    Space.discrete_measurable _
  refine ⟨?_, fun invariant => ?_⟩
  · show coin.bind redraw = coin
    have coinProbability : Measure.IsProbability coin := fair_probability bools false true
    rw [redraw, Measure.bind_const, coinProbability.univ_eq_one, Measure.one_smul]
  · have bound : (Measure.dirac bools true).bind redraw = Measure.dirac bools true := invariant
    have atFalse : ((Measure.dirac bools true).bind redraw) (fun value => value = false) =
        (Measure.dirac bools true) (fun value => value = false) := by
      rw [bound]
    rw [redraw, Measure.bind_const, Measure.dirac_apply_univ, Measure.one_smul, coin, fair,
      Measure.smul_apply_measurable _ _ falseMeasurable,
      Measure.add_apply_measurable _ _ falseMeasurable,
      Measure.dirac_apply_of_mem _ _ falseMeasurable rfl,
      Measure.dirac_apply_of_not_mem _ _ falseMeasurable (by decide), ENNReal.add_zero,
      ENNReal.mul_one] at atFalse
    exact halfMass_ne_zero atFalse

end

end Problib.Inference.Necessity.Population
