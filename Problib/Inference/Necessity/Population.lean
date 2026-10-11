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
both statements directly.

Inv_N is a property of the whole population, not of any lane. Two lanes that
put weight two on a fair Boolean and weight zero on its negation are invariant
for the fair coin (`correlated_invariant`). Neither lane alone is properly
weighted for it: lane zero's expected weight is two and lane one's is zero
(`lane_not_properlyWeighted`). -/

namespace Problib.Inference.Necessity.Population

open Problib.Real Problib.Measure
open Problib.Inference.Necessity.Weighting (bools fair halfMass halfMass_ne_zero fair_probability
  rationalWeight lintegral_fair half_ofRat half_sum_ofRat)

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

/-! ### Correlated lanes -/

/-- Weight two. -/
@[expose] noncomputable def two : NNReal := rationalWeight 2 (by decide +kernel)

/-- Weight two on `value` in lane zero and weight zero on its negation in lane
one. -/
@[expose] noncomputable def opposed (value : Bool) : Fin 2 → Bool × NNReal :=
  fun lane => if lane = 0 then (value, two) else (!value, NNReal.zero)

/-- A fair choice between the two opposed populations. The lanes always carry opposite
values. -/
@[expose] noncomputable def correlated : Measure (populationSpace (Fin 2) bools) :=
  fair _ (opposed true) (opposed false)

private theorem share_two : ENNReal.finite (Lanes.fin 2).share = halfMass := by
  unfold Lanes.share halfMass ENNReal.ofRat
  congr 1
  apply NNReal.ofRat_congr
  show (((List.finRange 2).length : Nat) : Rat)⁻¹ = 1 / 2
  rw [List.length_finRange]
  decide +kernel

private theorem empirical_opposed (value : Bool) {function : Bool → ENNReal}
    (measurable : ENNRealMeasurable bools function) :
    lintegral (empirical (Lanes.fin 2) bools (opposed value)) function = function value := by
  rw [lintegral_empirical _ _ measurable, share_two]
  change ENNReal.mul halfMass (ENNReal.add
      (ENNReal.mul (ENNReal.ofRat 2 (by decide +kernel)) (function value))
      (ENNReal.add (ENNReal.mul ENNReal.zero (function (!value))) ENNReal.zero)) = function value
  rw [ENNReal.zero_mul, ENNReal.add_zero, ENNReal.add_zero, ← ENNReal.mul_assoc,
    half_ofRat 2 1 (by decide +kernel) (by decide +kernel) (by decide +kernel),
    ENNReal.ofRat_one, ENNReal.one_mul]

/-- The correlated population is invariant for the fair coin. -/
theorem correlated_invariant : EmpiricalInvariant (Lanes.fin 2) coin correlated := by
  refine ⟨fair_probability _ _ _, ?_⟩
  apply (Measure.eq_iff_lintegral _ _).mpr
  intro function measurable
  rw [Measure.lintegral_bind _ _ measurable, correlated,
    lintegral_fair _ _ _ (Kernel.lintegral_measurable _ measurable),
    empirical_opposed true measurable, empirical_opposed false measurable, coin,
    lintegral_fair _ _ _ measurable]
  exact congrArg (ENNReal.mul halfMass) (ENNReal.add_comm _ _)

/-- No fixed lane of the correlated population is properly weighted for the
fair coin. -/
theorem lane_not_properlyWeighted (lane : Fin 2) :
    ¬ProperlyWeighted coin (correlated.map (fun draws => draws lane) (lane_measurable bools lane)) := by
  intro proper
  have total := properlyWeighted_mass proper
  rw [lintegral_map _ _ _ (drawWeight_measurable bools), correlated,
    lintegral_fair _ _ _ ((drawWeight_measurable bools).comp (lane_measurable bools lane)),
    coin, (fair_probability bools false true).univ_eq_one] at total
  rcases lane with ⟨_ | _ | _, bound⟩
  · change ENNReal.mul halfMass (ENNReal.add (ENNReal.ofRat 2 (by decide +kernel))
        (ENNReal.ofRat 2 (by decide +kernel))) = ENNReal.one at total
    rw [half_sum_ofRat 2 2 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel), ← ENNReal.ofRat_one] at total
    exact absurd (NNReal.ofRat_injective (ENNReal.finite_injective total)) (by decide +kernel)
  · change ENNReal.mul halfMass (ENNReal.add ENNReal.zero ENNReal.zero) = ENNReal.one at total
    rw [ENNReal.add_zero, ENNReal.mul_zero] at total
    exact ENNReal.one_ne_zero total.symm
  · omega

end

end Problib.Inference.Necessity.Population
