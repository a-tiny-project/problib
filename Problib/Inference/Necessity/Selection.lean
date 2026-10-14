module

public import Problib.Inference.Population.SelectionDensity
public import Problib.Inference.Necessity.Weighting
import Problib.Measure.Integral.Density.Zero
import Problib.Measure.Integral.Lebesgue.Extensionality
import Problib.Measure.Integral.Lebesgue.Measure
import Problib.Measure.Integral.Lebesgue.Transport
import Problib.Measure.Kernel.Measurable
set_option autoImplicit false

/-! Necessity for the density estimate of a selected lane.

A conditional run pinned at `x` estimates the selected law's density at `x`
only where the total weight is positive. Take one lane over the Booleans
against counting measure, the target `γ = δ_true`, so `γ(true) = 1` and
`γ(false) = 0`, and a fair proposal, so the lane is `(true, 2)` or `(false, 0)`
with equal probability. The point mass at the population `((true, 2))`, and at
`((false, 0))` over `false`, is a Markov conditional law of that population.
With one lane, selection returns that lane, so the selected law puts `1/2` on
`false`. The estimate `γ(x)/Ẑ_c` at `false` is zero, so its mean is not a
density of the selected law (`selection_positive_necessary`). Positivity fails
exactly at the population `((false, 0))`. -/

namespace Problib.Inference.Necessity.Selection

open Problib.Real Problib.Measure
open Problib.Inference.Necessity.Weighting (bools fair halfMass halfMass_ne_zero
  fair_probability half_sum_ofRat half_sum_scale)

public section

/-- One lane. -/
abbrev single : Lanes (Fin 1) := Lanes.fin 1

/-- Populations of one weighted Boolean. -/
abbrev populations : Space (Fin 1 → Bool × NNReal) := populationSpace (Fin 1) bools

/-- Every map out of a discrete space is measurable. -/
theorem discrete_map_measurable {α β : Type} {target : Space β} (function : α → β) :
    MeasurableMap (Space.discrete α) target function :=
  fun _ => True.intro

/-- Counting measure on the Booleans. -/
@[expose] noncomputable def counts : Measure bools :=
  Measure.add (Measure.dirac bools true) (Measure.dirac bools false)

/-- The target `δ_true`, read as an unnormalized target. -/
@[expose] noncomputable def target : Measure bools := Measure.dirac bools true

/-- The target's density against counting measure. -/
@[expose] noncomputable def targetDensity (value : Bool) : NNReal :=
  if value then NNReal.one else NNReal.zero

/-- The weight of a fair proposal for `δ_true`: two at `true`, zero at `false`. -/
@[expose] noncomputable def proposalWeight (value : Bool) : NNReal :=
  if value then NNReal.two else NNReal.zero

/-- The one-lane population holding `value` at its proposal weight. -/
@[expose] noncomputable def lane (value : Bool) : Fin 1 → Bool × NNReal :=
  fun _ => (value, proposalWeight value)

/-- One lane drawn from the fair proposal and weighted for the target. -/
@[expose] noncomputable def population : Measure populations :=
  fair populations (lane true) (lane false)

/-- The conditional run pinned at `value`: its only lane holds `value`. -/
@[expose] noncomputable def conditional : Kernel bools (markedSpace (Fin 1) bools) :=
  Kernel.deterministic (fun value => (lane value, (0 : Fin 1))) (discrete_map_measurable _)

/-- The lane drawn at zero total weight. -/
@[expose] noncomputable def fallback : Kernel populations (Space.discrete (Fin 1)) :=
  Kernel.deterministic (fun _ => (0 : Fin 1)) (MeasurableMap.constant _ _ 0)

theorem fallback_markov (draws : Fin 1 → Bool × NNReal) :
    Measure.IsProbability (fallback draws) :=
  Measure.IsProbability.dirac _ _

theorem conditional_markov (value : Bool) : Measure.IsProbability (conditional value) :=
  Measure.IsProbability.dirac _ _

/-- The conditional run's estimate `γ(x)/Ẑ_c`, read through `1/Ẑ_c`. -/
@[expose] noncomputable def estimate : Kernel bools weightSpace :=
  readEstimate conditional (Kernel.IsSFinite.ofMarkov conditional_markov)
    (fun pair => NNReal.mul (targetDensity pair.1)
      (NNReal.div NNReal.one (meanWeight single pair.2.1)))
    (selectedEstimate_measurable single bools (discrete_map_measurable _))

/-- The selected law: run the population and select its lane by weight. -/
@[expose] noncomputable def selected : Measure bools :=
  (population.bind (selection single bools fallback fallback_markov)).map Prod.fst
    (draw_value_measurable bools)

/-! ### Arithmetic of the example -/

theorem share_single : single.share = NNReal.one := by
  have unit := single.share_mul_count
  rw [show (NNReal.ofRat ((single.count : Nat) : Rat) Rat.natCast_nonneg) = NNReal.one from
    NNReal.ofRat_one, NNReal.mul_one] at unit
  exact unit

theorem finRange_one : List.finRange 1 = [(0 : Fin 1)] := by decide

theorem halfMass_double :
    ENNReal.mul halfMass (ENNReal.add ENNReal.one ENNReal.one) = ENNReal.one := by
  rw [← ENNReal.ofRat_one]
  exact half_sum_ofRat 1 1 1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem two_ne_zero_weight : NNReal.two ≠ NNReal.zero := NNReal.two_ne_zero

/-- The total weight of a one-lane population is its lane's weight. -/
theorem totalWeight_single (draws : Fin 1 → Bool × NNReal) :
    totalWeight single draws = (draws 0).2 := by
  show NNReal.additiveLaws.listSum ((List.finRange 1).map fun index => (draws index).2) = _
  rw [finRange_one]
  exact NNReal.add_zero _

/-- Integrating against the fair population averages the two lanes. -/
theorem lintegral_population {function : (Fin 1 → Bool × NNReal) → ENNReal}
    (measurable : ENNRealMeasurable populations function) :
    lintegral population function =
      ENNReal.mul halfMass (ENNReal.add (function (lane true)) (function (lane false))) := by
  rw [population, fair, lintegral_smul_measure, lintegral_add_measure,
    lintegral_dirac _ _ measurable, lintegral_dirac _ _ measurable]

/-! ### The example -/

/-- `δ_true` has density `1` at `true` and `0` at `false` against counting
measure. -/
theorem target_density :
    Measure.IsDensity target counts fun value => ENNReal.finite (targetDensity value) := by
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  rw [target, lintegral_dirac _ _ measurable,
    lintegral_withDensity _ (finite_weight_measurable (discrete_map_measurable _)) measurable,
    counts, lintegral_add_measure,
    lintegral_dirac _ _ (ENNRealMeasurable.mul
      (finite_weight_measurable (discrete_map_measurable targetDensity)) measurable),
    lintegral_dirac _ _ (ENNRealMeasurable.mul
      (finite_weight_measurable (discrete_map_measurable targetDensity)) measurable)]
  show function true = ENNReal.add (ENNReal.mul ENNReal.one (function true))
    (ENNReal.mul ENNReal.zero (function false))
  rw [ENNReal.one_mul, ENNReal.zero_mul, ENNReal.add_zero]

/-- The point masses at the populations holding each value form a conditional
law of the population for `δ_true`. -/
theorem conditional_law : ConditionalLaw single population target conditional := by
  refine ⟨?_, fun value => ?_⟩
  · refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
    have bound := Kernel.lintegral_measurable (markedLane single bools) measurable
    rw [target, Measure.dirac_bind, conditional, Kernel.deterministic_apply,
      lintegral_dirac _ _ measurable, extended, Measure.lintegral_bind _ _ measurable,
      lintegral_population bound, lintegral_markedLane single _ measurable,
      lintegral_markedLane single _ measurable, share_single]
    show function (lane true, 0) = ENNReal.mul halfMass (ENNReal.add
      (ENNReal.mul ENNReal.one (ENNReal.additiveLaws.listSum ((List.finRange 1).map fun index =>
        ENNReal.mul (ENNReal.finite NNReal.two) (function (lane true, index)))))
      (ENNReal.mul ENNReal.one (ENNReal.additiveLaws.listSum ((List.finRange 1).map fun index =>
        ENNReal.mul ENNReal.zero (function (lane false, index))))))
    rw [finRange_one]
    show function (lane true, 0) = ENNReal.mul halfMass (ENNReal.add
      (ENNReal.mul ENNReal.one (ENNReal.add
        (ENNReal.mul (ENNReal.add ENNReal.one ENNReal.one) (function (lane true, 0)))
        ENNReal.zero))
      (ENNReal.mul ENNReal.one (ENNReal.add
        (ENNReal.mul ENNReal.zero (function (lane false, 0))) ENNReal.zero)))
    rw [ENNReal.zero_mul, ENNReal.add_zero, ENNReal.add_zero, ENNReal.one_mul, ENNReal.one_mul,
      ENNReal.add_zero, ENNReal.mul_comm (ENNReal.add _ _), ENNReal.mul_add, ENNReal.mul_one,
      ← ENNReal.one_mul (function (lane true, 0)), half_sum_scale, halfMass_double]
    exact discrete_map_measurable _
  · show Measure.map (Measure.dirac _ (lane value, (0 : Fin 1))) _ _ =
      Measure.map (Measure.dirac _ (lane value, (0 : Fin 1))) _ _
    rw [Measure.map_dirac, Measure.map_dirac]
    all_goals first
      | rfl
      | exact Kernel.pair_left_measurable value
      | exact readMarked_measurable single bools

/-- The population `((false, 0))` has zero total weight and probability one
half. -/
theorem not_positive :
    ¬population.AE fun draws => totalWeight single draws ≠ NNReal.zero := by
  intro positive
  have zeroMeasurable : populations.Measurable fun draws =>
      ¬(totalWeight single draws ≠ NNReal.zero) := by
    have same : (fun draws : Fin 1 → Bool × NNReal =>
        ¬(totalWeight single draws ≠ NNReal.zero)) =
        zeroTotal single :=
      funext fun draws => propext ⟨fun zero => (zeroTotal_iff single draws).mpr
        (Classical.byContradiction zero), fun zero nonzero =>
          nonzero ((zeroTotal_iff single draws).mp zero)⟩
    rw [same]
    exact zeroTotal_measurable single bools
  have mass : population (fun draws => ¬(totalWeight single draws ≠ NNReal.zero)) =
      ENNReal.zero := positive
  rw [population, fair, Measure.smul_apply_measurable _ _ zeroMeasurable,
    Measure.add_apply_measurable _ _ zeroMeasurable,
    Measure.dirac_apply_of_not_mem _ _ zeroMeasurable (fun zero => zero (by
      rw [totalWeight_single]
      exact two_ne_zero_weight)),
    Measure.dirac_apply_of_mem _ _ zeroMeasurable (fun nonzero => nonzero (by
      rw [totalWeight_single]
      rfl)),
    ENNReal.zero_add, ENNReal.mul_one] at mass
  exact halfMass_ne_zero mass

/-- The selected law puts one half on `false`. -/
theorem selected_false : selected (fun value => value = false) = halfMass := by
  have falseMeasurable : bools.Measurable fun value : Bool => value = false :=
    Space.discrete_measurable _
  have drawMeasurable := draw_value_measurable bools falseMeasurable
  have atTrue : laneLaw single bools fallback (lane true) (fun _ => true = false) =
      ENNReal.zero := by
    have empty : (fun _ : Fin 1 => true = false) = Set.empty :=
      funext fun _ => propext ⟨fun wrong => Bool.noConfusion wrong, False.elim⟩
    rw [empty]
    exact Measure.empty_apply _
  have atFalse : laneLaw single bools fallback (lane false) (fun _ => false = false) =
      ENNReal.one := by
    have whole : (fun _ : Fin 1 => false = false) = Set.univ :=
      funext fun _ => propext ⟨fun _ => True.intro, fun _ => rfl⟩
    rw [whole]
    exact (laneLaw_markov single bools fallback_markov (lane false)).univ_eq_one
  rw [selected, Measure.map_apply _ _ _ falseMeasurable,
    Measure.bind_apply _ _ drawMeasurable,
    lintegral_population ((selection single bools fallback fallback_markov).measurable
      drawMeasurable),
    selection, Kernel.map_apply, Kernel.map_apply, Kernel.attach_apply, Kernel.attach_apply,
    Measure.map_comp, Measure.map_comp, Measure.map_apply _ _ _ drawMeasurable,
    Measure.map_apply _ _ _ drawMeasurable]
  show ENNReal.mul halfMass (ENNReal.add
    (laneLaw single bools fallback (lane true) (fun _ => true = false))
    (laneLaw single bools fallback (lane false) (fun _ => false = false))) = halfMass
  rw [atTrue, atFalse, ENNReal.zero_add, ENNReal.mul_one]

/-- Without positive total weight, the conditional run's estimate is unbiased
for no density of the selected law. Every other premise of
`selected_density_unbiased` holds: the target has a density, the conditional
law is a Markov conditional law of the population, and the estimate is read
off it. At `false` the estimate is zero, while the selected law puts one half
there. -/
theorem selection_positive_necessary :
    Measure.IsDensity target counts (fun value => ENNReal.finite (targetDensity value)) ∧
      ConditionalLaw single population target conditional ∧
      (∀ value, Measure.IsProbability (conditional value)) ∧
      ¬population.AE (fun draws => totalWeight single draws ≠ NNReal.zero) ∧
      ¬Measure.IsDensity selected counts
        (fun value => lintegral (estimate value) fun weight => ENNReal.finite weight) := by
  refine ⟨target_density, conditional_law, conditional_markov, not_positive, fun density => ?_⟩
  have meanMeasurable := Kernel.lintegral_measurable estimate
    (finite_weight_measurable (MeasurableMap.identity weightSpace))
  have falseMeasurable : bools.Measurable fun value : Bool => value = false :=
    Space.discrete_measurable _
  have vanishes : (Measure.withDensity counts fun value =>
      lintegral (estimate value) fun weight => ENNReal.finite weight)
      (fun value => value = false) = ENNReal.zero := by
    refine (Measure.withDensity_apply_eq_zero_iff meanMeasurable falseMeasurable).mpr ?_
    have empty : Set.inter (fun value : Bool => value = false)
        (fun value => (lintegral (estimate value) fun weight => ENNReal.finite weight) ≠
          ENNReal.zero) = Set.empty := by
      refine Set.ext fun value => ⟨fun member => (member.2 ?_).elim, fun member => member.elim⟩
      rw [member.1, estimate,
        readEstimate_apply _ _ (selectedEstimate_measurable single bools (discrete_map_measurable _)),
        lintegral_map _ _ _ (finite_weight_measurable (MeasurableMap.identity weightSpace))]
      show lintegral (conditional false) (fun marked => ENNReal.finite (NNReal.mul NNReal.zero
        (NNReal.div NNReal.one (meanWeight single marked.1)))) = ENNReal.zero
      have zero : (fun marked : (Fin 1 → Bool × NNReal) × Fin 1 => ENNReal.finite
          (NNReal.mul NNReal.zero (NNReal.div NNReal.one (meanWeight single marked.1)))) =
          fun _ => ENNReal.zero :=
        funext fun marked => congrArg ENNReal.finite (NNReal.zero_mul _)
      rw [zero]
      exact lintegral_zero _
    rw [empty]
    exact counts.empty_apply
  rw [← density, selected_false] at vanishes
  exact halfMass_ne_zero vanishes

end

end Problib.Inference.Necessity.Selection
