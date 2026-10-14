module

public import Problib.Inference.PseudoMarginal
public import Problib.Inference.Necessity.Weighting
public import Problib.Measure.Space.Countable
set_option autoImplicit false

/-! Necessity for pseudo-marginal chains: the current estimate must be kept.

The pseudo-marginal chain keeps the estimate of its current state until a move
is accepted. Monte Carlo within Metropolis (`mcwmKernel`) refreshes the current
estimate at every step as well, and that chain does not keep its target.

Two states carry the uniform target. The proposal always moves to the other
state. A fair coin is the auxiliary. The estimate is exactly `1/2` at `false`,
and `1/4` or `3/4` by the coin at `true`, so it is unbiased at both states.
Refreshing both estimates moves `false → true` with probability `3/4` and
`true → false` with probability `5/6`. The uniform law then maps to `13/24`
at `false` (`mcwm_uniform_image`), so it is not invariant
(`mcwm_not_invariant`). The chain's stationary law is `(10/19, 9/19)`. The
pseudo-marginal chain on the same data keeps its extended target, whose value
marginal is the uniform law at half its mass (`pseudoMarginal_invariant`).

Proofs are finite evaluations of Dirac sums. -/

namespace Problib.Inference.Necessity.PseudoMarginal

open Problib.Real Problib.Measure
open Problib.Real.Construction
open Problib.Measure.Real (Carrier)
open Problib.Inference.Necessity.Weighting (bools fair halfMass lintegral_fair fair_probability
  half_sum_ofRat half_sum_scale rationalWeight ofRat_congr)

public section

/-! ### Monte Carlo within Metropolis -/

/-- Monte Carlo within Metropolis: draw a fresh auxiliary at the current value,
take one pseudo-marginal step, and keep only the value. -/
@[expose] noncomputable def mcwmKernel {α υ : Type} {space : Space α} {extra : Space υ}
    (proposal : Kernel space space) (proposalFinite : Kernel.IsSFinite proposal)
    (estimator : Kernel space extra) (estimatorFinite : Kernel.IsSFinite estimator)
    (estimate : α × υ → NNReal)
    (estimateMeasurable : MeasurableMap (Space.product space extra) weightSpace estimate) :
    Kernel space space :=
  ((estimator.attach estimatorFinite).comp
    (pseudoMarginalKernel proposal proposalFinite estimator estimatorFinite estimate
      estimateMeasurable)).map Prod.fst (Space.first_measurable space extra)

/-! ### Two states and a coin -/

/-- A value with its coin. -/
abbrev pairs : Space (Bool × Bool) := Space.product bools bools

private def codeBool (value : Bool) : Nat := if value then 1 else 0

private def code (point : Bool × Bool) : Nat := 2 * codeBool point.1 + codeBool point.2

private theorem code_injective : Function.Injective code := by
  intro left right same
  rcases left with ⟨first, second⟩
  rcases right with ⟨third, fourth⟩
  cases first <;> cases second <;> cases third <;> cases fourth <;>
    first | rfl | exact absurd same (by decide)

/-- Every set of values with coins is measurable: it is a union of points. -/
theorem pairs_measurable (set : Set (Bool × Bool)) : pairs.Measurable set := by
  have points := Space.i_union_of_nat_injection pairs code code_injective
    (fun point => Set.product (fun value => set point ∧ value = point.1)
      (fun coin => coin = point.2))
    (fun _ => Space.product_set_measurable bools bools (Space.discrete_measurable _)
      (Space.discrete_measurable _))
  have same : (fun value => ∃ point, Set.product
      (fun first => set point ∧ first = point.1)
      (fun coin => coin = point.2) value) = set := by
    apply Set.ext
    intro value
    constructor
    · rintro ⟨point, ⟨inside, first⟩, second⟩
      have equal : value = point := Prod.ext first second
      exact equal ▸ inside
    · intro inside
      exact ⟨value, ⟨inside, rfl⟩, rfl⟩
  rw [← same]
  exact points

private theorem pairs_ennreal (function : Bool × Bool → ENNReal) :
    ENNRealMeasurable pairs function :=
  fun _ => pairs_measurable _

/-- The uniform law on the two values. -/
noncomputable abbrev uniform : Measure bools := fair bools false true

/-- Always propose the other value. -/
@[expose] noncomputable def flip : Kernel bools bools :=
  Kernel.deterministic (fun value => !value) (MeasurableMap.from_discrete _ _)

@[expose] noncomputable def flipFinite : Kernel.IsSFinite flip :=
  Kernel.IsSFinite.deterministic (fun value : Bool => !value) (MeasurableMap.from_discrete _ _)

/-- A fair coin at every value. -/
@[expose] noncomputable def coin : Kernel bools bools := Kernel.const bools uniform

@[expose] noncomputable def coinFinite : Kernel.IsSFinite coin :=
  Kernel.IsSFinite.const bools
    (Measure.SFinite.ofFinite (fair_probability bools false true).to_finite)

/-- Exactly `1/2` at `false`, and `1/4` or `3/4` by the coin at `true`. -/
@[expose] def estimate : Bool × Bool → NNReal
  | (false, _) => rationalWeight (1 / 2) (by decide +kernel)
  | (true, false) => rationalWeight (1 / 4) (by decide +kernel)
  | (true, true) => rationalWeight (3 / 4) (by decide +kernel)

theorem estimate_measurable : MeasurableMap pairs weightSpace estimate :=
  fun _ => pairs_measurable _

/-- The estimate read as a real weight. -/
abbrev weight (point : Bool × Bool) : Carrier := NNReal.toReal (estimate point)

/-- The chain that refreshes both estimates. -/
@[expose] noncomputable def mcwm : Kernel bools bools :=
  mcwmKernel flip flipFinite coin coinFinite estimate estimate_measurable

/-- The chain that keeps the current estimate. -/
@[expose] noncomputable def pseudoMarginal : Kernel pairs pairs :=
  pseudoMarginalKernel flip flipFinite coin coinFinite estimate estimate_measurable

/-! ### Acceptances -/

private theorem ofRat_positive (value : Rat) (nonnegative : 0 ≤ value) (positive : 0 < value) :
    ENNReal.lt ENNReal.zero (ENNReal.ofRat value nonnegative) := by
  rw [← ENNReal.ofRat_zero]
  exact (ENNReal.ofRat_lt_iff _ _ _ _).mpr positive

private theorem real_positive (value : Rat) (positive : 0 < value) :
    Dedekind.lt Dedekind.zero (Dedekind.selection.ofRat value) := by
  rw [← Dedekind.ofRat_zero]
  exact (Dedekind.ofRat_lt_iff _ _).mpr positive

/-- The estimate read as an extended weight is its rational value. -/
private theorem ofReal_weight (value : Rat) (nonnegative : 0 ≤ value) :
    ENNReal.ofReal (NNReal.toReal (rationalWeight value nonnegative)) =
      ENNReal.ofRat value nonnegative :=
  ENNReal.ofReal_toReal_finite _

/-- From `1/2` to `1/4` the move is accepted with probability `1/2`. -/
private theorem accept_down_half (current : Bool) :
    metropolisAccept weight ((false, current), (true, false)) =
      ENNReal.ofRat (1 / 2) (by decide +kernel) := by
  have balance := metropolis_balance weight ((false, current), (true, false))
  have from_ : ENNReal.ofReal (weight (false, current)) =
      ENNReal.ofRat (1 / 2) (by decide +kernel) := by
    cases current <;> exact ofReal_weight _ _
  rw [from_, show ENNReal.ofReal (weight (true, false)) =
      ENNReal.ofRat (1 / 4) (by decide +kernel) from ofReal_weight _ _,
    ENNReal.min_eq_right ((ENNReal.ofRat_le_iff _ _ _ _).mpr (by decide +kernel))] at balance
  refine ENNReal.mul_right_cancel_of_finite (factor := ENNReal.ofRat (1 / 2) (by decide +kernel))
    True.intro (ofRat_positive _ _ (by decide +kernel)) ?_
  rw [ENNReal.mul_comm (metropolisAccept _ _), balance, ← ENNReal.ofRat_mul]
  exact ofRat_congr (by decide +kernel) _ _

/-- From `3/4` to `1/2` the move is accepted with probability `2/3`. -/
private theorem accept_down_twoThirds (proposed : Bool) :
    metropolisAccept weight ((true, true), (false, proposed)) =
      ENNReal.ofRat (2 / 3) (by decide +kernel) := by
  have balance := metropolis_balance weight ((true, true), (false, proposed))
  have to : ENNReal.ofReal (weight (false, proposed)) =
      ENNReal.ofRat (1 / 2) (by decide +kernel) := by
    cases proposed <;> exact ofReal_weight _ _
  rw [to, show ENNReal.ofReal (weight (true, true)) =
      ENNReal.ofRat (3 / 4) (by decide +kernel) from ofReal_weight _ _,
    ENNReal.min_eq_right ((ENNReal.ofRat_le_iff _ _ _ _).mpr (by decide +kernel))] at balance
  refine ENNReal.mul_right_cancel_of_finite (factor := ENNReal.ofRat (3 / 4) (by decide +kernel))
    True.intro (ofRat_positive _ _ (by decide +kernel)) ?_
  rw [ENNReal.mul_comm (metropolisAccept _ _), balance, ENNReal.mul_comm, ← ENNReal.ofRat_mul]
  exact ofRat_congr (by decide +kernel) _ _

/-- From `1/2` to `3/4` the move is always accepted. -/
private theorem accept_up_threeQuarters (current : Bool) :
    metropolisAccept weight ((false, current), (true, true)) = ENNReal.one := by
  have from_ : weight (false, current) = Dedekind.selection.ofRat (1 / 2) := by
    cases current <;> rfl
  apply metropolisAccept_eq_one
  · change Dedekind.le (weight (false, current)) (Dedekind.selection.ofRat (3 / 4))
    rw [from_]
    exact (Dedekind.ofRat_le_iff _ _).mpr (by decide +kernel)
  · exact real_positive (3 / 4) (by decide +kernel)

/-- From `1/4` to `1/2` the move is always accepted. -/
private theorem accept_up_half (proposed : Bool) :
    metropolisAccept weight ((true, false), (false, proposed)) = ENNReal.one := by
  have to : weight (false, proposed) = Dedekind.selection.ofRat (1 / 2) := by
    cases proposed <;> rfl
  apply metropolisAccept_eq_one
  · change Dedekind.le (Dedekind.selection.ofRat (1 / 4)) (weight (false, proposed))
    rw [to]
    exact (Dedekind.ofRat_le_iff _ _).mpr (by decide +kernel)
  · change Dedekind.lt Dedekind.zero (weight (false, proposed))
    rw [to]
    exact real_positive (1 / 2) (by decide +kernel)

/-! ### One step of each chain -/

/-- The test for being at `false`. -/
@[expose] noncomputable def atFalse (value : Bool) : ENNReal :=
  if value then ENNReal.zero else ENNReal.one

/-- One pseudo-marginal step from `(x, c)`, read on a test of the value: the
coin at the other value is drawn fresh, and the move is accepted or not. -/
private theorem lintegral_pseudoMarginal (state current : Bool) (function : Bool → ENNReal) :
    lintegral (pseudoMarginal (state, current)) (fun point => function point.1) =
      ENNReal.mul halfMass (ENNReal.add
        (ENNReal.add
          (ENNReal.mul (metropolisAccept weight ((state, current), (!state, false)))
            (function (!state)))
          (ENNReal.mul (ENNReal.sub ENNReal.one
              (metropolisAccept weight ((state, current), (!state, false))))
            (function state)))
        (ENNReal.add
          (ENNReal.mul (metropolisAccept weight ((state, current), (!state, true)))
            (function (!state)))
          (ENNReal.mul (ENNReal.sub ENNReal.one
              (metropolisAccept weight ((state, current), (!state, true))))
            (function state)))) := by
  rw [pseudoMarginal, pseudoMarginalKernel,
    lintegral_mhKernel _ _ _ _ _ (pairs_ennreal _), extendedProposal_apply,
    lintegral_semiproduct _ _ _ (pairs_ennreal _)]
  change lintegral (Measure.dirac bools (!state)) _ = _
  rw [lintegral_dirac _ _ (ENNRealMeasurable.from_discrete _)]
  change lintegral uniform _ = _
  rw [lintegral_fair _ _ _ (ENNRealMeasurable.from_discrete _)]

/-- One Monte Carlo within Metropolis step, read on a test: the current coin is
drawn fresh before the pseudo-marginal step. -/
private theorem lintegral_mcwm (state : Bool) (function : Bool → ENNReal) :
    lintegral (mcwm state) function =
      ENNReal.mul halfMass (ENNReal.add
        (lintegral (pseudoMarginal (state, false)) (fun point => function point.1))
        (lintegral (pseudoMarginal (state, true)) (fun point => function point.1))) := by
  rw [mcwm, mcwmKernel, Kernel.map_apply,
    lintegral_map _ _ _ (ENNRealMeasurable.from_discrete _), Kernel.comp_apply,
    Measure.lintegral_bind _ _ (pairs_ennreal _), Kernel.attach_apply,
    lintegral_map _ _ _ (pairs_ennreal _)]
  change lintegral uniform _ = _
  rw [lintegral_fair _ _ _ (ENNRealMeasurable.from_discrete _)]
  rfl

private theorem half_twice (value : Rat) (nonnegative : 0 ≤ value) :
    ENNReal.mul halfMass (ENNReal.add (ENNReal.ofRat value nonnegative)
      (ENNReal.ofRat value nonnegative)) = ENNReal.ofRat value nonnegative :=
  half_sum_ofRat value value value nonnegative nonnegative nonnegative (by grind)

private theorem half_twice_one (value : ENNReal) :
    ENNReal.mul halfMass (ENNReal.add value value) = value := by
  have scaled := half_sum_scale ENNReal.one ENNReal.one value
  rw [ENNReal.one_mul, ← ENNReal.ofRat_one, half_twice, ENNReal.ofRat_one,
    ENNReal.one_mul] at scaled
  exact scaled

private theorem one_sub_half :
    ENNReal.sub ENNReal.one (ENNReal.ofRat (1 / 2) (by decide +kernel)) =
      ENNReal.ofRat (1 / 2) (by decide +kernel) := by
  have split : ENNReal.one = ENNReal.add (ENNReal.ofRat (1 / 2) (by decide +kernel))
      (ENNReal.ofRat (1 / 2) (by decide +kernel)) := by
    rw [← ENNReal.ofRat_one, ← ENNReal.ofRat_add]
    exact ofRat_congr (by decide +kernel) _ _
  rw [split, ENNReal.add_sub_cancel_right (right := ENNReal.ofRat (1 / 2) (by decide +kernel))
    True.intro]

/-- From `false`, the chain leaves with probability `3/4`. -/
theorem mcwm_false_stays :
    lintegral (mcwm false) atFalse = ENNReal.ofRat (1 / 4) (by decide +kernel) := by
  have step : ∀ current, lintegral (pseudoMarginal (false, current))
      (fun point => atFalse point.1) = ENNReal.ofRat (1 / 4) (by decide +kernel) := by
    intro current
    rw [lintegral_pseudoMarginal, Bool.not_false, accept_down_half, accept_up_threeQuarters]
    change ENNReal.mul halfMass (ENNReal.add
        (ENNReal.add (ENNReal.mul _ ENNReal.zero) (ENNReal.mul _ ENNReal.one))
        (ENNReal.add (ENNReal.mul _ ENNReal.zero) (ENNReal.mul _ ENNReal.one))) = _
    rw [ENNReal.mul_zero, ENNReal.mul_zero, ENNReal.zero_add, ENNReal.zero_add,
      ENNReal.mul_one, ENNReal.mul_one, ENNReal.sub_self, one_sub_half, ← ENNReal.ofRat_zero]
    exact half_sum_ofRat _ _ _ _ _ _ (by decide +kernel)
  rw [lintegral_mcwm, step, step]
  exact half_twice _ _

/-- From `true`, the chain leaves with probability `5/6`. -/
theorem mcwm_true_leaves :
    lintegral (mcwm true) atFalse = ENNReal.ofRat (5 / 6) (by decide +kernel) := by
  have step : ∀ current, lintegral (pseudoMarginal (true, current))
      (fun point => atFalse point.1) =
        metropolisAccept weight ((true, current), (false, false)) := by
    intro current
    rw [lintegral_pseudoMarginal, Bool.not_true]
    have same : metropolisAccept weight ((true, current), (false, true)) =
        metropolisAccept weight ((true, current), (false, false)) := by
      cases current
      · rw [accept_up_half, accept_up_half]
      · rw [accept_down_twoThirds, accept_down_twoThirds]
    rw [same]
    change ENNReal.mul halfMass (ENNReal.add
        (ENNReal.add (ENNReal.mul _ ENNReal.one) (ENNReal.mul _ ENNReal.zero))
        (ENNReal.add (ENNReal.mul _ ENNReal.one) (ENNReal.mul _ ENNReal.zero))) = _
    rw [ENNReal.mul_zero, ENNReal.add_zero, ENNReal.mul_one]
    exact half_twice_one _
  rw [lintegral_mcwm, step, step, accept_up_half, accept_down_twoThirds, ← ENNReal.ofRat_one]
  exact half_sum_ofRat _ _ _ _ _ _ (by decide +kernel)

/-- The uniform law after one step of Monte Carlo within Metropolis has mass
`13/24` at `false`. -/
theorem mcwm_uniform_image :
    (uniform.bind mcwm) (fun value => value = false) =
      ENNReal.ofRat (13 / 24) (by decide +kernel) := by
  have falseMeasurable : bools.Measurable (fun value : Bool => value = false) :=
    Space.discrete_measurable _
  have atFalse_indicator : ∀ state, mcwm state (fun value => value = false) =
      lintegral (mcwm state) atFalse := by
    intro state
    rw [apply_eq_lintegral_indicator _ falseMeasurable]
    apply lintegral_congr
    intro value
    cases value
    · rw [ennrealIndicator_of_mem (region := fun value : Bool => value = false) rfl]
      rfl
    · rw [ennrealIndicator_of_not_mem (region := fun value : Bool => value = false)
        (by decide)]
      rfl
  rw [Measure.bind_apply _ _ falseMeasurable]
  change lintegral uniform _ = _
  rw [lintegral_fair _ _ _ (ENNRealMeasurable.from_discrete _), atFalse_indicator,
    atFalse_indicator, mcwm_false_stays, mcwm_true_leaves]
  exact half_sum_ofRat _ _ _ _ _ _ (by decide +kernel)

/-- Refreshing the current estimate breaks invariance: the uniform law is not
invariant for Monte Carlo within Metropolis, although the estimate is unbiased
at both values. -/
theorem mcwm_not_invariant : ¬KernelInvariant uniform mcwm := by
  intro invariant
  have image := mcwm_uniform_image
  have atFalse_mass : uniform (fun value => value = false) =
      ENNReal.ofRat (1 / 2) (by decide +kernel) := by
    rw [uniform, fair, Measure.smul_apply_measurable _ _ (Space.discrete_measurable _),
      Measure.add_apply_measurable _ _ (Space.discrete_measurable _),
      Measure.dirac_apply_of_mem _ _ (set := fun value : Bool => value = false)
        (Space.discrete_measurable _) rfl,
      Measure.dirac_apply_of_not_mem _ _ (set := fun value : Bool => value = false)
        (Space.discrete_measurable _) (by decide),
      ENNReal.add_zero, ENNReal.mul_one]
    rfl
  have bound : uniform.bind mcwm = uniform := invariant
  rw [bound, atFalse_mass] at image
  have below : ENNReal.le (ENNReal.ofRat (13 / 24) (by decide +kernel))
      (ENNReal.ofRat (1 / 2) (by decide +kernel)) := by
    rw [← image]
    exact ENNReal.le_refl _
  exact absurd ((ENNReal.ofRat_le_iff _ _ _ _).mp below) (by decide +kernel)

/-! ### The pseudo-marginal chain on the same data -/

/-- The flip is reversible for the uniform law. -/
theorem flip_reversible : DetailedBalance uniform flip flipFinite := by
  unfold DetailedBalance
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  rw [lintegral_map _ _ _ measurable,
    lintegral_semiproduct _ _ _ (pairs_ennreal _), lintegral_semiproduct _ _ _ measurable]
  change lintegral uniform _ = lintegral uniform _
  rw [lintegral_fair _ _ _ (ENNRealMeasurable.from_discrete _),
    lintegral_fair _ _ _ (ENNRealMeasurable.from_discrete _)]
  change ENNReal.mul halfMass (ENNReal.add
      (lintegral (Measure.dirac bools true) _) (lintegral (Measure.dirac bools false) _)) =
    ENNReal.mul halfMass (ENNReal.add
      (lintegral (Measure.dirac bools true) _) (lintegral (Measure.dirac bools false) _))
  rw [lintegral_dirac _ _ (ENNRealMeasurable.from_discrete _),
    lintegral_dirac _ _ (ENNRealMeasurable.from_discrete _),
    lintegral_dirac _ _ (ENNRealMeasurable.from_discrete _),
    lintegral_dirac _ _ (ENNRealMeasurable.from_discrete _), ENNReal.add_comm]

/-- The estimate read off the coin is unbiased for `1/2` at both values. -/
theorem estimate_unbiased :
    UnbiasedEstimate (fun _ => halfMass) (readEstimate coin coinFinite estimate
      estimate_measurable) where
  probability value := by
    rw [readEstimate_apply]
    exact (fair_probability bools false true).map _ _
  mean_eq value := by
    rw [readEstimate_apply,
      lintegral_map _ _ _ (finite_weight_measurable (MeasurableMap.identity weightSpace))]
    change lintegral uniform _ = _
    rw [lintegral_fair _ _ _ (ENNRealMeasurable.from_discrete _)]
    cases value
    · exact half_twice _ _
    · exact half_sum_ofRat (1 / 4) (3 / 4) (1 / 2) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel)

/-- Keeping the current estimate keeps the extended target, whose value
marginal is the uniform law at half its mass. -/
theorem pseudoMarginal_invariant :
    KernelInvariant (extendedTarget uniform coin coinFinite estimate) pseudoMarginal ∧
      (extendedTarget uniform coin coinFinite estimate).map Prod.fst
          (Space.first_measurable bools bools) =
        uniform.withDensity (fun _ => halfMass) :=
  ⟨pseudoMarginalKernel_invariant (fun _ => Measure.IsProbability.dirac _ _) flip_reversible
      (fun _ => fair_probability bools false true) estimate_measurable,
    pseudo_marginal_marginal coinFinite estimate_measurable estimate_unbiased⟩

end

end Problib.Inference.Necessity.PseudoMarginal
