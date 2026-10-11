module

public import Problib.Inference.Necessity.PseudoMarginal
public import Problib.Inference.Reciprocal
public import Problib.Inference.SPI
set_option autoImplicit false

/-! Necessity for reciprocal samplers.

RAVI weighs a joint draw `(x, u)` of a mixture `q(x) = Σ_u m(u) k(x | u)` by
`r(u | x) / (m(u) k(x | u))`, where `r` is a meta kernel's density. The weighted
draws are properly weighted for the reference measure when the meta kernel puts
no mass where `m(u) k(x | u)` vanishes (`ravi_forward_properlyWeighted`'s
`answer`).

The proposal here draws `u` fairly. At `u = true` it returns `x = true`, and at
`u = false` it draws `x` fairly, so `q(true) = 3/4` and `q(false) = 1/4`. The
meta kernel is fair in `u` and ignores `x`. At `x = false` it puts mass `1/2` on
`u = true`, which cannot produce `x = false`, so the support condition fails
there. Only `u = false` reaches `x = false`, with weight `(1/2)/(1/4) = 2`, where
the reciprocal `1/q(false)` is `4`. At `x = true` the weight is `1` or `2`, with
conditional mean `4/3 = 1/q(true)`. So the weighted law is properly weighted for
`δ_true + (1/2)δ_false` and not for counting measure on the two values
(`ravi_support_necessary`). Both values have positive `q`, so restricting the
reference to `{q > 0}` cannot repair the lost mass.

A reciprocal sampler need not draw from its target. The target puts `1/4` on
`false` and `3/4` on `true`, so against counting measure its density is
positive everywhere. Fair draws at weight two are properly weighted for counting
measure, so they reciprocally weigh the target, yet the drawn point is fair
(`reciprocal_marginal_necessary`).

Strict reciprocity is still not what Metropolis–Hastings with an estimated
proposal density consumes. The proposal is fair at either current value. At
`false` the sampler draws `y` fairly and, independently, `r = 1` or `r = 3`, and
at `true` it draws `y` fairly with `r = 2`. Both are strict reciprocal samplers
for the fair proposal, since `E[r | y] = 2`. With the exact reverse density
`1/2`, the test `min(1, r/2)` leaves `false` with probability `3/8` and `true`
with probability `1/2`, so the uniform target is not invariant. The first
sampler is not paired with the exact estimator (`unpaired_strict`): the step
needs the joint correspondence `Paired`, of which strict reciprocity is a
corollary.

Proofs are finite evaluations of Dirac sums. -/

namespace Problib.Inference.Necessity.Reciprocal

open Problib.Real Problib.Measure
open Problib.Inference.Necessity.Weighting (bools fair halfMass lintegral_fair fair_probability
  half_sum_ofRat half_sum_scale rationalWeight ofRat_congr skewed atTrue)
open Problib.Inference.Necessity.PseudoMarginal (pairs pairs_measurable)

public section

/-! ### The mixture and its meta kernel -/

/-- One half, as a weight. -/
@[expose] noncomputable def halfWeight : NNReal := rationalWeight (1 / 2) (by decide +kernel)

/-- The fair mixing density `m(u) = 1/2` against counting measure. -/
@[expose] noncomputable def mixingDensity (_ : Bool) : NNReal := halfWeight

/-- The component density `k(x | u)` at `(x, u)`: `u = true` returns `x = true`,
and `u = false` draws `x` fairly. -/
@[expose] noncomputable def componentDensity : Bool × Bool → NNReal
  | (true, true) => NNReal.one
  | (false, true) => NNReal.zero
  | (_, false) => halfWeight

/-- The meta kernel's density `r(u | x) = 1/2`, fair in `u` at every `x`. -/
@[expose] noncomputable def metaDensity (_ : Bool × Bool) : NNReal := halfWeight

/-- The meta kernel: a fair draw of `u` that ignores `x`. -/
@[expose] noncomputable def metaKernel : Kernel bools bools := Kernel.const bools (fair bools true false)

/-- RAVI's forward weight `r(u | x) / (m(u) k(x | u))`, read as zero where the
denominator vanishes. -/
@[expose] noncomputable def raviRatio (point : Bool × Bool) : NNReal :=
  NNReal.div (metaDensity point) (NNReal.mul (mixingDensity point.2) (componentDensity point))

/-- The joint draw of `(x, u)`: a fair choice between `u = true`, which returns
`x = true`, and `u = false`, which draws `x` fairly. -/
@[expose] noncomputable def joint : Measure pairs :=
  Measure.smul halfMass
    (Measure.add (Measure.dirac pairs (true, true)) (fair pairs (true, false) (false, false)))

theorem raviDraw_measurable :
    MeasurableMap pairs (Space.product bools weightSpace) (fun point => (point.1, raviRatio point)) :=
  fun _ => pairs_measurable _

/-- RAVI's forward weighted law: the joint draw, keeping `x` and its weight. -/
@[expose] noncomputable def raviLaw : Measure (Space.product bools weightSpace) :=
  joint.map (fun point => (point.1, raviRatio point)) raviDraw_measurable

/-- Unit mass at each of the two values. -/
@[expose] noncomputable def twoPoints : Measure bools :=
  Measure.add (Measure.dirac bools true) (Measure.dirac bools false)

/-- Unit mass at `true` and half mass at `false`. -/
@[expose] noncomputable def raviTarget : Measure bools :=
  Measure.add (Measure.dirac bools true) (Measure.smul halfMass (Measure.dirac bools false))

/-! ### The weights -/

private theorem div_ofRat (left right : Rat) (leftNonnegative : 0 ≤ left)
    (rightNonnegative : 0 ≤ right) (quotientNonnegative : 0 ≤ left / right) :
    NNReal.div (NNReal.ofRat left leftNonnegative) (NNReal.ofRat right rightNonnegative) =
      NNReal.ofRat (left / right) quotientNonnegative := by
  apply NNReal.ext
  rw [NNReal.toReal_div, NNReal.toReal_ofRat, NNReal.toReal_ofRat, NNReal.toReal_ofRat]
  exact (Construction.Dedekind.ofRat_div left right).symm

/-- Where `u = true` produced `x = true`, the weight is one. -/
theorem raviRatio_true_true : raviRatio (true, true) = NNReal.one := by
  show NNReal.div halfWeight (NNReal.mul halfWeight NNReal.one) = NNReal.one
  rw [halfWeight, rationalWeight, ← NNReal.ofRat_one, ← NNReal.ofRat_mul, div_ofRat _ _ _ _ (by decide +kernel)]
  exact NNReal.ofRat_congr (by decide +kernel)

/-- Where `u = false` was drawn, the weight is two at either `x`. -/
theorem raviRatio_false (value : Bool) :
    raviRatio (value, false) = rationalWeight 2 (by decide +kernel) := by
  cases value <;>
  · show NNReal.div halfWeight (NNReal.mul halfWeight halfWeight) = _
    rw [halfWeight, rationalWeight, ← NNReal.ofRat_mul, div_ofRat _ _ _ _ (by decide +kernel)]
    exact NNReal.ofRat_congr (by decide +kernel)

/-! ### Proper weighting -/

private theorem pairs_ennreal (function : Bool × Bool → ENNReal) :
    ENNRealMeasurable pairs function :=
  fun _ => pairs_measurable _

private theorem bools_ennreal (function : Bool → ENNReal) : ENNRealMeasurable bools function :=
  fun _ => Space.discrete_measurable _

/-- The joint draw is a probability. -/
theorem joint_probability : Measure.IsProbability joint := by
  constructor
  rw [joint, Measure.smul_apply_measurable _ _ pairs.univ,
    Measure.add_apply_measurable _ _ pairs.univ, Measure.dirac_apply_univ,
    (fair_probability pairs (true, false) (false, false)).univ_eq_one, ← ENNReal.ofRat_one]
  exact half_sum_ofRat 1 1 1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- Integrating against the joint draw. -/
theorem lintegral_joint (function : Bool × Bool → ENNReal) :
    lintegral joint function =
      ENNReal.mul halfMass (ENNReal.add (function (true, true))
        (ENNReal.mul halfMass (ENNReal.add (function (true, false)) (function (false, false))))) := by
  rw [joint, lintegral_smul_measure, lintegral_add_measure,
    lintegral_dirac _ _ (pairs_ennreal function), lintegral_fair _ _ _ (pairs_ennreal function)]

/-- Half of two is one. -/
private theorem half_two :
    ENNReal.mul halfMass (ENNReal.ofRat 2 (by decide +kernel)) = ENNReal.one := by
  rw [halfMass, ← ENNReal.ofRat_mul _ _ (by decide +kernel) (by decide +kernel), ← ENNReal.ofRat_one]
  exact ofRat_congr (by decide +kernel) _ _

/-- The weighted law's expectation of `v f(x)` is `f(true) + f(false)/2`. -/
theorem lintegral_raviLaw (function : Bool → ENNReal) :
    lintegral raviLaw (fun draw => ENNReal.mul (drawWeight draw) (function draw.1)) =
      ENNReal.add (function true) (ENNReal.mul halfMass (function false)) := by
  rw [raviLaw, lintegral_map _ _ _ (weighted_integrand_measurable (bools_ennreal function)),
    lintegral_joint]
  show ENNReal.mul halfMass (ENNReal.add
      (ENNReal.mul (ENNReal.finite (raviRatio (true, true))) (function true))
      (ENNReal.mul halfMass (ENNReal.add
        (ENNReal.mul (ENNReal.finite (raviRatio (true, false))) (function true))
        (ENNReal.mul (ENNReal.finite (raviRatio (false, false))) (function false))))) = _
  rw [raviRatio_true_true, raviRatio_false, raviRatio_false]
  show ENNReal.mul halfMass (ENNReal.add
      (ENNReal.mul ENNReal.one (function true))
      (ENNReal.mul halfMass (ENNReal.add
        (ENNReal.mul (ENNReal.ofRat 2 (by decide +kernel)) (function true))
        (ENNReal.mul (ENNReal.ofRat 2 (by decide +kernel)) (function false))))) = _
  -- `½ (a + ½ (2a + 2b)) = ½ (a + (a + b)) = ½ (2a + b) = a + ½ b`.
  have double : ∀ value : ENNReal, ENNReal.add value value =
      ENNReal.mul (ENNReal.ofRat 2 (by decide +kernel)) value := by
    intro value
    rw [ENNReal.mul_comm, ofRat_congr (show (2 : Rat) = 1 + 1 by decide +kernel) _
        (by decide +kernel), ENNReal.ofRat_add 1 1 (by decide +kernel) (by decide +kernel),
      ENNReal.ofRat_one, ENNReal.mul_add, ENNReal.mul_one]
  have halve : ∀ value : ENNReal,
      ENNReal.mul halfMass (ENNReal.mul (ENNReal.ofRat 2 (by decide +kernel)) value) = value := by
    intro value
    rw [← ENNReal.mul_assoc, half_two, ENNReal.one_mul]
  rw [ENNReal.one_mul, ENNReal.mul_add halfMass
      (ENNReal.mul (ENNReal.ofRat 2 (by decide +kernel)) (function true)), halve, halve,
    ← ENNReal.add_assoc, double, ENNReal.mul_add, halve]

/-! ### Necessity: RAVI without its support condition -/

/-- RAVI's forward weighted law, with a meta kernel that puts mass where the
mixture cannot produce the value, is properly weighted for
`δ_true + (1/2)δ_false` and so not for counting measure on the two values. By
hand:
`E[v f(x)] = (3/4)(4/3) f(true) + (1/4) 2 f(false) = f(true) + f(false)/2`. -/
theorem ravi_support_necessary :
    (∀ input, Measure.IsProbability (metaKernel input)) ∧
      ProperlyWeighted raviTarget raviLaw ∧ ¬ProperlyWeighted twoPoints raviLaw := by
  have properlyWeighted : ProperlyWeighted raviTarget raviLaw := by
    refine properlyWeighted_iff_lintegral.mpr ⟨joint_probability.map _ _, fun function _ => ?_⟩
    rw [lintegral_raviLaw, raviTarget, lintegral_add_measure, lintegral_smul_measure,
      lintegral_dirac _ _ (bools_ennreal function), lintegral_dirac _ _ (bools_ennreal function)]
  refine ⟨fun input => ?_, properlyWeighted, fun counting => ?_⟩
  · rw [metaKernel, Kernel.const_apply]
    exact fair_probability bools true false
  have atUniv : raviTarget Set.univ = twoPoints Set.univ := by
    rw [properlyWeighted_target_unique properlyWeighted counting]
  rw [raviTarget, twoPoints, Measure.add_apply_measurable _ _ bools.univ,
    Measure.add_apply_measurable _ _ bools.univ, Measure.smul_apply_measurable _ _ bools.univ,
    Measure.dirac_apply_univ, Measure.dirac_apply_univ, ENNReal.mul_one, halfMass,
    ← ENNReal.ofRat_one, ← ENNReal.ofRat_add, ← ENNReal.ofRat_add] at atUniv
  have bound : ENNReal.le (ENNReal.ofRat (1 + 1) (by decide +kernel))
      (ENNReal.ofRat (1 + 1 / 2) (by decide +kernel)) := by
    rw [atUniv]
    exact ENNReal.le_refl _
  exact absurd ((ENNReal.ofRat_le_iff _ _ _ _).mp bound) (by decide +kernel)

/-! ### Necessity: a reciprocal sampler need not draw from its target -/

/-- The density of `skewed` against counting measure: `1/4` at `false` and
`3/4` at `true`. -/
@[expose] noncomputable def skewedWeight : Bool → NNReal
  | false => rationalWeight (1 / 4) (by decide +kernel)
  | true => rationalWeight (3 / 4) (by decide +kernel)

/-- Fair draws, each at weight two. -/
@[expose] noncomputable def doubledFair : Measure (Space.product bools weightSpace) :=
  fair (Space.product bools weightSpace)
    (false, rationalWeight 2 (by decide +kernel)) (true, rationalWeight 2 (by decide +kernel))

private theorem ofRat_ne_zero (value : Rat) (nonnegative : 0 ≤ value) (positive : ¬value ≤ 0) :
    ENNReal.ofRat value nonnegative ≠ ENNReal.zero := by
  intro zero
  have bound : ENNReal.le (ENNReal.ofRat value nonnegative) (ENNReal.ofRat 0 (by decide +kernel)) := by
    rw [ENNReal.ofRat_zero, zero]
    exact ENNReal.le_refl _
  exact positive ((ENNReal.ofRat_le_iff _ _ _ _).mp bound)

/-- Integrating against the skewed target. -/
private theorem lintegral_skewed (function : Bool → ENNReal) :
    lintegral skewed function =
      ENNReal.add (ENNReal.mul (ENNReal.ofRat (1 / 4) (by decide +kernel)) (function false))
        (ENNReal.mul (ENNReal.ofRat (3 / 4) (by decide +kernel)) (function true)) := by
  rw [skewed, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac _ _ (bools_ennreal function), lintegral_dirac _ _ (bools_ennreal function)]

/-- The skewed target has density `skewedWeight` against counting measure. -/
theorem skewed_isDensity :
    Measure.IsDensity skewed twoPoints (fun value => ENNReal.finite (skewedWeight value)) := by
  refine (Measure.eq_iff_lintegral _ _).mpr fun function _ => ?_
  rw [lintegral_skewed, lintegral_withDensity _ (bools_ennreal _) (bools_ennreal function),
    twoPoints, lintegral_add_measure, lintegral_dirac _ _ (bools_ennreal _),
    lintegral_dirac _ _ (bools_ennreal _)]
  exact ENNReal.add_comm _ _

/-- Counting measure, restricted to where the skewed density is positive, is
counting measure. -/
theorem twoPoints_restrict_skewed :
    (twoPoints.restrict fun value => ENNReal.finite (skewedWeight value) ≠ ENNReal.zero) =
      twoPoints := by
  have everywhere : (fun value => ENNReal.finite (skewedWeight value) ≠ ENNReal.zero) =
      Set.univ := by
    funext value
    refine propext ⟨fun _ => trivial, fun _ => ?_⟩
    cases value
    · exact ofRat_ne_zero (1 / 4) (by decide +kernel) (by decide +kernel)
    · exact ofRat_ne_zero (3 / 4) (by decide +kernel) (by decide +kernel)
  rw [everywhere, Measure.restrict_univ]

/-- Fair draws at weight two are properly weighted for counting measure. -/
theorem doubledFair_properlyWeighted : ProperlyWeighted twoPoints doubledFair := by
  refine properlyWeighted_iff_lintegral.mpr ⟨fair_probability _ _ _, fun function measurable => ?_⟩
  rw [doubledFair, lintegral_fair _ _ _ (weighted_integrand_measurable measurable), twoPoints,
    lintegral_add_measure, lintegral_dirac _ _ measurable, lintegral_dirac _ _ measurable]
  show ENNReal.mul halfMass (ENNReal.add
      (ENNReal.mul (ENNReal.ofRat 2 (by decide +kernel)) (function false))
      (ENNReal.mul (ENNReal.ofRat 2 (by decide +kernel)) (function true))) = _
  rw [ENNReal.mul_add, ← ENNReal.mul_assoc, ← ENNReal.mul_assoc, half_two, ENNReal.one_mul,
    ENNReal.one_mul]
  exact ENNReal.add_comm _ _

/-- Fair draws at weight two reciprocally weigh `skewed` against counting
measure, but they are not a strict reciprocal sampler for it: the drawn point
is `true` with probability `1/2`, where `skewed` puts `3/4`. -/
theorem reciprocal_marginal_necessary :
    ReciprocallyWeighted twoPoints skewed doubledFair ∧
      ¬StrictReciprocal twoPoints skewed doubledFair := by
  refine ⟨⟨fun value => ENNReal.finite (skewedWeight value), bools_ennreal _, skewed_isDensity,
    finite_ae_of_code twoPoints skewedWeight, ?_⟩, fun strict => ?_⟩
  · rw [twoPoints_restrict_skewed]
    exact doubledFair_properlyWeighted
  · have atTrueMass : lintegral (doubledFair.map Prod.fst
        (Space.first_measurable bools weightSpace)) atTrue = lintegral skewed atTrue := by
      rw [strict.marginal]
    rw [lintegral_map _ _ _ (bools_ennreal atTrue), doubledFair,
      lintegral_fair _ _ _ ((bools_ennreal atTrue).comp (Space.first_measurable bools weightSpace)),
      lintegral_skewed] at atTrueMass
    change ENNReal.mul halfMass (ENNReal.add ENNReal.zero ENNReal.one) =
      ENNReal.add (ENNReal.mul _ ENNReal.zero) (ENNReal.mul _ ENNReal.one) at atTrueMass
    rw [ENNReal.zero_add, ENNReal.mul_one, ENNReal.mul_zero, ENNReal.zero_add, ENNReal.mul_one,
      halfMass] at atTrueMass
    have bound : ENNReal.le (ENNReal.ofRat (3 / 4) (by decide +kernel))
        (ENNReal.ofRat (1 / 2) (by decide +kernel)) := by
      rw [atTrueMass]
      exact ENNReal.le_refl _
    exact absurd ((ENNReal.ofRat_le_iff _ _ _ _).mp bound) (by decide +kernel)

/-! ### Necessity: strict reciprocity does not pair a sampler with its estimator -/

/-- A weight's singleton is measurable. -/
theorem weight_singleton_measurable (weight : NNReal) :
    weightSpace.Measurable (Set.singleton weight) := by
  have preimage := (finite_weight_measurable (MeasurableMap.identity weightSpace)).singleton
    (ENNReal.finite weight)
  have same : Set.singleton weight = Set.preimage (fun value : NNReal => ENNReal.finite value)
      (ennrealSingleton (ENNReal.finite weight)) := by
    funext value
    exact propext ⟨fun equal => congrArg ENNReal.finite equal,
      fun equal => ENNReal.finite_injective equal⟩
  rw [same]
  exact preimage

/-- A weighted draw's singleton is measurable. -/
theorem draw_singleton_measurable (draw : Bool × NNReal) :
    (Space.product bools weightSpace).Measurable (Set.singleton draw) := by
  have product := Space.product_set_measurable bools weightSpace
    (Space.discrete_measurable (Set.singleton draw.1)) (weight_singleton_measurable draw.2)
  have same : Set.singleton draw = Set.product (Set.singleton draw.1) (Set.singleton draw.2) := by
    funext value
    exact propext ⟨fun equal => ⟨congrArg Prod.fst equal, congrArg Prod.snd equal⟩,
      fun both => Prod.ext both.1 both.2⟩
  rw [same]
  exact product

/-- Integrating against a fair choice of two weighted draws averages the
integrand there. Singletons are measurable, so the integrand need not be. -/
private theorem lintegral_fair_draws (first second : Bool × NNReal)
    (function : Bool × NNReal → ENNReal) :
    lintegral (fair (Space.product bools weightSpace) first second) function =
      ENNReal.mul halfMass (ENNReal.add (function first) (function second)) := by
  rw [fair, lintegral_smul_measure, lintegral_add_measure,
    lintegral_dirac_of_measurable_singleton _ _ _ (draw_singleton_measurable first),
    lintegral_dirac_of_measurable_singleton _ _ _ (draw_singleton_measurable second)]

/-- Half of a value counted twice is the value. -/
private theorem half_double (value : ENNReal) :
    ENNReal.mul halfMass (ENNReal.add value value) = value := by
  have double : ENNReal.add value value =
      ENNReal.mul (ENNReal.ofRat 2 (by decide +kernel)) value := by
    rw [ENNReal.mul_comm, ofRat_congr (show (2 : Rat) = 1 + 1 by decide +kernel) _
        (by decide +kernel), ENNReal.ofRat_add 1 1 (by decide +kernel) (by decide +kernel),
      ENNReal.ofRat_one, ENNReal.mul_add, ENNReal.mul_one]
  rw [double, ← ENNReal.mul_assoc, half_two, ENNReal.one_mul]

/-- At `x = false` the reciprocal sampler draws `y` fairly and, independently,
`r = 1` or `r = 3`. -/
@[expose] noncomputable def splitSampler : Measure (Space.product bools weightSpace) :=
  Measure.smul halfMass (Measure.add
    (fair (Space.product bools weightSpace)
      (false, rationalWeight 1 (by decide +kernel)) (false, rationalWeight 3 (by decide +kernel)))
    (fair (Space.product bools weightSpace)
      (true, rationalWeight 1 (by decide +kernel)) (true, rationalWeight 3 (by decide +kernel))))

/-- Integrating against the split sampler. -/
private theorem lintegral_splitSampler (function : Bool × NNReal → ENNReal) :
    lintegral splitSampler function =
      ENNReal.mul halfMass (ENNReal.add
        (ENNReal.mul halfMass (ENNReal.add (function (false, rationalWeight 1 (by decide +kernel)))
          (function (false, rationalWeight 3 (by decide +kernel)))))
        (ENNReal.mul halfMass (ENNReal.add (function (true, rationalWeight 1 (by decide +kernel)))
          (function (true, rationalWeight 3 (by decide +kernel)))))) := by
  rw [splitSampler, lintegral_smul_measure, lintegral_add_measure, lintegral_fair_draws,
    lintegral_fair_draws]

/-- The fair proposal has density one half against counting measure. -/
theorem fair_isDensity :
    Measure.IsDensity (fair bools false true) twoPoints
      (fun _ => ENNReal.finite halfWeight) := by
  refine (Measure.eq_iff_lintegral _ _).mpr fun function _ => ?_
  rw [lintegral_fair _ _ _ (bools_ennreal function),
    lintegral_withDensity _ (bools_ennreal _) (bools_ennreal function), twoPoints,
    lintegral_add_measure, lintegral_dirac _ _ (bools_ennreal _),
    lintegral_dirac _ _ (bools_ennreal _), ENNReal.mul_add]
  exact ENNReal.add_comm _ _

/-- A law properly weighted for counting measure whose drawn point is fair is a
strict reciprocal sampler for the fair proposal. -/
theorem strict_of_fair {weighted : Measure (Space.product bools weightSpace)}
    (properlyWeighted : ProperlyWeighted twoPoints weighted)
    (marginal : weighted.map Prod.fst (Space.first_measurable bools weightSpace) =
      fair bools false true) :
    StrictReciprocal twoPoints (fair bools false true) weighted := by
  have everywhere : (fun _ : Bool => ENNReal.finite halfWeight ≠ ENNReal.zero) = Set.univ := by
    funext value
    exact propext ⟨fun _ => trivial, fun _ => ofRat_ne_zero (1 / 2) (by decide +kernel)
      (by decide +kernel)⟩
  refine ⟨⟨fun _ => ENNReal.finite halfWeight, bools_ennreal _, fair_isDensity,
    finite_ae_of_code twoPoints (fun _ => halfWeight), ?_⟩, marginal⟩
  rw [everywhere, Measure.restrict_univ]
  exact properlyWeighted

/-- The split sampler is properly weighted for counting measure: its weight's
conditional mean is two at either `y`. -/
theorem splitSampler_properlyWeighted : ProperlyWeighted twoPoints splitSampler := by
  refine properlyWeighted_iff_lintegral.mpr ⟨⟨?_⟩, fun function measurable => ?_⟩
  · rw [splitSampler, Measure.smul_apply_measurable _ _ (Space.product bools weightSpace).univ,
      Measure.add_apply_measurable _ _ (Space.product bools weightSpace).univ,
      (fair_probability _ _ _).univ_eq_one, (fair_probability _ _ _).univ_eq_one]
    exact half_double ENNReal.one
  rw [lintegral_splitSampler, twoPoints, lintegral_add_measure, lintegral_dirac _ _ measurable,
    lintegral_dirac _ _ measurable]
  show ENNReal.mul halfMass (ENNReal.add
      (ENNReal.mul halfMass (ENNReal.add
        (ENNReal.mul (ENNReal.ofRat 1 (by decide +kernel)) (function false))
        (ENNReal.mul (ENNReal.ofRat 3 (by decide +kernel)) (function false))))
      (ENNReal.mul halfMass (ENNReal.add
        (ENNReal.mul (ENNReal.ofRat 1 (by decide +kernel)) (function true))
        (ENNReal.mul (ENNReal.ofRat 3 (by decide +kernel)) (function true))))) = _
  rw [half_sum_scale, half_sum_scale, half_sum_ofRat 1 3 2 _ _ (by decide +kernel)
      (by decide +kernel), ENNReal.mul_add, ← ENNReal.mul_assoc, ← ENNReal.mul_assoc, half_two,
    ENNReal.one_mul, ENNReal.one_mul]
  exact ENNReal.add_comm _ _

/-- The split sampler's drawn point is fair. -/
theorem splitSampler_marginal :
    splitSampler.map Prod.fst (Space.first_measurable bools weightSpace) =
      fair bools false true := by
  refine (Measure.eq_iff_lintegral _ _).mpr fun function _ => ?_
  rw [lintegral_map _ _ _ (bools_ennreal function), lintegral_splitSampler,
    lintegral_fair _ _ _ (bools_ennreal function)]
  show ENNReal.mul halfMass (ENNReal.add
      (ENNReal.mul halfMass (ENNReal.add (function false) (function false)))
      (ENNReal.mul halfMass (ENNReal.add (function true) (function true)))) = _
  rw [half_double, half_double]

/-- Fair draws at weight two have a fair drawn point. -/
theorem doubledFair_marginal :
    doubledFair.map Prod.fst (Space.first_measurable bools weightSpace) =
      fair bools false true := by
  refine (Measure.eq_iff_lintegral _ _).mpr fun function _ => ?_
  rw [lintegral_map _ _ _ (bools_ennreal function), doubledFair, lintegral_fair_draws,
    lintegral_fair _ _ _ (bools_ennreal function)]

/-- The naive test's acceptance probability at a reciprocal weight `r`:
`min(1, r · wb)`, where `wb = 1/2` is the exact reverse proposal density and
the uniform target's weights cancel. -/
@[expose] noncomputable def naiveAcceptance (weight : NNReal) : ENNReal :=
  ENNReal.min ENNReal.one (ENNReal.finite (NNReal.mul weight halfWeight))

/-- The naive step's probability of leaving `current`, when its proposal comes
from the reciprocal sampler drawn there. -/
@[expose] noncomputable def naiveMove (current : Bool)
    (sampler : Measure (Space.product bools weightSpace)) : ENNReal :=
  lintegral sampler fun draw => if draw.1 = current then ENNReal.zero else naiveAcceptance draw.2

private theorem naiveAcceptance_ofRat (value : Rat) (nonnegative : 0 ≤ value) :
    naiveAcceptance (rationalWeight value nonnegative) =
      ENNReal.min ENNReal.one (ENNReal.ofRat (value * (1 / 2))
        (Rat.mul_nonneg nonnegative (by decide +kernel))) := by
  unfold naiveAcceptance halfWeight rationalWeight
  rw [← NNReal.ofRat_mul]
  rfl

private theorem naiveAcceptance_light : naiveAcceptance (rationalWeight 1 (by decide +kernel)) =
    halfMass := by
  rw [naiveAcceptance_ofRat, ENNReal.min_eq_right]
  · exact ofRat_congr (by decide +kernel) _ _
  · rw [← ENNReal.ofRat_one]
    exact (ENNReal.ofRat_le_iff _ _ _ _).mpr (by decide +kernel)

private theorem naiveAcceptance_heavy (value : Rat) (nonnegative : 0 ≤ value)
    (heavy : 1 ≤ value * (1 / 2)) :
    naiveAcceptance (rationalWeight value nonnegative) = ENNReal.one := by
  rw [naiveAcceptance_ofRat, ENNReal.min_eq_left]
  rw [← ENNReal.ofRat_one]
  exact (ENNReal.ofRat_le_iff _ _ _ _).mpr heavy

/-- Counterexample B. The proposal is fair at either current value. At
`x = false` the reciprocal sampler is `splitSampler` and at `x = true` it is
`doubledFair`, and both are strict reciprocal samplers for the proposal:
`E[r | y] = 2 = 1/q(y)`. The exact reverse density `wb = 1/2` is an unbiased
estimate. The naive test `min(1, r · wb)` leaves `false` with probability `3/8`
and `true` with probability `1/2`, so the uniform target, which a two-state
step keeps only when the two are equal, is not invariant. The split sampler is
not paired with the exact estimator: its forward weights `1/r` are `1` and
`1/3`, with mean `2/3`, where the paired law's weight is `1/2`. -/
theorem unpaired_strict :
    StrictReciprocal twoPoints (fair bools false true) splitSampler ∧
      StrictReciprocal twoPoints (fair bools false true) doubledFair ∧
      naiveMove false splitSampler = ENNReal.ofRat (3 / 8) (by decide +kernel) ∧
      naiveMove true doubledFair = halfMass ∧
      naiveMove false splitSampler ≠ naiveMove true doubledFair ∧
      ¬Paired twoPoints (fair bools false true) (fun _ => ENNReal.finite halfWeight)
        (Kernel.deterministic (fun _ => halfWeight) (MeasurableMap.constant bools weightSpace halfWeight))
        (Kernel.IsSFinite.deterministic _ _)
        (splitSampler.map (fun draw => (draw.1, NNReal.div NNReal.one draw.2))
          (reciprocal_draw_measurable bools)) := by
  have leaving : naiveMove false splitSampler = ENNReal.ofRat (3 / 8) (by decide +kernel) := by
    rw [naiveMove, lintegral_splitSampler]
    change ENNReal.mul halfMass (ENNReal.add
        (ENNReal.mul halfMass (ENNReal.add ENNReal.zero ENNReal.zero))
        (ENNReal.mul halfMass (ENNReal.add (naiveAcceptance (rationalWeight 1 (by decide +kernel)))
          (naiveAcceptance (rationalWeight 3 (by decide +kernel)))))) = _
    rw [naiveAcceptance_light, naiveAcceptance_heavy 3 _ (by decide +kernel), ENNReal.add_zero,
      ENNReal.mul_zero, ENNReal.zero_add, halfMass, ← ENNReal.ofRat_one, ← ENNReal.ofRat_add,
      ← ENNReal.ofRat_mul, ← ENNReal.ofRat_mul]
    exact ofRat_congr (by decide +kernel) _ _
  have returning : naiveMove true doubledFair = halfMass := by
    rw [naiveMove, doubledFair, lintegral_fair_draws]
    change ENNReal.mul halfMass (ENNReal.add
        (naiveAcceptance (rationalWeight 2 (by decide +kernel))) ENNReal.zero) = _
    rw [naiveAcceptance_heavy 2 _ (by decide +kernel), ENNReal.add_zero, ENNReal.mul_one]
  refine ⟨strict_of_fair splitSampler_properlyWeighted splitSampler_marginal,
    strict_of_fair doubledFair_properlyWeighted doubledFair_marginal, leaving, returning,
    fun same => ?_, fun paired => ?_⟩
  · rw [leaving, returning, halfMass] at same
    have bound : ENNReal.le (ENNReal.ofRat (1 / 2) (by decide +kernel))
        (ENNReal.ofRat (3 / 8) (by decide +kernel)) := by
      rw [same]
      exact ENNReal.le_refl _
    exact absurd ((ENNReal.ofRat_le_iff _ _ _ _).mp bound) (by decide +kernel)
  · -- The forward weight's mean differs: `2/3` on the split sampler, `1/2` on the paired law.
    have weightMean := congrArg (fun weighted => lintegral weighted drawWeight) paired.joint
    change lintegral (splitSampler.map _ _) drawWeight =
      lintegral (extendedTarget _ _ _ _) drawWeight at weightMean
    rw [lintegral_map _ _ _ (drawWeight_measurable bools), lintegral_splitSampler, extendedTarget,
      lintegral_withDensity _ (finite_weight_measurable (Space.second_measurable bools weightSpace))
        (drawWeight_measurable bools),
      lintegral_semiproduct _ _ _ (ENNRealMeasurable.mul
        (finite_weight_measurable (Space.second_measurable bools weightSpace))
        (drawWeight_measurable bools)),
      twoPoints, lintegral_add_measure, lintegral_dirac _ _ (bools_ennreal _),
      lintegral_dirac _ _ (bools_ennreal _)] at weightMean
    change ENNReal.mul halfMass (ENNReal.add
        (ENNReal.mul halfMass (ENNReal.add
          (ENNReal.finite (NNReal.div NNReal.one (rationalWeight 1 (by decide +kernel))))
          (ENNReal.finite (NNReal.div NNReal.one (rationalWeight 3 (by decide +kernel))))))
        (ENNReal.mul halfMass (ENNReal.add
          (ENNReal.finite (NNReal.div NNReal.one (rationalWeight 1 (by decide +kernel))))
          (ENNReal.finite (NNReal.div NNReal.one (rationalWeight 3 (by decide +kernel))))))) =
      ENNReal.add
        (lintegral (Measure.dirac weightSpace halfWeight) fun weight =>
          ENNReal.mul (ENNReal.finite weight) (ENNReal.finite weight))
        (lintegral (Measure.dirac weightSpace halfWeight) fun weight =>
          ENNReal.mul (ENNReal.finite weight) (ENNReal.finite weight)) at weightMean
    rw [lintegral_dirac_of_measurable_singleton _ _ _ (weight_singleton_measurable halfWeight),
      half_double, rationalWeight, rationalWeight, ← NNReal.ofRat_one, div_ofRat 1 1 _ _ (by decide +kernel),
      div_ofRat 1 3 _ _ (by decide +kernel), halfWeight, rationalWeight] at weightMean
    change ENNReal.mul halfMass (ENNReal.add (ENNReal.ofRat (1 / 1) (by decide +kernel))
        (ENNReal.ofRat (1 / 3) (by decide +kernel))) =
      ENNReal.add (ENNReal.mul halfMass halfMass) (ENNReal.mul halfMass halfMass) at weightMean
    rw [halfMass, ← ENNReal.ofRat_add, ← ENNReal.ofRat_mul, ← ENNReal.ofRat_mul,
      ← ENNReal.ofRat_add] at weightMean
    have bound : ENNReal.le (ENNReal.ofRat (1 / 2 * (1 / 1 + 1 / 3)) (by decide +kernel))
        (ENNReal.ofRat (1 / 2 * (1 / 2) + 1 / 2 * (1 / 2)) (by decide +kernel)) := by
      rw [weightMean]
      exact ENNReal.le_refl _
    exact absurd ((ENNReal.ofRat_le_iff _ _ _ _).mp bound) (by decide +kernel)

end

end Problib.Inference.Necessity.Reciprocal
