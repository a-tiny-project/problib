import Problib.Inference.Derivative.Continuous.Estimate
import Problib.Analysis.Categorical
import Problib.Measure.Measurability
import Problib.Real.Grind
import Problib.Analysis.Real.Leibniz
import Problib.Analysis.Real.Sided

set_option autoImplicit false

/-! The interchange theorem: one-sided and first order.

Differentiating an expectation means exchanging a derivative with an integral.
The classical Leibniz rule does so for a family of integrands on one law, each
differentiable in the parameter and with dominated difference quotients. A
derivative estimator needs the exchange in a weaker form, because its samples
can have kinks and its family can be unbiased only to first order.

A derivative estimator is built from a family of estimators `h(ε, ·)` on one
law `R` that does not move with the step `ε`. Each member estimates the
objective at `ε`, and the estimator reads the right derivative of each sample
at zero. Pathwise transport, score reweighting, point masses, measure-valued
derivatives, phantom estimators, ADEV rules and GradInf plans are its
specializations: each is one way of putting the perturbed program on a single
probability space.

`Estimates.interchange_right` takes three premises on a step interval `[0, δ)`:

- **Local:** the member at `ε` has certified mean `J(ε) + e(ε)`, with
  `e(0) = 0` and `e(ε)/ε → 0` from the right. Unbiasedness is needed only to
  first order.
- **Directional AD:** almost every sample has right derivative `g(ω)` at zero.
- **Domination:** almost every sample satisfies `|h(ε, ω) - h(0, ω)| ≤ ε·G(ω)`
  at every positive step below the radius, with `G` integrable.
Then `g` has a certified mean, and that mean is the objective's right
derivative. `Estimates.interchange` additionally takes a two-sided objective
derivative and identifies its slope with the right mean by uniqueness. This
regularity premise belongs to the answer boundary, rather than the right
soundness result.

The samples and the objective need only one-sided derivatives for the right
result. A kink in every sample, as in a maximal coupling, is allowed.
The proof reads the right quotient at `|d|`, which turns the one-sided limit
into the punctured limit that dominated convergence consumes.

`Estimates.interchange_dominated` is the classical case at either side:
dominated difference quotients and pointwise derivatives at a side derive the
objective's derivative at that side, by the Leibniz rule of
`Problib.Analysis.Real.Leibniz`, so it assumes no regularity. At the two-sided
side it is the classical rule. `Estimates.interchange` keeps the two-sided
objective derivative as a premise for families whose samples are one-sided:
`Coupling` has samples with no two-sided derivative and a smooth objective.
A right-sided family does not prove a two-sided objective derivative: `Kink`
has a dominated family whose objective `|ε|` has none. -/

namespace Problib.Inference.Derivative.Continuous

open Problib.Real Problib.Real.Construction.Dedekind
open Problib.Measure Problib.Measure.Real
open Problib.Analysis.Real

universe u

variable {Outcome : Type u} {space : Space Outcome}

/-- The values of `function` at positive steps converge to `limit` as the step
falls to zero. -/
def ApproachesFromRight (function : selection.Carrier → selection.Carrier)
    (limit : selection.Carrier) : Prop :=
  ∀ epsilon : selection.Carrier, lt zero epsilon →
    ∃ radius : selection.Carrier, lt zero radius ∧
      ∀ step : selection.Carrier, lt zero step → lt step radius →
        lt (abs (sub (function step) limit)) epsilon

/-- The right derivative: the limit of the secant over positive
displacements. -/
def HasRightDerivative (function : selection.Carrier → selection.Carrier)
    (point derivative : selection.Carrier) : Prop :=
  ApproachesFromRight (secant function point) derivative

/-- A right limit, read at the size of a displacement, is a punctured limit. -/
theorem ApproachesFromRight.atSize {function : selection.Carrier → selection.Carrier}
    {limit : selection.Carrier} (right : ApproachesFromRight function limit) :
    Approaches (fun displacement => function (abs displacement)) limit := by
  intro epsilon positive
  obtain ⟨radius, radiusPositive, close⟩ := right epsilon positive
  exact ⟨radius, radiusPositive, fun displacement nonzero small =>
    close (abs displacement) (abs_positive_of_nonzero nonzero) small⟩

/-- The positive-step and absolute-step statements name the same right limit. -/
theorem approachesOn_right_iff {function : selection.Carrier → selection.Carrier}
    {limit : selection.Carrier} :
    ApproachesOn .right function limit ↔ ApproachesFromRight function limit := by
  refine ⟨?_, ApproachesFromRight.atSize⟩
  intro approaches epsilon positive
  obtain ⟨radius, radiusPositive, close⟩ := approaches epsilon positive
  refine ⟨radius, radiusPositive, fun step stepPositive small => ?_⟩
  have nonzero : step ≠ zero := fun vanished =>
    lt_irrefl zero (by rwa [vanished] at stepPositive)
  simpa only [Side.along, abs_of_nonnegative stepPositive.left] using
    close step nonzero (by rwa [abs_of_nonnegative stepPositive.left])

/-- Right derivatives use one limit contract, whether the step is positive or
the size of a punctured displacement. -/
theorem hasDerivativeOn_right_iff {function : selection.Carrier → selection.Carrier}
    {point derivative : selection.Carrier} :
    HasDerivativeOn .right function point derivative ↔
      HasRightDerivative function point derivative :=
  approachesOn_right_iff

/-- A derivative is a right derivative. -/
theorem hasRightDerivative_of_hasDerivative
    {function : selection.Carrier → selection.Carrier} {point derivative : selection.Carrier}
    (differentiable : HasDerivative function point derivative) :
    HasRightDerivative function point derivative := by
  intro epsilon positive
  obtain ⟨radius, radiusPositive, close⟩ := differentiable epsilon positive
  refine ⟨radius, radiusPositive, fun step stepPositive small => ?_⟩
  have nonzero : step ≠ zero := fun vanished =>
    lt_irrefl zero (by rwa [vanished] at stepPositive)
  exact close step nonzero (by rwa [abs_of_nonnegative stepPositive.left])

/-- An error that vanishes identically is small to first order. -/
private theorem noError_small :
    ApproachesFromRight (fun step => div ((fun _ => zero) step) step) zero := by
  intro epsilon positive
  refine ⟨one, one_positive, fun step _ _ => ?_⟩
  show lt (abs (sub (div zero step) zero)) epsilon
  rwa [zero_div, sub_self, abs_zero]

/-- The size of a measurable real map is measurable. -/
private theorem abs_measurable' {function : Outcome → selection.Carrier}
    (measurable : MeasurableMap space borel function) :
    MeasurableMap space borel fun outcome => abs (function outcome) := by
  classical
  have branches : MeasurableMap space borel fun outcome =>
      @ite selection.Carrier (le zero (function outcome)) (Classical.propDecidable _)
        (function outcome) (neg (function outcome)) :=
    measurable_piecewise (measurable_le (MeasurableMap.constant space borel zero) measurable)
      measurable (MeasurableMap.comp neg_measurable measurable)
  have same : (fun outcome => abs (function outcome)) = fun outcome =>
      @ite selection.Carrier (le zero (function outcome)) (Classical.propDecidable _)
        (function outcome) (neg (function outcome)) := by
    funext outcome
    by_cases nonnegative : le zero (function outcome)
    · rw [abs_of_nonnegative nonnegative, ite_eq_left nonnegative]
    · rw [abs_of_nonpositive (le_of_lt (lt_of_not_le nonnegative)),
        ite_eq_right nonnegative]
  rw [same]
  intro set measurableSet
  exact branches measurableSet

namespace Estimates

/-- Dominated right quotients establish the objective's right derivative and
its certified mean without assuming objective regularity. -/
theorem interchange_right {law : Measure space}
    {family : selection.Carrier → Outcome → selection.Carrier}
    {objective error : selection.Carrier → selection.Carrier}
    {tangent dominator : Outcome → selection.Carrier}
    {radius dominatorValue : selection.Carrier}
    (radiusPositive : lt zero radius)
    (unbiased : ∀ step, le zero step → lt step radius →
      HasRealIntegral law (family step) (add (objective step) (error step)))
    (errorAtZero : error zero = zero)
    (errorSmall : ApproachesFromRight (fun step => div (error step) step) zero)
    (sampleDerivative : law.AE fun outcome =>
      HasRightDerivative (fun step => family step outcome) zero (tangent outcome))
    (tangentMeasurable : MeasurableMap space borel tangent)
    (lipschitz : law.AE fun outcome => ∀ step, lt zero step → lt step radius →
      le (abs (sub (family step outcome) (family zero outcome)))
        (mul step (dominator outcome)))
    (dominatorIntegral : HasRealIntegral law dominator dominatorValue) :
    ∃ slope, Estimates law (family zero) tangent (objective zero) slope ∧
      HasDerivativeOn .right objective zero slope := by
  classical
  have primal : HasRealIntegral law (family zero) (objective zero) := by
    have primal := unbiased zero (le_refl zero) radiusPositive
    rwa [errorAtZero, add_zero] at primal
  obtain ⟨exceptional, exceptionalMeasurable, exceptionalNull, outside⟩ :=
    (sampleDerivative.and lipschitz).exists_null_exception
  have almost : ∀ {first second : Outcome → selection.Carrier},
      (∀ outcome, ¬exceptional outcome → first outcome = second outcome) →
        law.AE fun outcome => first outcome = second outcome :=
    fun agree => exceptionalNull.mono fun {outcome} failure =>
      Classical.byContradiction fun clear => failure (agree outcome clear)
  -- The right quotient at `|d|`, set to zero on the exceptional null set.
  let quotient := fun (displacement : selection.Carrier) (outcome : Outcome) =>
    if exceptional outcome then zero
    else secant (fun step => family step outcome) zero (abs displacement)
  let limit := fun outcome => if exceptional outcome then zero else tangent outcome
  let bound := fun outcome => if exceptional outcome then zero else dominator outcome
  have boundIntegral : HasRealIntegral law bound dominatorValue :=
    dominatorIntegral.congr_ae
      (MeasurableMap.ite exceptionalMeasurable (MeasurableMap.constant _ _ zero)
        dominatorIntegral.measurable)
      (almost fun outcome clear => (ite_eq_right clear).symm)
  have inside : ∀ displacement, displacement ≠ zero → lt (abs displacement) radius →
      lt zero (abs displacement) ∧ abs displacement ≠ zero :=
    fun displacement nonzero _ => ⟨abs_positive_of_nonzero nonzero,
      fun vanished => nonzero (abs_eq_zero_iff.mp vanished)⟩
  have integrals : ∀ displacement, displacement ≠ zero → lt (abs displacement) radius →
      HasRealIntegral law (quotient displacement)
        (add (secant objective zero (abs displacement))
          (div (error (abs displacement)) (abs displacement))) := by
    intro displacement nonzero small
    have scaled := ((unbiased _ (abs_nonnegative displacement) small).sub
      (unbiased zero (le_refl zero) radiusPositive)).smul (inverse (abs displacement))
    have valueEqual : mul (inverse (abs displacement))
        (sub (add (objective (abs displacement)) (error (abs displacement)))
          (add (objective zero) (error zero))) =
        add (secant objective zero (abs displacement))
          (div (error (abs displacement)) (abs displacement)) := by
      rw [errorAtZero]
      simp only [secant, zero_add]
      real_grind
    rw [valueEqual] at scaled
    have plain := scaled.congr
      (g := fun outcome => secant (fun step => family step outcome) zero (abs displacement))
      fun outcome => by
        show _ = div (sub (family (add zero (abs displacement)) outcome) (family zero outcome))
          (abs displacement)
        rw [zero_add, div_eq_mul_inverse, mul_comm]
    exact HasRealIntegral.congr_ae
      (second := quotient displacement) plain
      (MeasurableMap.ite exceptionalMeasurable (MeasurableMap.constant _ _ zero)
        plain.measurable)
      (almost fun outcome clear => (ite_eq_right clear).symm)
  have dominated : ∀ displacement, displacement ≠ zero → lt (abs displacement) radius →
      ∀ outcome, le (abs (quotient displacement outcome)) (bound outcome) := by
    intro displacement nonzero small outcome
    by_cases excluded : exceptional outcome
    · show le (abs (if exceptional outcome then zero else _))
        (if exceptional outcome then zero else _)
      simp only [ite_eq_left excluded, abs_zero]
      exact le_refl zero
    · show le (abs (if exceptional outcome then zero else _))
        (if exceptional outcome then zero else _)
      obtain ⟨positive, sizeNonzero⟩ := inside displacement nonzero small
      simp only [ite_eq_right excluded]
      rw [secant, zero_add, abs_div, abs_of_nonnegative positive.left]
      have divided := div_le_div_right positive ((outside outcome excluded).2 _ positive small)
      rwa [mul_comm, div_eq_mul_inverse (mul _ _), mul_assoc, mul_inverse_cancel sizeNonzero,
        mul_one] at divided
  have pointwise : ∀ outcome,
      Approaches (fun displacement => quotient displacement outcome) (limit outcome) := by
    intro outcome
    by_cases excluded : exceptional outcome
    · show Approaches (fun _ => if exceptional outcome then zero else _)
        (if exceptional outcome then zero else _)
      simp only [ite_eq_left excluded]
      exact approaches_const zero
    · show Approaches (fun _ => if exceptional outcome then zero else _)
        (if exceptional outcome then zero else _)
      simp only [ite_eq_right excluded]
      exact (outside outcome excluded).1.atSize
  obtain ⟨value, integral, approaches⟩ := dominated_convergence_approaches radiusPositive
    integrals
    (MeasurableMap.ite exceptionalMeasurable (MeasurableMap.constant _ _ zero)
      tangentMeasurable)
    boundIntegral dominated pointwise
  refine ⟨value, ⟨primal, integral.congr_ae tangentMeasurable
    (almost fun outcome clear => ite_eq_right clear)⟩, ?_⟩
  have target := approaches_sub approaches errorSmall.atSize
  rw [sub_zero] at target
  refine approaches_congr_near one_positive (fun _ _ _ => ?_) target
  show sub (add (secant objective zero _) _) _ = secant objective zero _
  simp only [Side.along, sub_eq_add_neg, add_assoc, add_neg, add_zero]

/-- The regular objective case identifies the right mean with the given
two-sided slope. The dominated-convergence argument is shared with the
unconditional right result. -/
theorem interchange {law : Measure space}
    {family : selection.Carrier → Outcome → selection.Carrier}
    {objective error : selection.Carrier → selection.Carrier}
    {tangent dominator : Outcome → selection.Carrier}
    {radius dominatorValue slope : selection.Carrier}
    (radiusPositive : lt zero radius)
    (unbiased : ∀ step, le zero step → lt step radius →
      HasRealIntegral law (family step) (add (objective step) (error step)))
    (errorAtZero : error zero = zero)
    (errorSmall : ApproachesFromRight (fun step => div (error step) step) zero)
    (sampleDerivative : law.AE fun outcome =>
      HasRightDerivative (fun step => family step outcome) zero (tangent outcome))
    (tangentMeasurable : MeasurableMap space borel tangent)
    (lipschitz : law.AE fun outcome => ∀ step, lt zero step → lt step radius →
      le (abs (sub (family step outcome) (family zero outcome)))
        (mul step (dominator outcome)))
    (dominatorIntegral : HasRealIntegral law dominator dominatorValue)
    (regular : HasDerivative objective zero slope) :
    Estimates law (family zero) tangent (objective zero) slope ∧
      Jet objective (objective zero) slope := by
  obtain ⟨mean, estimates, right⟩ := interchange_right radiusPositive unbiased errorAtZero
    errorSmall sampleDerivative tangentMeasurable lipschitz dominatorIntegral
  have equal : mean = slope := approaches_unique right (regular.atSide .right)
  rw [equal] at estimates
  exact ⟨estimates, ⟨rfl, regular⟩⟩

/-- Dominated quotients at the selected side certify the tangent mean and the
objective's derivative at that side. No objective regularity is assumed. -/
theorem interchange_dominated {side : Side} {measure : Measure space}
    {family : IntegralFamily measure} {pointwise : Outcome → selection.Carrier}
    (dominated : HasDominatedDifferenceQuotients family zero side)
    (differentiable : HasPointwiseDerivative family zero pointwise side)
    (measurable : MeasurableMap space borel pointwise) :
    ∃ slope, Estimates measure (family.integrand zero) pointwise (family.value zero) slope ∧
      Jet family.value (family.value zero) slope side := by
  obtain ⟨slope, _, integral, regular⟩ :=
    differentiatesUnderIntegral_of_dominated dominated differentiable measurable
  exact ⟨slope, ⟨⟨family.certified zero, integral⟩, ⟨rfl, regular⟩⟩⟩

/-- A point mass is the exact interchange case at either side. Its two
certified means are the readouts at the atom, and the objective's selected-side
jet identifies them. A right jet does not require a two-sided derivative. -/
theorem interchange_dirac {side : Side} (atom : Outcome)
    {primal tangent : Outcome → selection.Carrier}
    {objective : selection.Carrier → selection.Carrier}
    (primalMeasurable : MeasurableMap space borel primal)
    (tangentMeasurable : MeasurableMap space borel tangent)
    (jet : Jet objective (primal atom) (tangent atom) side) :
    Estimates (Measure.dirac space atom) primal tangent (objective zero) (tangent atom) ∧
      Jet objective (objective zero) (tangent atom) side := by
  have estimates := Estimates.dirac atom primalMeasurable tangentMeasurable
  rw [← jet.base] at estimates
  exact ⟨estimates, ⟨rfl, jet.derivative⟩⟩

end Estimates

/-! ### A one-sided family: the maximal coupling of two coins

The seed is the draw `x₀` of a fair coin, the law `Bernoulli(1/2)`. The maximal
coupling of `Bernoulli(1/2)` with `Bernoulli(1/2 + ε)` keeps `x₀` with the
largest probability, and GradInf integrates out the switch per seed. The
surrogate is the conditional probability that the coupled draw is `true`:
`min(1 + 2ε, 1)` after `true` and `2·max(ε, 0)` after `false`. Its mean is the
coupled coin's bias `1/2 + ε` at every step, so the family is exact. Each
sample has a kink at zero: its right slope is the other sample's left slope. -/

namespace Coupling

/-- The kept draw. -/
abbrev seeds : Space Bool := Space.discrete Bool

/-- The fair coin, as a categorical law with equal weights. -/
noncomputable def seed : Measure seeds :=
  Problib.Analysis.categorical [true, false] fun _ => NNReal.one

/-- Each outcome's share of the fair coin, which is one half. -/
noncomputable def share : selection.Carrier :=
  (NNReal.div NNReal.one
    (NNReal.additiveLaws.listSum ([true, false].map fun _ => NNReal.one))).toReal

/-- The per-seed surrogate: `min(1 + 2ε, 1)` after `true`, `2·max(ε, 0)` after
`false`. -/
noncomputable def surrogate (step : selection.Carrier) : Bool → selection.Carrier
  | true => add one (sub step (abs step))
  | false => add step (abs step)

/-- The objective: the coupled coin's bias, `1/2 + ε`. -/
noncomputable def bias (step : selection.Carrier) : selection.Carrier :=
  mul share (add one (add step step))

/-- The right slope of each sample. -/
noncomputable def slope : Bool → selection.Carrier
  | true => zero
  | false => add one one

/-- A reading of the kept draw averages its two values. -/
theorem hasRealIntegral_seed (reading : Bool → selection.Carrier) :
    HasRealIntegral seed reading (mul share (add (reading true) (reading false))) := by
  have integral : HasRealIntegral seed reading
      (add (mul share (reading true)) (add (mul share (reading false)) zero)) :=
    Problib.Analysis.hasRealIntegral_categorical [true, false] (fun _ => NNReal.one) reading
  rwa [add_zero, ← mul_add] at integral

/-- The family is exact: its mean is the bias at every step. -/
theorem surrogate_mean (step : selection.Carrier) :
    HasRealIntegral seed (surrogate step) (bias step) := by
  have integral := hasRealIntegral_seed (surrogate step)
  have exact : mul share (add (surrogate step true) (surrogate step false)) = bias step := by
    show mul share (add (add one (sub step (abs step))) (add step (abs step))) =
      mul share (add one (add step step))
    real_grind
  rwa [exact] at integral

/-- Over a positive step, each sample moves by its right slope. -/
theorem surrogate_increment (outcome : Bool) {step : selection.Carrier}
    (positive : lt zero step) :
    sub (surrogate step outcome) (surrogate zero outcome) = mul step (slope outcome) := by
  cases outcome
  · show sub (add step (abs step)) (add zero (abs zero)) = mul step (add one one)
    rw [abs_of_nonnegative positive.left, abs_zero]
    real_grind
  · show sub (add one (sub step (abs step))) (add one (sub zero (abs zero))) = mul step zero
    rw [abs_of_nonnegative positive.left, abs_zero]
    real_grind

/-- Each sample's right derivative is its slope. -/
theorem surrogate_right (outcome : Bool) :
    HasRightDerivative (fun step => surrogate step outcome) zero (slope outcome) := by
  intro epsilon positive
  refine ⟨one, one_positive, fun step stepPositive _ => ?_⟩
  have nonzero : step ≠ zero := fun vanished =>
    lt_irrefl zero (by rwa [vanished] at stepPositive)
  show lt (abs (sub (div (sub (surrogate (add zero step) outcome) (surrogate zero outcome))
    step) (slope outcome))) epsilon
  rw [zero_add, surrogate_increment outcome stepPositive, mul_comm, div_eq_mul_inverse,
    mul_assoc, mul_inverse_cancel nonzero, mul_one, sub_self, abs_zero]
  exact positive

/-- Over a negative step, each sample moves by the other sample's right
slope. -/
theorem surrogate_left_increment (outcome : Bool) {step : selection.Carrier}
    (positive : lt zero step) :
    sub (surrogate (neg step) outcome) (surrogate zero outcome) =
      mul (neg step) (slope (!outcome)) := by
  cases outcome
  · show sub (add (neg step) (abs (neg step))) (add zero (abs zero)) = mul (neg step) zero
    rw [abs_neg, abs_of_nonnegative positive.left, abs_zero]
    real_grind
  · show sub (add one (sub (neg step) (abs (neg step)))) (add one (sub zero (abs zero))) =
      mul (neg step) (add one one)
    rw [abs_neg, abs_of_nonnegative positive.left, abs_zero]
    real_grind

/-- No sample is differentiable at zero: the secants on the two sides settle at
slopes two apart. -/
theorem surrogate_kink (outcome : Bool) (derivative : selection.Carrier) :
    ¬HasDerivative (fun step => surrogate step outcome) zero derivative := by
  intro differentiable
  obtain ⟨radius, radiusPositive, close⟩ := differentiable one one_positive
  obtain ⟨witness, witnessNonzero, small⟩ := exists_nonzero_within radiusPositive
  have positive := abs_positive_of_nonzero witnessNonzero
  have sizeNonzero : abs witness ≠ zero := fun vanished =>
    witnessNonzero (abs_eq_zero_iff.mp vanished)
  have negativeNonzero : neg (abs witness) ≠ zero := fun vanished =>
    sizeNonzero (by rw [← neg_neg (abs witness), vanished, neg_zero])
  have smallSize : lt (abs (abs witness)) radius := by
    rwa [abs_of_nonnegative positive.left]
  have smallNegative : lt (abs (neg (abs witness))) radius := by
    rwa [abs_neg, abs_of_nonnegative positive.left]
  have right := close _ sizeNonzero smallSize
  have left := close _ negativeNonzero smallNegative
  simp only [secant, zero_add] at right left
  rw [surrogate_increment outcome positive, mul_comm, div_eq_mul_inverse, mul_assoc,
    mul_inverse_cancel sizeNonzero, mul_one] at right
  rw [surrogate_left_increment outcome positive, mul_comm, div_eq_mul_inverse, mul_assoc,
    mul_inverse_cancel negativeNonzero, mul_one] at left
  rw [abs_lt] at right left
  cases outcome <;> simp only [slope, Bool.not_true, Bool.not_false] at right left <;>
    real_grind

/-- The interchange theorem applies although no sample is differentiable: the
right slopes have certified mean `2·(1/2)`, the derivative of the bias. -/
theorem coupling_estimates :
    Estimates seed (surrogate zero) slope (bias zero) (mul share (add one one)) ∧
      Jet bias (bias zero) (mul share (add one one)) := by
  have regular : HasDerivative bias zero (mul share (add zero (add one one))) :=
    hasDerivative_smul share (hasDerivative_add (hasDerivative_const one zero)
      (hasDerivative_add (hasDerivative_identity zero) (hasDerivative_identity zero)))
  rw [zero_add] at regular
  exact Estimates.interchange (error := fun _ => zero) (dominator := slope) one_positive
    (fun step _ _ => by rw [add_zero]; exact surrogate_mean step) rfl noError_small
    (Measure.ae_of_forall surrogate_right) (MeasurableMap.from_discrete borel slope)
    (Measure.ae_of_forall fun outcome step positive _ => by
      rw [surrogate_increment outcome positive, abs_mul, abs_of_nonnegative positive.left]
      cases outcome
      · show le (mul step (abs (add one one))) (mul step (add one one))
        rw [abs_of_nonnegative (add_nonnegative (le_of_lt one_positive)
          (le_of_lt one_positive))]
        exact le_refl _
      · show le (mul step (abs zero)) (mul step zero)
        rw [abs_zero]
        exact le_refl _)
    (hasRealIntegral_seed slope) regular

end Coupling

/-! ### Correlated coefficients

Marginal means do not supply the product rule's mixed moments. Under the fair
coin the sign `±1` has mean zero, so a coefficient and an estimate that are
both the sign are each unbiased for zero. Their product is one at every
outcome, so `E[A·X] = 1` while `E[A]·E[X] = 0`. -/

namespace Correlated

open Coupling (seed hasRealIntegral_seed)

/-- `+1` at `true` and `-1` at `false`. -/
noncomputable def sign : Bool → selection.Carrier
  | true => one
  | false => neg one

/-- The fair coin is a probability. -/
theorem seed_probability : Measure.IsProbability seed :=
  Problib.Analysis.categorical_isProbability _ fun total =>
    NNReal.one_ne_zero (NNReal.add_eq_zero_iff.mp total).1

/-- The sign has mean zero. -/
theorem sign_mean : HasRealIntegral seed sign zero := by
  have integral := hasRealIntegral_seed sign
  have vanishes : mul Coupling.share (add (sign true) (sign false)) = zero := by
    show mul Coupling.share (add one (neg one)) = zero
    rw [add_neg, mul_zero]
  rwa [vanishes] at integral

/-- The sign times itself has mean one. -/
theorem product_mean :
    HasRealIntegral seed (fun outcome => mul (sign outcome) (sign outcome)) one :=
  (HasRealIntegral.const seed_probability one).congr fun outcome => by
    cases outcome
    · show one = mul (neg one) (neg one)
      real_grind
    · show one = mul one one
      real_grind

/-- Each coefficient is unbiased for zero, yet the primal moment is not the
product of the means. -/
theorem moment_not_product :
    HasRealIntegral seed sign zero ∧
      ¬HasRealIntegral seed (fun outcome => mul (sign outcome) (sign outcome))
        (mul zero zero) := by
  refine ⟨sign_mean, fun wrong => ?_⟩
  have equal := product_mean.unique wrong
  rw [mul_zero] at equal
  exact one_ne_zero equal

end Correlated

/-! ### A kinked objective

A right-sided interchange does not promote to a two-sided derivative. On a
point mass, every sample of the family `h(ε) = |ε|` moves by `|ε|`, so the
family is dominated with right slope one, and `interchange_right` certifies the
objective's right derivative one. The objective `|ε|` has no two-sided
derivative at zero, so no theorem may conclude one from these premises. -/

namespace Kink

/-- The one-point space. -/
abbrev point : Space Unit := Space.discrete Unit

/-- Every sample is the size of the step. -/
noncomputable def family (step : selection.Carrier) (_ : Unit) : selection.Carrier :=
  abs step

/-- Over a positive step, the size moves by the step. -/
theorem abs_increment {step : selection.Carrier} (positive : lt zero step) :
    sub (abs step) (abs zero) = mul step one := by
  rw [abs_of_nonnegative positive.left, abs_zero, sub_zero, mul_one]

/-- The size has right derivative one at zero. -/
theorem abs_right : HasRightDerivative abs zero one := by
  intro epsilon positive
  refine ⟨one, one_positive, fun step stepPositive _ => ?_⟩
  have nonzero : step ≠ zero := fun vanished =>
    lt_irrefl zero (by rwa [vanished] at stepPositive)
  simp only [secant, zero_add]
  rw [abs_increment stepPositive, mul_comm, div_eq_mul_inverse, mul_assoc,
    mul_inverse_cancel nonzero, mul_one, sub_self, abs_zero]
  exact positive

/-- The right interchange certifies the right derivative of the kinked
objective. -/
theorem right_estimates : ∃ slope,
    Estimates (Measure.dirac point ()) (family zero) (fun _ => one) (abs zero) slope ∧
      HasDerivativeOn .right abs zero slope :=
  Estimates.interchange_right (objective := abs) (error := fun _ => zero)
    (dominator := fun _ => one) one_positive
    (fun step _ _ => by
      rw [add_zero]
      exact hasRealIntegral_dirac point () (fun _ => Space.discrete_measurable _))
    rfl noError_small (Measure.ae_of_forall fun _ => abs_right)
    (fun _ => Space.discrete_measurable _)
    (Measure.ae_of_forall fun _ step positive _ => by
      show le (abs (sub (abs step) (abs zero))) (mul step one)
      rw [abs_increment positive, mul_one, abs_of_nonnegative positive.left]
      exact le_refl step)
    (hasRealIntegral_dirac point () (fun _ => Space.discrete_measurable _))

/-- The kinked objective has no two-sided derivative at zero: its secants on
the two sides settle at `1` and `-1`. -/
theorem abs_kink (derivative : selection.Carrier) : ¬HasDerivative abs zero derivative := by
  intro differentiable
  obtain ⟨radius, radiusPositive, close⟩ := differentiable one one_positive
  obtain ⟨witness, witnessNonzero, small⟩ := exists_nonzero_within radiusPositive
  have positive := abs_positive_of_nonzero witnessNonzero
  have sizeNonzero : abs witness ≠ zero := fun vanished =>
    witnessNonzero (abs_eq_zero_iff.mp vanished)
  have negativeNonzero : neg (abs witness) ≠ zero := fun vanished =>
    sizeNonzero (by rw [← neg_neg (abs witness), vanished, neg_zero])
  have smallSize : lt (abs (abs witness)) radius := by
    rwa [abs_of_nonnegative positive.left]
  have smallNegative : lt (abs (neg (abs witness))) radius := by
    rwa [abs_neg, abs_of_nonnegative positive.left]
  have right := close _ sizeNonzero smallSize
  have left := close _ negativeNonzero smallNegative
  have leftIncrement : sub (abs (neg (abs witness))) (abs zero) =
      mul (neg (abs witness)) (neg one) := by
    rw [abs_neg, abs_of_nonnegative positive.left, abs_zero, sub_zero]
    real_grind
  simp only [secant, zero_add] at right left
  rw [abs_increment positive, mul_comm, div_eq_mul_inverse, mul_assoc,
    mul_inverse_cancel sizeNonzero, mul_one] at right
  rw [leftIncrement, mul_comm, div_eq_mul_inverse, mul_assoc,
    mul_inverse_cancel negativeNonzero, mul_one] at left
  rw [abs_lt] at right left
  real_grind

end Kink

end Problib.Inference.Derivative.Continuous
