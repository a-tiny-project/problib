module

public import Problib.Analysis.Gamma.Envelope
public import Problib.Analysis.Gamma.Density
public import Problib.Analysis.Logarithm.Derivative
public import Problib.Analysis.Real.Substitution
public import Problib.Measure.Uniform
public import Problib.Measure.Integral.Lebesgue.Zero
import Problib.Real.Grind

/-! Cheng's rejection sampler for the Gamma law at shape `a ≥ 1`.

The sampler draws two uniforms `u` and `v`. The first gives the log-logistic
proposal `x = a·e^V` with `V = logit(u)/λ`, by inversion. The second is the
coin: the attempt accepts when `u > 0` and

  `2·log u + log(1 − v) ≤ a − log 4 + (a + λ)V − x`,

that is, when `log(1 − v)` is at most `T(u) = a − log 4 + (a + λ)V − x − 2·log u`.
The coin reads `1 − v`, so a uniform on `[0, 1)` never takes the logarithm of
zero.

Cheng (1977, algorithm GB) takes `λ = √(2a − 1)`. We take `λ = √a`
(`Envelope`). The threshold is the envelope's `Φ(V)` (`threshold_eq`), so the
coin shows heads with probability `e^{T(u)}` when `Φ ≤ 0` (`section_mass`). The
proposal is an increasing substitution from `(0, 1)` onto `(0, ∞)`
(`substitution`), and the coin's probability is the substitution's derivative
times a fixed multiple of the Gamma density at the proposal
(`coin_eq_density`). So the accepted proposals have a fixed multiple of the
Gamma law (`accepted_integral`). At every positive `λ` the coin's probability
is positive on `(0, 1)`, so acceptance is positive (`acceptance_positive`),
whether or not the envelope holds.
-/

set_option autoImplicit false

open scoped Problib.Real.AC

namespace Problib.Analysis.Gamma.Cheng

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real Problib.Analysis.Logarithm Problib.Analysis.Gamma.Envelope

noncomputable section

/-- `log u − log(1 − u)`. -/
@[expose] public def logit (value : Carrier) : Carrier :=
  sub (logIntegral value) (logIntegral (sub one value))

/-- The log-logistic proposal at index `λ`, with shape `λ²`. -/
@[expose] public def proposal (shape index value : Carrier) : Carrier :=
  mul shape (exp (div (logit value) index))

/-- The right side of Cheng's test, `a − log 4 + (a + λ)V − x`. -/
@[expose] public def bound (shape index value : Carrier) : Carrier :=
  sub (add (sub shape (mul (selection.ofRat 2) (logIntegral (selection.ofRat 2))))
      (mul (add shape index) (div (logit value) index)))
    (proposal shape index value)

/-- The coin's threshold: `log(1 − v)` at most this accepts. -/
@[expose] public def threshold (shape index value : Carrier) : Carrier :=
  sub (bound shape index value) (mul (selection.ofRat 2) (logIntegral value))

/-- Cheng's test as the sampler writes it. -/
@[expose] public def accepts (shape index first second : Carrier) : Prop :=
  lt zero first ∧ le (add (mul (selection.ofRat 2) (logIntegral first))
    (logIntegral (sub one second))) (bound shape index first)

private theorem two_positive : lt zero (selection.ofRat 2) := ofRat_two_positive

private theorem lt_of_le_of_ne' {left right : Carrier} (ordered : le left right)
    (different : left ≠ right) : lt left right :=
  ⟨ordered, fun reverse => different (le_antisymm ordered reverse)⟩

/-- A positive real embeds as a positive extended real. -/
public theorem ofReal_positive {value : Carrier} (positive : lt zero value) :
    ENNReal.lt ENNReal.zero (ENNReal.ofReal value) := by
  rw [← ENNReal.ofReal_zero]
  exact (ENNReal.ofReal_lt_ofReal_iff (le_refl zero) (le_of_lt positive)).mpr positive

private theorem complement_positive {value : Carrier} (member : Ioo zero one value) :
    lt zero (sub one value) := sub_positive_iff.mpr member.2

/-! ### Measurability -/

public theorem logit_measurable : MeasurableMap borel borel logit :=
  measurable_sub log_measurable (MeasurableMap.comp log_measurable
    (measurable_sub (MeasurableMap.constant borel borel one) (MeasurableMap.identity borel)))

public theorem proposal_measurable (shape index : Carrier) :
    MeasurableMap borel borel (proposal shape index) :=
  measurable_mul (MeasurableMap.constant borel borel shape) (MeasurableMap.comp exp_measurable
    (measurable_div logit_measurable (MeasurableMap.constant borel borel index)))

public theorem bound_measurable (shape index : Carrier) :
    MeasurableMap borel borel (bound shape index) :=
  measurable_sub (measurable_add (MeasurableMap.constant borel borel _)
      (measurable_mul (MeasurableMap.constant borel borel _)
        (measurable_div logit_measurable (MeasurableMap.constant borel borel index))))
    (proposal_measurable shape index)

public theorem threshold_measurable (shape index : Carrier) :
    MeasurableMap borel borel (threshold shape index) :=
  measurable_sub (bound_measurable shape index)
    (measurable_mul (MeasurableMap.constant borel borel _) log_measurable)

/-! ### The threshold is the envelope -/

/-- On `(0, 1)` with `a = λ²`, the coin's threshold is the envelope's log ratio
at `V = logit(u)/λ`. -/
public theorem threshold_eq {shape index : Carrier} (square : mul index index = shape)
    (indexPositive : lt zero index) {value : Carrier} (member : Ioo zero one value) :
    threshold shape index value = logRatio index (div (logit value) index) := by
  have complement := complement_positive member
  have indexNonzero := nonzero_of_positive indexPositive
  have scaled : mul index (div (logit value) index) = logit value := by
    rw [mul_comm]; exact div_mul_cancel _ indexNonzero
  -- `e^{logit u} = u/(1 − u)`, so `(1 + e^{logit u})/2 = 1/(2(1 − u))`.
  have odds : exp (logit value) = mul value (inverse (sub one value)) := by
    unfold logit
    rw [show sub (logIntegral value) (logIntegral (sub one value)) =
        add (logIntegral value) (neg (logIntegral (sub one value))) by real_grind,
      exp_add, exp_neg, exp_log _ member.1, exp_log _ complement]
  have half : div (add one (exp (logit value))) (selection.ofRat 2) =
      inverse (mul (selection.ofRat 2) (sub one value)) := by
    rw [odds]
    have cancel := mul_inverse_cancel (nonzero_of_positive complement)
    have twoCancel := mul_inverse_cancel (nonzero_of_positive two_positive)
    rw [div_eq_mul_inverse, inverse_mul (nonzero_of_positive two_positive)
      (nonzero_of_positive complement)]
    real_grind
  have logHalf : logIntegral (div (add one (exp (logit value))) (selection.ofRat 2)) =
      neg (add (logIntegral (selection.ofRat 2)) (logIntegral (sub one value))) := by
    rw [half, log_inverse _ (mul_positive two_positive complement),
      log_mul _ _ two_positive complement]
  unfold threshold bound logRatio proposal
  rw [scaled, logHalf, ← square]
  unfold logit at scaled ⊢
  real_grind

/-! ### The coin -/

/-- The unit interval's volume is the open interval's. -/
public theorem restrictedUnit_eq : restrictedUnit = volume.restrict (Ioo zero one) := by
  apply Measure.ext
  intro region measurable
  unfold restrictedUnit
  rw [Measure.restrict_apply _ _ measurable, Measure.restrict_apply _ _ measurable]
  apply Measure.measure_eq_of_null_difference
  · apply Measure.NullSet.mono (Measure.NullSet.union (volume_singleton zero) (volume_singleton one))
    intro value member
    classical
    by_cases low : value = zero
    · exact Or.inl low
    · refine Or.inr ?_
      have inside := member.1.2
      refine Classical.byContradiction fun high => member.2 ⟨member.1.1, ?_, ?_⟩
      · exact lt_of_le_of_ne' inside.1 (Ne.symm low)
      · exact lt_of_le_of_ne' inside.2 high
  · apply Measure.NullSet.mono (volume_singleton zero)
    intro value member
    exact False.elim (member.2 ⟨member.1.1, le_of_lt member.1.2.1, le_of_lt member.1.2.2⟩)

/-- The coin's heads region: `log(1 − v)` at most the threshold. -/
@[expose] public def heads (threshold : Carrier) : Set Carrier :=
  fun value => le (logIntegral (sub one value)) threshold

public theorem heads_measurable (threshold : Carrier) : borel.Measurable (heads threshold) :=
  (MeasurableMap.comp log_measurable (measurable_sub (MeasurableMap.constant borel borel one)
    (MeasurableMap.identity borel))) (measurable_iic threshold)

/-- At a nonpositive threshold `t`, the coin shows heads with probability `eᵗ`. -/
public theorem section_mass {threshold : Carrier} (nonpositive : le threshold zero) :
    restrictedUnit (heads threshold) = ENNReal.ofReal (exp threshold) := by
  have weight := exp_positive threshold
  have weightAtMost : le (exp threshold) one := by
    have := exp_monotone nonpositive
    rwa [exp_zero] at this
  rw [restrictedUnit_eq, Measure.restrict_apply _ _ (heads_measurable threshold)]
  have lower : volume (Ioo (sub one (exp threshold)) one) = ENNReal.ofReal (exp threshold) := by
    rw [volume_ioo]; congr 1; real_grind
  have upper : volume (Icc (sub one (exp threshold)) one) = ENNReal.ofReal (exp threshold) := by
    rw [volume_icc]; congr 1; real_grind
  apply ENNReal.le_antisymm
  · rw [← upper]
    apply volume.mono
    intro value member
    have complement := complement_positive member.2
    have logged := exp_monotone member.1
    rw [exp_log _ complement] at logged
    exact ⟨by real_grind, le_of_lt member.2.2⟩
  · rw [← lower]
    apply volume.mono
    intro value member
    have complement : lt zero (sub one value) := sub_positive_iff.mpr member.2
    have below : le (sub one value) (exp threshold) := by
      have := member.1; real_grind
    have logged := log_monotone _ _ complement below
    rw [log_exp] at logged
    refine ⟨logged, ?_, member.2⟩
    have := member.1
    real_grind

/-- At a nonnegative threshold the coin always shows heads. -/
public theorem section_mass_of_nonnegative {threshold : Carrier} (nonnegative : le zero threshold) :
    restrictedUnit (heads threshold) = ENNReal.one := by
  have whole := section_mass (le_refl zero)
  rw [exp_zero, ENNReal.ofReal_one] at whole
  apply ENNReal.le_antisymm
  · rw [← restrictedUnit_univ]
    exact restrictedUnit.mono (fun _ _ => True.intro)
  · rw [← whole]
    exact restrictedUnit.mono (fun _ member => le_trans member nonnegative)

/-- The coin shows heads with positive probability at every threshold. -/
public theorem section_mass_positive (threshold : Carrier) :
    ENNReal.lt ENNReal.zero (restrictedUnit (heads threshold)) := by
  rcases le_total threshold zero with nonpositive | nonnegative
  · rw [section_mass nonpositive]
    exact ofReal_positive (exp_positive threshold)
  · rw [section_mass_of_nonnegative nonnegative, ← ENNReal.ofReal_one]
    exact ofReal_positive one_positive

/-! ### The proposal as a substitution -/

private theorem hasDerivative_eq' {function : Carrier → Carrier} {point derivative other : Carrier}
    (differentiable : HasDerivative function point derivative) (same : derivative = other) :
    HasDerivative function point other :=
  same ▸ differentiable

/-- The proposal's derivative, `x/(λu(1 − u))`. -/
@[expose] public def slope (shape index value : Carrier) : Carrier :=
  div (proposal shape index value) (mul index (mul value (sub one value)))

/-- The proposal's inverse, the logistic function of `λ(log x − log a)`. -/
@[expose] public def quantile (shape index value : Carrier) : Carrier :=
  inverse (add one (exp (neg (mul index (sub (logIntegral value) (logIntegral shape))))))

public theorem slope_measurable (shape index : Carrier) :
    MeasurableMap borel borel (slope shape index) :=
  measurable_div (proposal_measurable shape index)
    (measurable_mul (MeasurableMap.constant borel borel index)
      (measurable_mul (MeasurableMap.identity borel)
        (measurable_sub (MeasurableMap.constant borel borel one) (MeasurableMap.identity borel))))

private theorem hasDerivative_logit {value : Carrier} (member : Ioo zero one value) :
    HasDerivative logit value
      (add (inverse value) (inverse (sub one value))) := by
  have complement := complement_positive member
  have inner : HasDerivative (fun point => sub one point) value (sub zero one) :=
    hasDerivative_sub (hasDerivative_const one value) (hasDerivative_identity value)
  have outer := hasDerivative_comp (hasDerivative_log complement) inner
  exact hasDerivative_eq' (hasDerivative_sub (hasDerivative_log member.1) outer) (by real_grind)

private theorem hasDerivative_proposal {shape index : Carrier} (indexPositive : lt zero index)
    {value : Carrier} (member : Ioo zero one value) :
    HasDerivative (proposal shape index) value (slope shape index value) := by
  have complement := complement_positive member
  have scaled : HasDerivative (fun point => div (logit point) index) value
      (mul (add (inverse value) (inverse (sub one value))) (inverse index)) := by
    have product := hasDerivative_smul (inverse index) (hasDerivative_logit member)
    have same : (fun point => div (logit point) index) =
        (fun point => mul (inverse index) (logit point)) := by
      funext point; rw [div_eq_mul_inverse, mul_comm]
    rw [same]
    exact hasDerivative_eq' product (by real_grind)
  have composed := hasDerivative_comp (outer := exp) (hasDerivative_exp _) scaled
  have total := hasDerivative_smul shape composed
  refine hasDerivative_eq' total ?_
  unfold slope proposal
  have valueCancel := mul_inverse_cancel (nonzero_of_positive member.1)
  have complementCancel := mul_inverse_cancel (nonzero_of_positive complement)
  have indexCancel := mul_inverse_cancel (nonzero_of_positive indexPositive)
  have split : inverse (mul index (mul value (sub one value))) =
      mul (inverse index) (mul (inverse value) (inverse (sub one value))) := by
    rw [inverse_mul (nonzero_of_positive indexPositive)
      (nonzero_of_positive (mul_positive member.1 complement)),
      inverse_mul (nonzero_of_positive member.1) (nonzero_of_positive complement)]
  simp only [div_eq_mul_inverse]
  rw [split]
  real_grind

private theorem slope_positive {shape index : Carrier} (shapePositive : lt zero shape)
    (indexPositive : lt zero index) {value : Carrier} (member : Ioo zero one value) :
    lt zero (slope shape index value) :=
  mul_positive (mul_positive shapePositive (exp_positive _))
    (inverse_of_positive_positive (mul_positive indexPositive
      (mul_positive member.1 (complement_positive member))))

private theorem logit_strict {first second : Carrier} (firstIn : Ioo zero one first)
    (secondIn : Ioo zero one second) (ordered : lt first second) :
    lt (logit first) (logit second) := by
  have rising := log_strict _ _ firstIn.1 ordered
  have falling := log_strict _ _ (complement_positive secondIn)
    (show lt (sub one second) (sub one first) by
      constructor
      · have := ordered.1; real_grind
      · intro back; apply ordered.2; real_grind)
  unfold logit
  constructor
  · have := rising.1; have := falling.1; real_grind
  · intro back
    have := rising.1; have := falling.1
    apply rising.2
    have := falling.2
    real_grind

private theorem logit_quantile {shape index : Carrier} {value : Carrier} :
    logit (quantile shape index value) =
      mul index (sub (logIntegral value) (logIntegral shape)) := by
  let tail := exp (neg (mul index (sub (logIntegral value) (logIntegral shape))))
  have tailPositive : lt zero tail := exp_positive _
  have total : lt zero (add one tail) := by have := one_positive; real_grind
  have totalCancel := mul_inverse_cancel (nonzero_of_positive total)
  have complement : sub one (quantile shape index value) = mul tail (inverse (add one tail)) := by
    show sub one (inverse (add one tail)) = _
    real_grind
  unfold logit
  rw [complement, log_mul _ _ tailPositive (inverse_of_positive_positive total)]
  show sub (logIntegral (inverse (add one tail))) _ = _
  rw [log_inverse _ total]
  show sub (neg _) (add (logIntegral (exp _)) _) = _
  rw [log_exp]
  real_grind

/-- The proposal is an increasing substitution from `(0, 1)` onto `(0, ∞)`, at
every positive shape and index. -/
public def substitution {shape index : Carrier} (shapePositive : lt zero shape)
    (indexPositive : lt zero index) : IncreasingSubstitution (Ioo zero one) (Ioi zero) where
  function := proposal shape index
  derivative := slope shape index
  inverse := quantile shape index
  functionMeasurable := proposal_measurable shape index
  derivativeMeasurable := slope_measurable shape index
  domainConvex := fun _ _ _ firstIn secondIn firstMiddle middleSecond =>
    ⟨lt_of_lt_of_le firstIn.1 firstMiddle, lt_of_le_of_lt middleSecond secondIn.2⟩
  domainOpen := fun value member => by
    have half : lt zero (inverse (selection.ofRat 2)) := inverse_of_positive_positive two_positive
    have halfCancel := mul_inverse_cancel (nonzero_of_positive two_positive)
    refine ⟨mul value (inverse (selection.ofRat 2)),
      mul (add one value) (inverse (selection.ofRat 2)), ⟨mul_positive member.1 half, ?_⟩,
      ⟨mul_positive (by have := member.1; have := one_positive; real_grind) half, ?_⟩, ?_, ?_⟩
    · have := mul_lt_mul_positive_right member.2 half; have := member.1; real_grind
    · have := mul_lt_mul_positive_right member.2 half; real_grind
    · have := mul_lt_mul_positive_right member.1 half; real_grind
    · have := mul_lt_mul_positive_right member.2 half; real_grind
  rangeExhaustion := Exhaustion.positive
  maps := fun _ _ => mul_positive shapePositive (exp_positive _)
  inverseIn := fun value _ => by
    have tail := exp_positive (neg (mul index (sub (logIntegral value) (logIntegral shape))))
    have total : lt zero (add one (exp (neg (mul index
        (sub (logIntegral value) (logIntegral shape)))))) := by
      have := one_positive; real_grind
    refine ⟨inverse_of_positive_positive total, ?_⟩
    have larger : lt one (add one (exp (neg (mul index
        (sub (logIntegral value) (logIntegral shape)))))) := by
      constructor
      · have := tail.1; real_grind
      · intro back; apply tail.2; real_grind
    have smaller := inverse_lt_inverse_of_positive one_positive total larger
    rwa [inverse_one] at smaller
  rightInverse := fun value positive => by
    unfold proposal
    rw [logit_quantile]
    have indexCancel := mul_inverse_cancel (nonzero_of_positive indexPositive)
    have exponent : div (mul index (sub (logIntegral value) (logIntegral shape))) index =
        add (logIntegral value) (neg (logIntegral shape)) := by
      rw [div_eq_mul_inverse]; real_grind
    rw [exponent, exp_add, exp_neg, exp_log _ positive, exp_log _ shapePositive]
    have shapeCancel := mul_inverse_cancel (nonzero_of_positive shapePositive)
    real_grind
  increasing := fun first second firstIn secondIn ordered => by
    unfold proposal
    apply mul_lt_mul_positive_left _ shapePositive
    apply exp_strict
    rw [div_eq_mul_inverse, div_eq_mul_inverse]
    exact mul_lt_mul_positive_right (logit_strict firstIn secondIn ordered)
      (inverse_of_positive_positive indexPositive)
  differentiable := fun _ member => hasDerivative_proposal indexPositive member
  continuous := fun value member => by
    have complement := complement_positive member
    have denominator : HasDerivative (fun point => mul index (mul point (sub one point))) value
        (mul index (add (mul one (sub one value)) (mul value (sub zero one)))) :=
      hasDerivative_smul index (hasDerivative_mul (hasDerivative_identity value)
        (hasDerivative_sub (hasDerivative_const one value) (hasDerivative_identity value)))
    exact hasDerivative_continuous (hasDerivative_div (hasDerivative_proposal indexPositive member)
      denominator (nonzero_of_positive (mul_positive indexPositive
        (mul_positive member.1 complement))))
  nonnegative := fun _ member => le_of_lt (slope_positive shapePositive indexPositive member)

/-! ### The coin against the Gamma density -/

/-- The factor between the coin's probability and the substitution's
derivative times the unnormalized Gamma weight: `λ·e^{a − log 4 − a·log a}`. -/
@[expose] public def scale (shape index : Carrier) : Carrier :=
  mul index (exp (sub (sub shape (mul (selection.ofRat 2) (logIntegral (selection.ofRat 2))))
    (mul shape (logIntegral shape))))

/-- The accepted mass's multiple of the Gamma law, `scale·Γ(a)`. -/
@[expose] public def acceptance (shape index : Carrier) : ENNReal :=
  ENNReal.ofReal (mul (scale shape index) (gamma shape))

/-- On `(0, 1)`, the exponential of the threshold is the substitution's
derivative times `scale` times the unnormalized Gamma weight at the proposal. -/
public theorem exp_threshold {shape index : Carrier} (shapePositive : lt zero shape)
    (indexPositive : lt zero index) {value : Carrier} (member : Ioo zero one value) :
    exp (threshold shape index value) =
      mul (slope shape index value) (mul (scale shape index)
        (mul (rpow (proposal shape index value) (sub shape one))
          (exp (neg (mul one (proposal shape index value)))))) := by
  have complement := complement_positive member
  have odds : exp (logit value) = mul value (inverse (sub one value)) := by
    unfold logit
    rw [show sub (logIntegral value) (logIntegral (sub one value)) =
        add (logIntegral value) (neg (logIntegral (sub one value))) by real_grind,
      exp_add, exp_neg, exp_log _ member.1, exp_log _ complement]
  have proposalPositive : lt zero (proposal shape index value) :=
    mul_positive shapePositive (exp_positive _)
  have logProposal : logIntegral (proposal shape index value) =
      add (logIntegral shape) (div (logit value) index) := by
    unfold proposal
    rw [log_mul _ _ shapePositive (exp_positive _), log_exp]
  have scaled : mul index (div (logit value) index) = logit value := by
    rw [mul_comm]; exact div_mul_cancel _ (nonzero_of_positive indexPositive)
  have pointEq : proposal shape index value = mul shape (exp (div (logit value) index)) := rfl
  unfold threshold bound slope scale
  rw [rpow_of_positive proposalPositive, logProposal]
  generalize proposal shape index value = point at *
  generalize div (logit value) index = offset at *
  generalize logit value = odd at *
  subst scaled
  -- Both sides are `e^{a − log 4 + a·V − x}` over `u(1 − u)`.
  have left : exp (sub (sub (add (sub shape (mul (selection.ofRat 2)
        (logIntegral (selection.ofRat 2)))) (mul (add shape index) offset)) point)
        (mul (selection.ofRat 2) (logIntegral value))) =
      mul (exp (sub (add (sub shape (mul (selection.ofRat 2) (logIntegral (selection.ofRat 2))))
        (mul shape offset)) point))
        (mul (exp (mul index offset)) (exp (neg (add (logIntegral value) (logIntegral value))))) := by
    rw [← exp_add, ← exp_add]; congr 1; real_grind
  have right : mul (exp offset) (mul (exp (sub (sub shape (mul (selection.ofRat 2)
        (logIntegral (selection.ofRat 2)))) (mul shape (logIntegral shape))))
        (mul (exp (mul (sub shape one) (add (logIntegral shape) offset)))
          (exp (neg (mul one point))))) =
      mul (exp (sub (add (sub shape (mul (selection.ofRat 2) (logIntegral (selection.ofRat 2))))
        (mul shape offset)) point)) (exp (neg (logIntegral shape))) := by
    rw [← exp_add, ← exp_add, ← exp_add, ← exp_add]; congr 1; real_grind
  have square : exp (neg (add (logIntegral value) (logIntegral value))) =
      mul (inverse value) (inverse value) := by
    rw [exp_neg, exp_add, exp_log _ member.1,
      inverse_mul (nonzero_of_positive member.1) (nonzero_of_positive member.1)]
  have shapeInverse : exp (neg (logIntegral shape)) = inverse shape := by
    rw [exp_neg, exp_log _ shapePositive]
  rw [square, odds] at left
  rw [shapeInverse] at right
  rw [left]
  have valueCancel := mul_inverse_cancel (nonzero_of_positive member.1)
  have complementCancel := mul_inverse_cancel (nonzero_of_positive complement)
  have indexCancel := mul_inverse_cancel (nonzero_of_positive indexPositive)
  have shapeCancel := mul_inverse_cancel (nonzero_of_positive shapePositive)
  have split : inverse (mul index (mul value (sub one value))) =
      mul (inverse index) (mul (inverse value) (inverse (sub one value))) := by
    rw [inverse_mul (nonzero_of_positive indexPositive)
      (nonzero_of_positive (mul_positive member.1 complement)),
      inverse_mul (nonzero_of_positive member.1) (nonzero_of_positive complement)]
  rw [div_eq_mul_inverse, split]
  real_grind

/-! ### The accepted law -/

/-- The coin's chance of heads at a threshold, written measurably. -/
@[expose] public def coin : Carrier → ENNReal :=
  ennrealPiecewise (Iic zero) (fun threshold => ENNReal.ofReal (exp threshold))
    (fun _ => ENNReal.one)

public theorem coin_measurable : ENNRealMeasurable borel coin :=
  ENNRealMeasurable.piecewise (measurable_iic zero)
    (ofReal_measurable.comp exp_measurable) (ENNRealMeasurable.constant borel _)

public theorem heads_eq_coin (threshold : Carrier) :
    restrictedUnit (heads threshold) = coin threshold := by
  classical
  unfold coin ennrealPiecewise
  by_cases nonpositive : le threshold zero
  · rw [ite_eq_left (show Iic zero threshold from nonpositive)]
    exact section_mass nonpositive
  · rw [ite_eq_right (show ¬Iic zero threshold from nonpositive)]
    exact section_mass_of_nonnegative (le_of_lt (lt_of_not_le nonpositive))


/-- The mass of the second draws that accept, at a first draw whose proposal
lies in `region`. -/
@[expose] public def accepted (shape index : Carrier) (region : Set Carrier)
    (first : Carrier) : ENNReal :=
  restrictedUnit (fun second => accepts shape index first second ∧
    region (proposal shape index first))

/-- At a positive first draw the accepted mass is the coin's chance of heads,
where the proposal lies in the region. -/
public theorem accepted_of_positive (shape index : Carrier) (region : Set Carrier)
    {value : Carrier} (positive : lt zero value) :
    accepted shape index region value =
      ennrealIndicator (Set.preimage (proposal shape index) region)
        (fun first => restrictedUnit (heads (threshold shape index first))) value := by
  classical
  unfold accepted
  by_cases inside : region (proposal shape index value)
  · rw [ennrealIndicator_of_mem (region := Set.preimage (proposal shape index) region) inside]
    apply congrArg restrictedUnit
    apply Set.ext
    intro second
    unfold accepts heads threshold
    constructor
    · rintro ⟨⟨_, test⟩, _⟩
      real_grind
    · intro test
      exact ⟨⟨positive, by real_grind⟩, inside⟩
  · rw [ennrealIndicator_of_not_mem (region := Set.preimage (proposal shape index) region) inside]
    have empty : (fun second => accepts shape index value second ∧
        region (proposal shape index value)) = Set.empty :=
      Set.ext fun _ => ⟨fun member => inside member.2, False.elim⟩
    rw [empty]
    exact restrictedUnit.empty_apply

/-- The accepted mass at every first draw: the coin's chance of heads where
the draw is positive and its proposal lies in the region, and zero elsewhere. -/
public theorem accepted_eq (shape index : Carrier) (region : Set Carrier) :
    accepted shape index region = ennrealIndicator
      (Set.inter (Ioi zero) (Set.preimage (proposal shape index) region))
      (fun first => coin (threshold shape index first)) := by
  classical
  funext value
  by_cases positive : lt zero value
  · rw [accepted_of_positive shape index region positive]
    by_cases inside : region (proposal shape index value)
    · rw [ennrealIndicator_of_mem (region := Set.preimage (proposal shape index) region) inside,
        ennrealIndicator_of_mem (show Set.inter (Ioi zero) (Set.preimage (proposal shape index)
          region) value from ⟨positive, inside⟩), heads_eq_coin]
    · rw [ennrealIndicator_of_not_mem (region := Set.preimage (proposal shape index) region) inside,
        ennrealIndicator_of_not_mem (show ¬Set.inter (Ioi zero) (Set.preimage (proposal shape index)
          region) value from fun member => inside member.2)]
  · rw [ennrealIndicator_of_not_mem (show ¬Set.inter (Ioi zero) (Set.preimage (proposal shape index)
      region) value from fun member => positive member.1)]
    have empty : (fun second => accepts shape index value second ∧
        region (proposal shape index value)) = Set.empty :=
      Set.ext fun _ => ⟨fun member => positive member.1.1, False.elim⟩
    unfold accepted
    rw [empty]
    exact restrictedUnit.empty_apply

/-- The accepted mass is measurable in the first draw. -/
public theorem accepted_measurable (shape index : Carrier) {region : Set Carrier}
    (measurable : borel.Measurable region) :
    ENNRealMeasurable borel (accepted shape index region) := by
  rw [accepted_eq]
  exact ENNRealMeasurable.indicator (borel.inter (measurable_ioi zero)
    (proposal_measurable shape index measurable))
    (coin_measurable.comp (threshold_measurable shape index))

/-- The second draws that accept at a first draw form a measurable set. -/
public theorem accepts_measurable (shape index first : Carrier) (region : Set Carrier) :
    borel.Measurable (fun second => accepts shape index first second ∧
      region (proposal shape index first)) := by
  classical
  by_cases condition : lt zero first ∧ region (proposal shape index first)
  · have same : (fun second => accepts shape index first second ∧
        region (proposal shape index first)) = heads (threshold shape index first) := by
      apply Set.ext
      intro second
      unfold accepts heads threshold
      constructor
      · rintro ⟨⟨_, test⟩, _⟩; real_grind
      · intro test; exact ⟨⟨condition.1, by real_grind⟩, condition.2⟩
    rw [same]
    exact heads_measurable _
  · have empty : (fun second => accepts shape index first second ∧
        region (proposal shape index first)) = Set.empty :=
      Set.ext fun _ => ⟨fun member => condition ⟨member.1.1, member.2⟩, False.elim⟩
    rw [empty]
    exact borel.empty

/-- The Gamma density at shape `a` and rate one, times the acceptance. -/
private def target (shape index : Carrier) (region : Set Carrier) : Carrier → ENNReal :=
  ennrealIndicator region
    (fun point => ENNReal.mul (acceptance shape index) (ENNReal.finite (density shape one point)))

private theorem target_measurable (shape index : Carrier) {region : Set Carrier}
    (measurable : borel.Measurable region) : ENNRealMeasurable borel (target shape index region) :=
  ENNRealMeasurable.indicator measurable
    ((ENNRealMeasurable.constant borel _).mul (density_measurable_slice shape one))

/-- Where the envelope holds, the coin's chance of heads is the substitution's
derivative times the Gamma density times the acceptance. -/
private theorem coin_eq {shape index : Carrier} (square : mul index index = shape)
    (one_le : le one index) (region : Set Carrier) {value : Carrier}
    (member : Ioo zero one value) :
    accepted shape index region value =
      ENNReal.mul (ENNReal.ofReal (slope shape index value))
        (target shape index region (proposal shape index value)) := by
  classical
  have indexPositive : lt zero index := lt_of_lt_of_le one_positive one_le
  have shapePositive : lt zero shape := square ▸ mul_positive indexPositive indexPositive
  have pointPositive : lt zero (proposal shape index value) :=
    mul_positive shapePositive (exp_positive _)
  rw [accepted_of_positive shape index region member.1]
  unfold target
  by_cases inside : region (proposal shape index value)
  · rw [ennrealIndicator_of_mem (show Set.preimage (proposal shape index) region value from inside),
      ennrealIndicator_of_mem inside]
    have envelope : le (threshold shape index value) zero := by
      rw [threshold_eq square indexPositive member]
      exact logRatio_nonpositive one_le _
    rw [section_mass envelope, exp_threshold shapePositive indexPositive member,
      density_of_positive shape one pointPositive]
    change _ = ENNReal.mul _ (ENNReal.mul _ (ENNReal.ofReal _))
    have gammaPositive := gamma_positive shapePositive
    have gammaCancel := mul_inverse_cancel (nonzero_of_positive gammaPositive)
    have slopeNonnegative : le zero (slope shape index value) :=
      le_of_lt (mul_positive (mul_positive shapePositive (exp_positive _))
        (inverse_of_positive_positive (mul_positive indexPositive
          (mul_positive member.1 (complement_positive member)))))
    have scalePositive : lt zero (scale shape index) :=
      mul_positive indexPositive (exp_positive _)
    have powerPositive := rpow_positive pointPositive (sub shape one)
    have tail := exp_positive (neg (mul one (proposal shape index value)))
    unfold acceptance
    rw [← ofReal_mul (le_of_lt (mul_positive scalePositive gammaPositive))
        (le_of_lt (div_positive (mul_positive (rpow_positive one_positive shape)
          (mul_positive powerPositive tail)) gammaPositive)),
      ← ofReal_mul slopeNonnegative (le_of_lt (mul_positive (mul_positive scalePositive gammaPositive)
          (div_positive (mul_positive (rpow_positive one_positive shape)
            (mul_positive powerPositive tail)) gammaPositive))),
      one_rpow, div_eq_mul_inverse]
    congr 1
    real_grind
  · rw [ennrealIndicator_of_not_mem (show ¬Set.preimage (proposal shape index) region value from inside),
      ennrealIndicator_of_not_mem inside, ENNReal.mul_zero]

/-- The target vanishes off the positive half line, where the density does. -/
private theorem target_positive_part (shape index : Carrier) (region : Set Carrier) :
    ennrealIndicator (Ioi zero) (target shape index region) = target shape index region := by
  classical
  funext point
  by_cases positive : lt zero point
  · exact ennrealIndicator_of_mem (show Ioi zero point from positive)
  · rw [ennrealIndicator_of_not_mem (show ¬Ioi zero point from positive)]
    unfold target
    by_cases inside : region point
    · rw [ennrealIndicator_of_mem inside,
        density_of_nonpositive shape one (not_lt_iff_le.mp positive)]
      exact (ENNReal.mul_zero _).symm
    · rw [ennrealIndicator_of_not_mem inside]

/-- Cheng's sampler at `λ ≥ 1` and `a = λ²`: the first draws whose proposal
lies in `region` and whose coin shows heads have the Gamma law of `region`,
times the acceptance. -/
public theorem accepted_integral {shape index : Carrier} (square : mul index index = shape)
    (one_le : le one index) {region : Set Carrier} (measurable : borel.Measurable region) :
    lintegral restrictedUnit (accepted shape index region) =
      ENNReal.mul (acceptance shape index) (law shape one region) := by
  have indexPositive : lt zero index := lt_of_lt_of_le one_positive one_le
  have shapePositive : lt zero shape := square ▸ mul_positive indexPositive indexPositive
  let change := substitution shapePositive indexPositive
  have pointwise : (volume.restrict (Ioo zero one)).AEEq (accepted shape index region)
      (fun value => ENNReal.mul (ENNReal.ofReal (change.derivative value))
        (target shape index region (change.function value))) :=
    (volume.ae_restrict_mem (measurable_ioo zero one)).mono
      (fun value member => coin_eq square one_le region member)
  rw [restrictedUnit_eq, lintegral_congr_ae pointwise,
    change.lintegral_eq (target_measurable shape index measurable),
    ← lintegral_indicator _ _ (measurable_ioi zero), target_positive_part]
  unfold target
  rw [lintegral_indicator _ _ measurable, lintegral_smul _ _ (density_measurable_slice shape one),
    law_apply shapePositive one_positive measurable]

/-- At every shape and index, whether or not the envelope holds, the attempt
accepts with positive probability: the coin shows heads with positive chance at
every threshold. -/
public theorem acceptance_positive (shape index : Carrier) :
    ENNReal.lt ENNReal.zero (lintegral restrictedUnit (accepted shape index Set.univ)) := by
  have pointwise : (volume.restrict (Ioo zero one)).AEEq (accepted shape index Set.univ)
      (fun value => coin (threshold shape index value)) :=
    (volume.ae_restrict_mem (measurable_ioo zero one)).mono (fun value member => by
      rw [accepted_of_positive shape index Set.univ member.1,
        ennrealIndicator_of_mem (show Set.preimage (proposal shape index) Set.univ value from
          True.intro), heads_eq_coin])
  rw [restrictedUnit_eq, lintegral_congr_ae pointwise]
  apply lintegral_positive _ (region := Set.univ)
  · rw [Measure.restrict_apply_univ, volume_ioo, sub_zero]
    exact ofReal_positive one_positive
  · exact coin_measurable.comp (threshold_measurable shape index)
  · intro value _
    rw [← heads_eq_coin]
    exact section_mass_positive _

/-- The acceptance is a positive, finite multiple. -/
public theorem acceptance_finite (shape index : Carrier) : ENNReal.Finite (acceptance shape index) :=
  ENNReal.ofReal_finite _

end

end Problib.Analysis.Gamma.Cheng
