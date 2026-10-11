module

public import Problib.Analysis.Gaussian.Moment
public import Problib.Analysis.Gaussian.Derivative
public import Problib.Analysis.Real.Substitution
import Problib.Measure.Integral.Density.Zero
import Problib.Real.Grind

/-! The standard Gaussian distribution function.

`cdf x` is the mass the standard Gaussian law gives the half-line `(-∞, x]`,
read as a real number. Every set has mass at most one, so the reading loses
nothing, and single points have mass zero because the density is bounded.

Two mechanisms carry the facts. First, the law is volume weighted by the
density φ, so the mass of `(a, b]` is the integral of φ there, the primitive of
`Real/Substitution.lean`. The fundamental theorem of calculus then gives
`cdf' = φ`, and φ's positivity makes `cdf` strictly increasing. Second, the
law is invariant under reflection (`reflection_integral`), so the mass of
`(-∞, -x]` equals the mass of `[x, ∞)`, which is `1 - cdf x`. The library
writes upper tails as `cdf (-x)` (`cdf_neg`), never as `1 - cdf x`, because in
floating point the subtraction loses every digit once `cdf x` rounds to one.

Markov's inequality on the first absolute moment bounds the upper tail,
`x · cdf (-x) ≤ 1/√(2π)` for `x > 0`, and the limits at `±∞` follow from it.
-/

set_option autoImplicit false

namespace Problib.Analysis.Gaussian

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real

local notation "φ(" t ")" => NNReal.toReal (density zero one t)

noncomputable section

/-- The standard Gaussian distribution function Φ: the standard law of `(-∞, x]`. -/
@[expose] public def cdf (x : Carrier) : Carrier :=
  ENNReal.toReal (law zero one (Iic x))

private theorem mass_finite (set : Set Carrier) : ENNReal.Finite (law zero one set) :=
  ENNReal.finite_of_le ((law_isProbability zero one).apply_le_one set) trivial

private theorem toReal_add_finite {left right : ENNReal} (leftFinite : ENNReal.Finite left)
    (rightFinite : ENNReal.Finite right) :
    ENNReal.toReal (ENNReal.add left right) =
      add (ENNReal.toReal left) (ENNReal.toReal right) := by
  rcases ENNReal.exists_finite_of_finite leftFinite with ⟨left, rfl⟩
  rcases ENNReal.exists_finite_of_finite rightFinite with ⟨right, rfl⟩
  rfl

/-- The distribution function reads the half-line mass without loss. -/
public theorem cdf_eq (x : Carrier) : ENNReal.ofReal (cdf x) = law zero one (Iic x) :=
  ENNReal.ofReal_toReal (mass_finite _)

/-- Single points carry no standard Gaussian mass. -/
private theorem atom_null (point : Carrier) :
    law zero one (Set.singleton point) = ENNReal.zero := by
  rw [law_apply zero one one_positive (measurable_singleton point)]
  apply ENNReal.le_antisymm _ (ENNReal.zero_le _)
  have pointwise : ∀ value, ENNReal.le (ENNReal.finite (density zero one value))
      (ENNReal.finite (NNReal.ofReal (inverse (normalizer one).toReal))) :=
    fun value => density_bound one one_positive zero value
  have bound := lintegral_mono (volume.restrict (Set.singleton point)) pointwise
  rw [lintegral_const, Measure.restrict_apply_univ, volume_singleton, ENNReal.mul_zero] at bound
  exact bound

/-- The half-line up to `b` is the half-line up to `a` and the segment `(a, b]`. -/
private theorem mass_split {first second : Carrier} (ordered : le first second) :
    law zero one (Iic second) =
      ENNReal.add (law zero one (Iic first)) (law zero one (Ioc first second)) := by
  have covers : Set.union (Iic first) (Ioc first second) = Iic second := by
    apply Set.ext
    intro value
    constructor
    · rintro (below | inside)
      · exact le_trans below ordered
      · exact inside.2
    · intro below
      by_cases low : le value first
      · exact Or.inl low
      · exact Or.inr ⟨lt_of_not_le low, below⟩
  rw [← covers]
  exact (law zero one).union_disjoint (measurable_iic first) (measurable_ioc first second)
    (fun value low inside => inside.1.2 low)

/-- The mass of a segment is the integral of the density over it. -/
private theorem mass_segment (first second : Carrier) :
    law zero one (Ioc first second) = segment (fun value => φ(value)) first second := by
  rw [law_apply zero one one_positive (measurable_ioc first second)]
  apply lintegral_congr
  intro value
  exact (ENNReal.ofReal_toReal_finite (density zero one value)).symm

/-- Across a segment the distribution function grows by the density's primitive. -/
private theorem cdf_increment {first second : Carrier} (ordered : le first second) :
    cdf second = add (cdf first) (primitive (fun value => φ(value)) first second) := by
  unfold cdf primitive
  rw [mass_split ordered, toReal_add_finite (mass_finite _) (mass_finite _), mass_segment]

/-- Every nonempty segment has positive mass, because the density is positive. -/
private theorem segment_positive {first second : Carrier} (ordered : lt first second) :
    lt zero (ENNReal.toReal (law zero one (Ioc first second))) := by
  have nonzero : law zero one (Ioc first second) ≠ ENNReal.zero := by
    intro vanished
    rw [law_eq_withDensity zero one one_positive] at vanished
    have support := (Measure.withDensity_apply_eq_zero_iff (density_measurable_slice zero one)
      (measurable_ioc first second)).mp vanished
    have whole : Set.inter (Ioc first second)
        (fun value => ENNReal.finite (density zero one value) ≠ ENNReal.zero) =
          Ioc first second := by
      apply Set.ext
      intro value
      refine ⟨fun member => member.1, fun member => ⟨member, fun vanishes => ?_⟩⟩
      have positive := density_positive zero one one_positive value
      have same : (density zero one value).toReal = ENNReal.toReal (ENNReal.finite
        (density zero one value)) := rfl
      rw [same, vanishes, ENNReal.toReal_zero] at positive
      exact lt_irrefl zero positive
    rw [whole, volume_ioc] at support
    have width := sub_positive_iff.mpr ordered
    have read := ENNReal.toReal_ofReal width.1
    rw [support, ENNReal.toReal_zero] at read
    rw [← read] at width
    exact lt_irrefl zero width
  have finite := mass_finite (Ioc first second)
  have positive := ENNReal.zero_lt_iff_ne_zero.mpr nonzero
  rw [← ENNReal.toReal_lt_toReal_iff (ENNReal.finite_of_le (ENNReal.zero_le _) finite) finite,
    ENNReal.toReal_zero] at positive
  exact positive

/-- The distribution function is nonnegative. -/
public theorem cdf_nonnegative (x : Carrier) : le zero (cdf x) :=
  ENNReal.toReal_nonnegative _

/-- The distribution function is strictly increasing. -/
public theorem cdf_strictMono {first second : Carrier} (ordered : lt first second) :
    lt (cdf first) (cdf second) := by
  rw [cdf_increment (le_of_lt ordered)]
  have gap := segment_positive ordered
  rw [mass_segment] at gap
  unfold primitive
  real_grind

/-- The distribution function is monotone. -/
public theorem cdf_monotone : Monotone cdf := by
  intro first second ordered
  rcases lt_trichotomy first second with less | equal | greater
  · exact le_of_lt (cdf_strictMono less)
  · rw [equal]
    exact le_refl _
  · exact absurd ordered (not_le_iff_lt.mpr greater)

/-- The distribution function is Borel measurable, because it is monotone. -/
public theorem cdf_measurable : MeasurableMap borel borel cdf :=
  monotone_measurable cdf_monotone

/-- The distribution function is positive. -/
public theorem cdf_positive (x : Carrier) : lt zero (cdf x) :=
  lt_of_le_of_lt (cdf_nonnegative (sub x one)) (cdf_strictMono (by real_grind))

/-! ### Reflection -/

/-- The standard law of `(-∞, -x]` is its law of `[x, ∞)`. -/
private theorem mass_reflect (x : Carrier) :
    law zero one (Iic (neg x)) = law zero one (Ici x) := by
  have indicator (set : Set Carrier) (measurable : borel.Measurable set) :
      lintegral (law zero one) (ennrealIndicator set (fun _ => ENNReal.one)) =
        law zero one set := by
    rw [lintegral_indicator _ set measurable, lintegral_const, Measure.restrict_apply_univ,
      ENNReal.one_mul]
  have reflected := reflection_integral one one_positive
    ((ENNRealMeasurable.constant borel ENNReal.one).indicator (measurable_iic (neg x)))
  have same : (fun value => ennrealIndicator (Iic (neg x)) (fun _ => ENNReal.one) (neg value)) =
      ennrealIndicator (Ici x) (fun _ => ENNReal.one) := by
    funext value
    have member : Iic (neg x) (neg value) = Ici x value :=
      propext (neg_le_neg_iff (left := x) (right := value))
    unfold ennrealIndicator ennrealPiecewise
    rw [member]
  rw [same, indicator _ (measurable_ici x), indicator _ (measurable_iic (neg x))] at reflected
  exact reflected.symm

/-- The standard law of `[x, ∞)` reads as `cdf (-x)`. -/
private theorem cdf_neg_eq (x : Carrier) : cdf (neg x) = ENNReal.toReal (law zero one (Ici x)) := by
  unfold cdf
  rw [mass_reflect]

/-- Reflection: `Φ(-x) = 1 - Φ(x)`. Upper tails are written `cdf (neg x)`. -/
public theorem cdf_neg (x : Carrier) : cdf (neg x) = sub one (cdf x) := by
  have closed : Set.union (Ioi x) (Set.singleton x) = Ici x := by
    apply Set.ext
    intro value
    constructor
    · rintro (above | equal)
      · exact le_of_lt above
      · rw [show value = x from equal]
        exact le_refl x
    · intro above
      rcases lt_trichotomy x value with strict | equal | greater
      · exact Or.inl strict
      · exact Or.inr equal.symm
      · exact absurd above (not_le_iff_lt.mpr greater)
  have upper : law zero one (Ici x) = law zero one (Ioi x) := by
    rw [← closed, (law zero one).union_disjoint (measurable_ioi x) (measurable_singleton x)
      (fun value above equal => by
        rw [show value = x from equal] at above
        exact lt_irrefl x above),
      atom_null, ENNReal.add_zero]
  have covers : Set.union (Iic x) (Ioi x) = Set.univ := by
    apply Set.ext
    intro value
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    by_cases below : le value x
    · exact Or.inl below
    · exact Or.inr (lt_of_not_le below)
  have whole := (law zero one).union_disjoint (measurable_iic x) (measurable_ioi x)
    (fun value below above => above.2 below)
  rw [covers, (law_isProbability zero one).univ_eq_one] at whole
  have whole := whole.symm
  have read := congrArg ENNReal.toReal whole
  rw [toReal_add_finite (mass_finite _) (mass_finite _)] at read
  rw [cdf_neg_eq, upper]
  unfold cdf
  change add _ _ = one at read
  real_grind

/-- The distribution function stays below one. -/
public theorem cdf_lt_one (x : Carrier) : lt (cdf x) one := by
  have reflected := cdf_neg x
  have positive := cdf_positive (neg x)
  real_grind

/-- The distribution function is at most one. -/
public theorem cdf_le_one (x : Carrier) : le (cdf x) one :=
  le_of_lt (cdf_lt_one x)

/-- The distribution function is one half at zero. -/
public theorem cdf_zero : cdf zero = half one := by
  have reflected := cdf_neg zero
  rw [neg_zero] at reflected
  unfold half two
  real_grind

/-! ### Derivative -/

private theorem density_continuous (x : Carrier) :
    Approaches (fun displacement => φ(add x displacement)) (φ(x)) :=
  hasDerivative_continuous (hasDerivative_density_value zero one x one_positive)

private theorem density_real_measurable : MeasurableMap borel borel (fun value => φ(value)) := by
  have formula : (fun value => φ(value)) = fun value =>
      div (exp (neg (div (mul (sub value zero) (sub value zero))
        (mul (selection.ofRat 2) one)))) (normalizer one).toReal :=
    funext fun value => density_toReal zero one value
  have centered : MeasurableMap borel borel (fun value => sub value zero) :=
    measurable_sub (MeasurableMap.identity borel) (MeasurableMap.constant borel borel zero)
  have exponent : MeasurableMap borel borel (fun value =>
      exp (neg (div (mul (sub value zero) (sub value zero)) (mul (selection.ofRat 2) one)))) :=
    MeasurableMap.comp exp_measurable (MeasurableMap.comp neg_measurable
      (measurable_div (measurable_mul centered centered)
        (MeasurableMap.constant borel borel (mul (selection.ofRat 2) one))))
  have quotient : MeasurableMap borel borel (fun value =>
      div (exp (neg (div (mul (sub value zero) (sub value zero)) (mul (selection.ofRat 2) one))))
        (normalizer one).toReal) :=
    measurable_div exponent (MeasurableMap.constant borel borel (normalizer one).toReal)
  rw [formula]
  exact @quotient

/-- The distribution function differentiates to the standard density at every point. -/
public theorem hasDerivative_cdf (x : Carrier) : HasDerivative cdf x (φ(x)) := by
  have baseBelow : lt (sub x one) x := by real_grind
  have primitiveDerivative := primitive_hasDerivative density_real_measurable
    (lower := sub (sub x one) one) (upper := add x one)
    (fun value _ _ => density_continuous value)
    (fun value _ _ => (density zero one value).property)
    (by real_grind) baseBelow (by real_grind)
  have shifted := hasDerivative_add (hasDerivative_const (cdf (sub x one)) x)
    primitiveDerivative
  rw [zero_add] at shifted
  refine HasDerivative.congr_near ⟨one, one_positive, fun displacement small => ?_⟩ shifted
  have inside := (abs_lt.mp small).1
  exact (cdf_increment (show le (sub x one) (add x displacement) by real_grind)).symm

/-- The distribution function is continuous at every point. -/
public theorem cdf_continuous (x : Carrier) :
    Approaches (fun displacement => cdf (add x displacement)) (cdf x) :=
  hasDerivative_continuous (hasDerivative_cdf x)

/-! ### Tails -/

/-- Markov's inequality on the first moment: `x · Φ(-x) ≤ 1/√(2π)` for `x > 0`. -/
public theorem cdf_neg_tail {x : Carrier} (positive : lt zero x) :
    le (mul x (cdf (neg x))) (halfMoment one).toReal := by
  have pointwise : ∀ value, ENNReal.le
      (ennrealIndicator (Ici x) (fun _ => ENNReal.ofReal x) value)
      (ENNReal.ofReal (sub value zero)) := by
    intro value
    unfold ennrealIndicator ennrealPiecewise
    by_cases above : Ici x value
    · rw [ite_eq_left above, sub_zero]
      exact ENNReal.ofReal_monotone above
    · rw [ite_eq_right above]
      exact ENNReal.zero_le _
  have bound := lintegral_mono (law zero one) pointwise
  rw [lintegral_indicator _ _ (measurable_ici x), lintegral_const, Measure.restrict_apply_univ,
    positive_centered_moment zero one one_positive] at bound
  rw [← ENNReal.ofReal_toReal (mass_finite (Ici x)),
    ← ofReal_mul positive.1 (ENNReal.toReal_nonnegative _)] at bound
  rw [cdf_neg_eq]
  exact (ENNReal.ofReal_le_iff_le_toReal (upper := ENNReal.finite (halfMoment one)) trivial).mp
    bound

/-- The distribution function tends to one at `+∞`. -/
public theorem cdf_tendsto_one {tolerance : Carrier} (positive : lt zero tolerance) :
    ∃ threshold, lt zero threshold ∧
      ∀ x, lt threshold x → lt (abs (sub one (cdf x))) tolerance := by
  obtain ⟨moment, momentNonnegative, tail⟩ : ∃ moment, le zero moment ∧
      ∀ x, lt zero x → le (mul x (cdf (neg x))) moment :=
    ⟨_, (halfMoment one).property, fun _ xPositive => cdf_neg_tail xPositive⟩
  have scalePositive : lt zero (add moment one) := by real_grind
  have thresholdPositive := mul_positive scalePositive (inverse_of_positive_positive positive)
  refine ⟨mul (add moment one) (inverse tolerance), thresholdPositive, fun x beyond => ?_⟩
  have xPositive := lt_trans thresholdPositive beyond
  have reflected := cdf_neg x
  have upper := cdf_nonnegative (neg x)
  have cancel : mul (mul (add moment one) (inverse tolerance)) tolerance = add moment one := by
    rw [mul_assoc, inverse_mul_cancel (positive_iff_nonnegative_and_nonzero.mp positive).2,
      mul_one]
  have scaled := mul_le_mul_nonnegative_right (le_of_lt beyond) positive.1
  rw [cancel] at scaled
  have product := mul_le_mul_nonnegative_left scaled upper
  have bounded := mul_le_mul_nonnegative_right (tail x xPositive) positive.1
  rw [abs_of_nonnegative (by real_grind)]
  apply lt_of_not_le
  intro large
  have lifted := mul_le_mul_nonnegative_right (show le tolerance (cdf (neg x)) by real_grind)
    (le_of_lt scalePositive)
  real_grind

/-- The distribution function tends to zero at `-∞`. -/
public theorem cdf_tendsto_zero {tolerance : Carrier} (positive : lt zero tolerance) :
    ∃ threshold, lt zero threshold ∧
      ∀ x, lt x (neg threshold) → lt (abs (cdf x)) tolerance := by
  obtain ⟨threshold, thresholdPositive, close⟩ := cdf_tendsto_one positive
  refine ⟨threshold, thresholdPositive, fun x beyond => ?_⟩
  have reflected := close (neg x) (by real_grind)
  rw [cdf_neg] at reflected
  have same : sub one (sub one (cdf x)) = cdf x := by real_grind
  rwa [same] at reflected

end

end Problib.Analysis.Gaussian
