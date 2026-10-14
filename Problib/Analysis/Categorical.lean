module

public import Problib.Analysis.Exponential
public import Problib.FiniteEnumeration
public import Problib.Measure.Integral.Lebesgue.Measure
public import Problib.Measure.Integral.Lebesgue.Transport
public import Problib.Measure.Integral.Density.Basic
public import Problib.Measure.Integral.Real
public import Problib.Measure.Normalization

/-! The categorical family.

`categorical categories weights` puts mass `wᵢ/W` on each listed category, where
`W = NNReal.additiveLaws.listSum (categories.map weights)`. The weights are nonnegative by type.
At a positive total the law is a probability (`categorical_isProbability`), and
a positive common factor on the weights leaves it unchanged
(`categorical_scale`).

Weighting `categorical categories w` by the weights `v` of a second categorical
gives `categorical categories (w⊙v)` scaled by `Σwv/W`
(`withDensity_categorical`). When `Σwv > 0` its normalization is
`categorical categories (w⊙v)` (`normalize_withDensity_categorical`). Disjoint
supports break this. `(1, 0)` weighted by `(0, 1)` is the zero measure
(`withDensity_categorical_disjoint`).

`logCategorical categories ℓ` reads log weights through `exp`. Its total is
positive on every nonempty list. A common shift of the log weights leaves it
unchanged (`logCategorical_shift`). Weighting it by `exp ℓ'` adds the log
weights (`withDensity_logCategorical`), and that product never degenerates. -/

set_option autoImplicit false

open scoped Problib.Real.AC

namespace Problib.Analysis

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

variable {ι : Type}

/-- A category's share `wᵢ/W` of the total weight. -/
@[expose] public def categoricalShare (categories : List ι) (weights : ι → NNReal)
    (category : ι) : ENNReal :=
  ENNReal.finite
    (NNReal.div (weights category) (NNReal.additiveLaws.listSum (categories.map weights)))

/-- The categorical law: each listed category carries its share of the total
weight. -/
@[expose] public def categorical (categories : List ι) (weights : ι → NNReal) :
    Measure (Space.discrete ι) :=
  Measure.listSum (categories.map fun category =>
    Measure.smul (categoricalShare categories weights category) (Measure.dirac _ category))

/-- At a positive total, the shares sum to one. -/
public theorem listSum_shares (categories : List ι) {weights : ι → NNReal}
    (positive : NNReal.additiveLaws.listSum (categories.map weights) ≠ NNReal.zero) :
    NNReal.additiveLaws.listSum (categories.map fun category =>
      NNReal.div (weights category) (NNReal.additiveLaws.listSum (categories.map weights))) =
      NNReal.one := by
  apply NNReal.mul_left_cancel positive
  rw [NNReal.mul_one, NNReal.additiveLaws.listSum_map_hom NNReal.additiveLaws (NNReal.mul _)
    (NNReal.mul_zero _) (NNReal.mul_add _)]
  exact NNReal.additiveLaws.listSum_map_congr categories
    (fun category _ => NNReal.mul_div_cancel _ positive)

/-- The categorical law of a set sums the shares of its listed members. -/
public theorem categorical_apply (categories : List ι) (weights : ι → NNReal) (set : Set ι) :
    categorical categories weights set =
      ENNReal.additiveLaws.listSum (categories.map fun category =>
        ENNReal.mul (categoricalShare categories weights category)
        (Measure.dirac (Space.discrete ι) category set)) := by
  rw [categorical, Measure.listSum_apply _ (Space.discrete_measurable set), List.map_map]
  simp only [Function.comp_def, Measure.smul_apply_measurable _ _ (Space.discrete_measurable set)]

/-- Over an enumeration, a category's mass is its share. -/
public theorem categorical_apply_category {categories : List ι}
    (enumeration : FiniteEnumeration categories) (weights : ι → NNReal) (category : ι) :
    categorical categories weights (fun other => other = category) =
      categoricalShare categories weights category := by
  have single : (Space.discrete ι).Measurable (fun other => other = category) :=
    Space.discrete_measurable _
  rw [categorical_apply]
  refine (ENNReal.additiveLaws.listSum_map_eq_single categories category enumeration.nodup
    (enumeration.complete category) _ fun other _ different => ?_).trans ?_
  · show ENNReal.mul _ (Measure.dirac _ other (fun other => other = category)) = ENNReal.zero
    rw [Measure.dirac_apply_of_not_mem _ other single different, ENNReal.mul_zero]
  · show ENNReal.mul _ (Measure.dirac _ category (fun other => other = category)) = _
    rw [Measure.dirac_apply_of_mem _ category single rfl, ENNReal.mul_one]

/-- Over a list without repeats, a listed category's mass is its share. -/
public theorem categorical_apply_member {categories : List ι} (nodup : categories.Nodup)
    (weights : ι → NNReal) {category : ι} (member : category ∈ categories) :
    categorical categories weights (fun other => other = category) =
      categoricalShare categories weights category := by
  have single : (Space.discrete ι).Measurable (fun other => other = category) :=
    Space.discrete_measurable _
  rw [categorical_apply]
  refine (ENNReal.additiveLaws.listSum_map_eq_single categories category nodup member _
    fun other _ different => ?_).trans ?_
  · show ENNReal.mul _ (Measure.dirac _ other (fun other => other = category)) = ENNReal.zero
    rw [Measure.dirac_apply_of_not_mem _ other single different, ENNReal.mul_zero]
  · show ENNReal.mul _ (Measure.dirac _ category (fun other => other = category)) = _
    rw [Measure.dirac_apply_of_mem _ category single rfl, ENNReal.mul_one]

/-- A measure on a finite discrete space is the sum of its point masses. -/
public theorem discrete_apply {ι : Type} (measure : Measure (Space.discrete ι)) {list : List ι}
    (enumeration : FiniteEnumeration list) (set : Set ι) :
    measure set = ENNReal.additiveLaws.listSum (list.map fun category =>
      ENNReal.mul (measure (fun other => other = category))
        (Measure.dirac (Space.discrete ι) category set)) := by
  have point : ∀ input, ennrealIndicator set (fun _ => ENNReal.one) input =
      ENNReal.additiveLaws.listSum (list.map fun category =>
        ennrealIndicator (fun other => other = category)
          (fun _ => Measure.dirac (Space.discrete ι) category set) input) := by
    intro input
    rw [ENNReal.additiveLaws.listSum_map_eq_single list input enumeration.nodup
      (enumeration.complete input) _ fun _ _ different =>
        ennrealIndicator_of_not_mem fun same => different same.symm,
      ennrealIndicator_of_mem (region := fun other => other = input) rfl]
    by_cases member : set input
    · rw [ennrealIndicator_of_mem member,
        Measure.dirac_apply_of_mem _ _ (Space.discrete_measurable set) member]
    · rw [ennrealIndicator_of_not_mem member,
        Measure.dirac_apply_of_not_mem _ _ (Space.discrete_measurable set) member]
  rw [apply_eq_lintegral_indicator measure (Space.discrete_measurable set),
    show ennrealIndicator set (fun _ => ENNReal.one) = _ from funext point,
    lintegral_listSum_map measure list fun _ =>
      ENNRealMeasurable.of_measurableMap (MeasurableMap.from_discrete ennrealBorel _)]
  refine congrArg ENNReal.additiveLaws.listSum (List.map_congr_left fun category _ => ?_)
  rw [lintegral_indicator measure _ (Space.discrete_measurable _), lintegral_const,
    Measure.restrict_apply_univ, ENNReal.mul_comm]

/-- Integrals against the categorical law are share-weighted finite sums. -/
public theorem lintegral_categorical (categories : List ι) (weights : ι → NNReal)
    (function : ι → ENNReal) :
    lintegral (categorical categories weights) function =
      ENNReal.additiveLaws.listSum (categories.map fun category =>
        ENNReal.mul (categoricalShare categories weights category) (function category)) := by
  have functionMeasurable : ENNRealMeasurable (Space.discrete ι) function :=
    ENNRealMeasurable.of_measurableMap (MeasurableMap.from_discrete ennrealBorel function)
  rw [categorical, lintegral_listSum, List.map_map]
  apply congrArg ENNReal.additiveLaws.listSum
  apply List.map_congr_left
  intro category _
  show lintegral (Measure.smul _ _) function = _
  rw [lintegral_smul_measure, lintegral_dirac _ _ functionMeasurable]

/-- A real reading of the categories has the share-weighted sum as its integral
against the categorical law. -/
public theorem hasRealIntegral_categorical (categories : List ι) (weights : ι → NNReal)
    (reading : ι → Carrier) :
    HasRealIntegral (categorical categories weights) reading
      (additiveLaws.listSum (categories.map fun category => mul
        (NNReal.div (weights category)
          (NNReal.additiveLaws.listSum (categories.map weights))).toReal
        (reading category))) := by
  let share := fun category =>
    NNReal.div (weights category) (NNReal.additiveLaws.listSum (categories.map weights))
  have mass : ∀ part : ι → NNReal,
      lintegral (categorical categories weights) (fun category => ENNReal.finite (part category)) =
        ENNReal.finite (NNReal.additiveLaws.listSum (categories.map fun category =>
          NNReal.mul (share category) (part category))) := by
    intro part
    rw [lintegral_categorical, NNReal.additiveLaws.listSum_map_hom ENNReal.additiveLaws
      ENNReal.finite rfl (fun _ _ => rfl)]
    exact congrArg ENNReal.additiveLaws.listSum (List.map_congr_left fun category _ =>
      ENNReal.finite_mul_finite _ _)
  have toReal : ∀ part : ι → NNReal,
      (NNReal.additiveLaws.listSum (categories.map part)).toReal =
        additiveLaws.listSum (categories.map fun category => (part category).toReal) :=
    NNReal.additiveLaws.listSum_map_hom additiveLaws NNReal.toReal rfl (fun _ _ => rfl)
      categories
  refine ⟨{ positive := fun category => NNReal.ofReal (reading category)
            negative := fun category => NNReal.ofReal (neg (reading category))
            positive_measurable := ENNRealMeasurable.of_measurableMap
              (MeasurableMap.from_discrete ennrealBorel _)
            negative_measurable := ENNRealMeasurable.of_measurableMap
              (MeasurableMap.from_discrete ennrealBorel _)
            decomposition := fun category => IntegralParts.scalar_decomposition (reading category)
            positiveMass := NNReal.additiveLaws.listSum (categories.map fun category =>
              NNReal.mul (share category) (NNReal.ofReal (reading category)))
            negativeMass := NNReal.additiveLaws.listSum (categories.map fun category =>
              NNReal.mul (share category) (NNReal.ofReal (neg (reading category))))
            positive_integral := mass _
            negative_integral := mass _ }, ?_⟩
  show sub (NNReal.additiveLaws.listSum (List.map _ categories)).toReal
    (NNReal.additiveLaws.listSum (List.map _ categories)).toReal = _
  rw [toReal, toReal]
  simp only [sub_eq_add_neg]
  rw [additiveLaws.listSum_map_hom additiveLaws neg neg_zero neg_add]
  refine (additiveLaws.listSum_map_add categories _ _).symm.trans ?_
  refine congrArg (fun terms => additiveLaws.listSum (categories.map terms))
    (funext fun category => ?_)
  show sub (mul (share category).toReal (NNReal.ofReal (reading category)).toReal)
      (mul (share category).toReal (NNReal.ofReal (neg (reading category))).toReal) = _
  rw [← mul_sub, ← IntegralParts.scalar_decomposition]

/-- At a positive total the categorical law is a probability. -/
public theorem categorical_isProbability (categories : List ι) {weights : ι → NNReal}
    (positive : NNReal.additiveLaws.listSum (categories.map weights) ≠ NNReal.zero) :
    Measure.IsProbability (categorical categories weights) := by
  constructor
  rw [categorical_apply]
  have atom : ∀ category, ENNReal.mul (categoricalShare categories weights category)
      (Measure.dirac (Space.discrete ι) category Set.univ) =
      categoricalShare categories weights category := fun category => by
    rw [Measure.dirac_apply_univ, ENNReal.mul_one]
  simp only [atom]
  calc ENNReal.additiveLaws.listSum (categories.map fun category =>
        categoricalShare categories weights category)
      = ENNReal.finite (NNReal.additiveLaws.listSum (categories.map fun category =>
          NNReal.div (weights category) (NNReal.additiveLaws.listSum (categories.map weights)))) :=
        (NNReal.additiveLaws.listSum_map_hom ENNReal.additiveLaws ENNReal.finite rfl
          (fun _ _ => rfl) categories _).symm
    _ = ENNReal.one :=
        (congrArg ENNReal.finite (listSum_shares categories positive)).trans rfl

private theorem nonzero_toReal {value : NNReal} (nonzero : value ≠ NNReal.zero) :
    NNReal.toReal value ≠ zero := fun vanishing =>
  nonzero (NNReal.ext (vanishing.trans NNReal.toReal_zero.symm))

/-- A nonzero common factor on the weights leaves the categorical law
unchanged. -/
public theorem categorical_scale (categories : List ι) {factor : NNReal}
    (nonzero : factor ≠ NNReal.zero) (weights : ι → NNReal) :
    categorical categories (fun category => NNReal.mul factor (weights category)) =
      categorical categories weights := by
  classical
  unfold categorical categoricalShare
  simp only [NNReal.semiring.listSum_map_mul_left]
  apply congrArg Measure.listSum
  apply List.map_congr_left
  intro category _
  congr 2
  apply NNReal.ext
  rw [NNReal.toReal_div, NNReal.toReal_div, NNReal.toReal_mul, NNReal.toReal_mul]
  by_cases vanishing : NNReal.additiveLaws.listSum (categories.map weights) = NNReal.zero
  · rw [vanishing, NNReal.toReal_zero, mul_zero, div_zero, div_zero]
  · rw [div_eq_mul_inverse, div_eq_mul_inverse,
      inverse_mul (nonzero_toReal nonzero) (nonzero_toReal vanishing)]
    calc mul (mul (NNReal.toReal factor) (NNReal.toReal (weights category)))
          (mul (inverse (NNReal.toReal factor))
            (inverse (NNReal.toReal (NNReal.additiveLaws.listSum (categories.map weights)))))
        = mul (mul (NNReal.toReal factor) (inverse (NNReal.toReal factor)))
            (mul (NNReal.toReal (weights category))
              (inverse (NNReal.toReal
                (NNReal.additiveLaws.listSum (categories.map weights))))) := by ac_rfl
      _ = _ := by rw [mul_inverse_cancel (nonzero_toReal nonzero), one_mul]

/-- The share identity behind the product law: `(a/W)·b = (S/W)·(ab/S)` at a
nonzero `S`. -/
private theorem share_product (first weight second total : NNReal)
    (nonzero : total ≠ NNReal.zero) :
    NNReal.mul (NNReal.div first weight) second =
      NNReal.mul (NNReal.div total weight) (NNReal.div (NNReal.mul first second) total) := by
  apply NNReal.ext
  simp only [NNReal.toReal_mul, NNReal.toReal_div, div_eq_mul_inverse]
  calc mul (mul (NNReal.toReal first) (inverse (NNReal.toReal weight))) (NNReal.toReal second)
      = mul one (mul (mul (NNReal.toReal first) (NNReal.toReal second))
          (inverse (NNReal.toReal weight))) := by
        rw [one_mul]
        ac_rfl
    _ = mul (mul (NNReal.toReal total) (inverse (NNReal.toReal total)))
          (mul (mul (NNReal.toReal first) (NNReal.toReal second))
            (inverse (NNReal.toReal weight))) := by
        rw [mul_inverse_cancel (nonzero_toReal nonzero)]
    _ = _ := by ac_rfl

/-- The product of two categoricals: weighting the law of `w` by the weights
`v` gives the law of `w⊙v` scaled by `Σwv/W`, when `Σwv` is positive. -/
public theorem withDensity_categorical (categories : List ι) (first second : ι → NNReal)
    (positive : NNReal.additiveLaws.listSum (categories.map fun category =>
      NNReal.mul (first category) (second category)) ≠ NNReal.zero) :
    (categorical categories first).withDensity (fun category => ENNReal.finite (second category)) =
      Measure.smul (ENNReal.finite (NNReal.div
          (NNReal.additiveLaws.listSum (categories.map fun category =>
            NNReal.mul (first category) (second category)))
          (NNReal.additiveLaws.listSum (categories.map first))))
        (categorical categories (fun category => NNReal.mul (first category) (second category))) := by
  classical
  apply Measure.ext
  intro set setMeasurable
  rw [Measure.withDensity_apply _ _ setMeasurable, ← lintegral_indicator _ _ setMeasurable,
    lintegral_categorical, Measure.smul_apply_measurable _ _ setMeasurable, categorical_apply]
  rw [ENNReal.additiveLaws.listSum_map_hom ENNReal.additiveLaws (ENNReal.mul _)
    (ENNReal.mul_zero _) (ENNReal.mul_add _)]
  apply congrArg ENNReal.additiveLaws.listSum
  apply List.map_congr_left
  intro category _
  unfold categoricalShare
  by_cases member : set category
  · rw [ennrealIndicator_of_mem member, Measure.dirac_apply_of_mem _ _ setMeasurable member,
      ENNReal.mul_one, ENNReal.finite_mul_finite, ENNReal.finite_mul_finite,
      share_product _ _ _ _ positive]
  · rw [ennrealIndicator_of_not_mem member,
      Measure.dirac_apply_of_not_mem _ _ setMeasurable member,
      ENNReal.mul_zero, ENNReal.mul_zero, ENNReal.mul_zero]

/-- The product of two categoricals is normalizable when both totals are
positive. -/
public theorem withDensity_categorical_normalizable (categories : List ι)
    {first second : ι → NNReal}
    (firstPositive : NNReal.additiveLaws.listSum (categories.map first) ≠ NNReal.zero)
    (positive : NNReal.additiveLaws.listSum (categories.map fun category =>
      NNReal.mul (first category) (second category)) ≠ NNReal.zero) :
    Measure.IsNormalizable
      ((categorical categories first).withDensity
        (fun category => ENNReal.finite (second category))) := by
  rw [withDensity_categorical categories first second positive]
  refine Measure.IsNormalizable.of_finite_mass (mass := NNReal.div
    (NNReal.additiveLaws.listSum (categories.map fun category =>
      NNReal.mul (first category) (second category)))
    (NNReal.additiveLaws.listSum (categories.map first))) ?_ ?_
  · rw [Measure.smul_apply_measurable _ _ (Space.univ _),
      (categorical_isProbability categories positive).univ_eq_one, ENNReal.mul_one]
  · intro vanishing
    have product := NNReal.div_mul_cancel
      (NNReal.additiveLaws.listSum (categories.map fun category =>
        NNReal.mul (first category) (second category)))
      firstPositive
    rw [vanishing, NNReal.zero_mul] at product
    exact positive product.symm

/-- `Cat(w)·Cat(v) ∝ Cat(w⊙v)`: when `Σwv > 0`, the normalized product is the
categorical law of `w⊙v`. -/
public theorem normalize_withDensity_categorical (categories : List ι)
    {first second : ι → NNReal}
    (firstPositive : NNReal.additiveLaws.listSum (categories.map first) ≠ NNReal.zero)
    (positive : NNReal.additiveLaws.listSum (categories.map fun category =>
      NNReal.mul (first category) (second category)) ≠ NNReal.zero) :
    Measure.normalize ((categorical categories first).withDensity
        (fun category => ENNReal.finite (second category)))
        (withDensity_categorical_normalizable categories firstPositive positive) =
      categorical categories (fun category => NNReal.mul (first category) (second category)) := by
  apply Measure.normalize_eq_of_smul_eq
  rw [withDensity_categorical categories first second positive,
    Measure.smul_apply_measurable _ _ (Space.univ _),
    (categorical_isProbability categories positive).univ_eq_one, ENNReal.mul_one]

/-- Disjoint supports multiply to the zero measure: `(1, 0)` weighted by
`(0, 1)`, over the categories `[true, false]`. The premise `Σwv > 0` of
`normalize_withDensity_categorical` is necessary. -/
public theorem withDensity_categorical_disjoint :
    (categorical [true, false]
      (fun category => if category then NNReal.one else NNReal.zero)).withDensity
        (fun category => ENNReal.finite (if category then NNReal.zero else NNReal.one)) =
      Measure.zero (Space.discrete Bool) := by
  apply Measure.ext
  intro set setMeasurable
  rw [Measure.withDensity_apply _ _ setMeasurable, ← lintegral_indicator _ _ setMeasurable,
    lintegral_categorical, Measure.zero_apply]
  have first : ennrealIndicator set
      (fun category => ENNReal.finite (if category then NNReal.zero else NNReal.one)) true =
      ENNReal.zero := by
    by_cases member : set true
    · exact (ennrealIndicator_of_mem member).trans rfl
    · exact ennrealIndicator_of_not_mem member
  have second : categoricalShare [true, false]
      (fun category => if category then NNReal.one else NNReal.zero) false = ENNReal.zero :=
    congrArg ENNReal.finite (NNReal.zero_div _)
  simp only [List.map_cons, List.map_nil, Problib.Algebra.AdditiveCommutativeMonoidLaws.listSum,
    first, second, ENNReal.mul_zero, ENNReal.zero_mul, ENNReal.add_zero]

/-- The zero product of disjoint supports cannot be normalized. -/
public theorem withDensity_categorical_disjoint_not_normalizable :
    ¬Measure.IsNormalizable ((categorical [true, false]
      (fun category => if category then NNReal.one else NNReal.zero)).withDensity
      (fun category => ENNReal.finite (if category then NNReal.zero else NNReal.one))) := by
  rw [withDensity_categorical_disjoint]
  exact Measure.zero_not_normalizable _

/-- The categorical law of log weights `ℓ`: weights `exp ℓᵢ`. -/
@[expose] public def logCategorical (categories : List ι) (logWeights : ι → Carrier) :
    Measure (Space.discrete ι) :=
  categorical categories (fun category => NNReal.ofReal (exp (logWeights category)))

private theorem exp_weight_positive (value : Carrier) :
    NNReal.lt NNReal.zero (NNReal.ofReal (exp value)) := by
  show lt (NNReal.toReal NNReal.zero) (NNReal.toReal (NNReal.ofReal (exp value)))
  rw [NNReal.toReal_zero, NNReal.toReal_ofReal (exp_positive value).1]
  exact exp_positive value

/-- Log weights have a positive total on every nonempty list. -/
public theorem logCategorical_total_ne_zero {categories : List ι}
    (nonempty : categories ≠ []) (logWeights : ι → Carrier) :
    NNReal.additiveLaws.listSum (categories.map fun category =>
      NNReal.ofReal (exp (logWeights category))) ≠ NNReal.zero := by
  cases categories with
  | nil => exact False.elim (nonempty rfl)
  | cons category categories =>
      intro vanishing
      have positive := NNReal.add_positive_left
        (right := NNReal.additiveLaws.listSum (categories.map fun category =>
          NNReal.ofReal (exp (logWeights category))))
        (exp_weight_positive (logWeights category))
      exact positive.2 (by
        show NNReal.le (NNReal.add _ _) NNReal.zero
        exact vanishing ▸ NNReal.le_refl _)

/-- The log-weight law is a probability on every nonempty list. -/
public theorem logCategorical_isProbability {categories : List ι} (nonempty : categories ≠ [])
    (logWeights : ι → Carrier) : Measure.IsProbability (logCategorical categories logWeights) :=
  categorical_isProbability categories (logCategorical_total_ne_zero nonempty logWeights)

private theorem exp_weight_add (first second : Carrier) :
    NNReal.ofReal (exp (add first second)) =
      NNReal.mul (NNReal.ofReal (exp first)) (NNReal.ofReal (exp second)) := by
  apply NNReal.ext
  rw [NNReal.toReal_mul, NNReal.toReal_ofReal (exp_positive _).1,
    NNReal.toReal_ofReal (exp_positive _).1, NNReal.toReal_ofReal (exp_positive _).1, exp_add]

/-- A common shift of the log weights leaves the law unchanged. -/
public theorem logCategorical_shift (categories : List ι) (logWeights : ι → Carrier)
    (shift : Carrier) :
    logCategorical categories (fun category => add (logWeights category) shift) =
      logCategorical categories logWeights := by
  unfold logCategorical
  have factored : (fun category => NNReal.ofReal (exp (add (logWeights category) shift))) =
      (fun category => NNReal.mul (NNReal.ofReal (exp shift))
        (NNReal.ofReal (exp (logWeights category)))) := by
    funext category
    rw [exp_weight_add, NNReal.mul_comm]
  rw [factored]
  exact categorical_scale categories
    (fun vanishing => (exp_weight_positive shift).2 (vanishing ▸ NNReal.le_refl _)) _

/-- Weighting a log-weight law by `exp ℓ'` adds the log weights, with a
positive finite scale on every nonempty list. -/
public theorem withDensity_logCategorical {categories : List ι} (nonempty : categories ≠ [])
    (first second : ι → Carrier) :
    (logCategorical categories first).withDensity
        (fun category => ENNReal.ofReal (exp (second category))) =
      Measure.smul (ENNReal.finite (NNReal.div
          (NNReal.additiveLaws.listSum (categories.map fun category =>
            NNReal.ofReal (exp (add (first category) (second category)))))
          (NNReal.additiveLaws.listSum (categories.map fun category =>
            NNReal.ofReal (exp (first category))))))
        (logCategorical categories (fun category => add (first category) (second category))) := by
  have product : (fun category => NNReal.ofReal (exp (add (first category) (second category)))) =
      (fun category => NNReal.mul (NNReal.ofReal (exp (first category)))
        (NNReal.ofReal (exp (second category)))) :=
    funext fun category => exp_weight_add _ _
  unfold logCategorical
  rw [product]
  exact withDensity_categorical categories _ _
    (product ▸ logCategorical_total_ne_zero nonempty _)

end

end Problib.Analysis
