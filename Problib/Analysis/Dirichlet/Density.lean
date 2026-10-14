module

public import Problib.Analysis.Gamma.Beta
public import Problib.Measure.Real.Simplex
public import Problib.Algebra.Product
public import Problib.Measure.Normalization
public import Problib.Measure.Kernel.Density.Normalized
import Problib.Measure.Kernel.Product
import Problib.Measure.Integral.Density.Algebra
import Problib.Real.Grind

/-! The Dirichlet family on the open simplex.

`Dirichlet.weight concentration point` is `∏ wᵢ^(αᵢ-1)`, a product of shape
powers, so it vanishes unless every coordinate is positive. `simplexIntegral`
integrates the weight of a simplex point over its free coordinates, with the
leading shape on the leftover coordinate `1 - Σv`.

Integrating the first free coordinate first against product Lebesgue measure
gives a Beta integral with budget equal to the leftover. That merges the
coordinate's shape into the leading one (`simplexIntegral_succ`). The Beta–Gamma
identity telescopes the merges into `B(α)·Γ(Σα) = ∏Γ(αᵢ)`
(`mass_mul_gammaIntegral`) at every concentration. It makes the mass finite and
positive at positive concentrations. It makes the mass infinite when one
concentration is zero and the rest are nonnegative with a positive total.

`Dirichlet.law` is the normalized family of the weight against the simplex
reference (`family`), so `Dirichlet.kernel` is measurable in the
concentration. Every law is a probability measure. At positive concentrations
it is the normalization of the weighted reference (`law_eq_normalize`) with
density `weight/B(α)` (`law_eq_withDensity`). With one concentration zero and a
positive total, the mass is infinite and the law is the fallback point mass at
the leading vertex (`law_zero_concentration`). That fallback is arbitrary: the
Dirichlet family has no single degenerate limit. -/

set_option autoImplicit false

open scoped Problib.Real.AC

namespace Problib.Analysis.Dirichlet

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

/-- The unnormalized Dirichlet density `∏ wᵢ^(αᵢ-1)`, zero unless every
coordinate is positive. -/
@[expose] public def weight : (count : Nat) → (Fin count → Carrier) →
    (Fin count → Carrier) → ENNReal
  | 0, _, _ => ENNReal.one
  | count + 1, concentration, point =>
      ENNReal.mul (shapePower (concentration 0) (point 0))
        (weight count (finTail count concentration) (finTail count point))

public theorem weight_measurable : (count : Nat) → (concentration : Fin count → Carrier) →
    ENNRealMeasurable (Space.pi (fun _ : Fin count => borel)) (weight count concentration)
  | 0, _ => ENNRealMeasurable.constant _ ENNReal.one
  | count + 1, concentration =>
      ((shapePower_measurable (concentration 0)).comp
          (Space.coordinate_measurable (fun _ : Fin (count + 1) => borel) 0)).mul
        ((weight_measurable count (finTail count concentration)).comp (finTail_measurable count))

/-- The weight is jointly measurable in the concentration and the point. -/
public theorem weight_jointly_measurable : (count : Nat) →
    ENNRealMeasurable
      (Space.product (Space.pi (fun _ : Fin count => borel))
        (Space.pi (fun _ : Fin count => borel)))
      (fun pair => weight count pair.1 pair.2)
  | 0 => ENNRealMeasurable.constant _ ENNReal.one
  | count + 1 =>
      (shapePower_jointly_measurable.comp (Space.pair_measurable
          (MeasurableMap.comp (Space.coordinate_measurable (fun _ : Fin (count + 1) => borel) 0)
            (Space.first_measurable _ _))
          (MeasurableMap.comp (Space.coordinate_measurable (fun _ : Fin (count + 1) => borel) 0)
            (Space.second_measurable _ _)))).mul
        ((weight_jointly_measurable count).comp (Space.pair_measurable
          (MeasurableMap.comp (finTail_measurable count) (Space.first_measurable _ _))
          (MeasurableMap.comp (finTail_measurable count) (Space.second_measurable _ _))))

/-- The weight vanishes at a point with a coordinate that is not positive. -/
public theorem weight_of_nonpositive : (count : Nat) → (concentration point : Fin count → Carrier) →
    (index : Fin count) → le (point index) zero →
    weight count concentration point = ENNReal.zero
  | 0, _, _, index, _ => Fin.elim0 index
  | count + 1, concentration, point, index, nonpositive => by
      show ENNReal.mul (shapePower (concentration 0) (point 0))
        (weight count (finTail count concentration) (finTail count point)) = ENNReal.zero
      rcases Fin.eq_zero_or_eq_succ index with rfl | ⟨earlier, rfl⟩
      · rw [shapePower_of_nonpositive _ nonpositive, ENNReal.zero_mul]
      · rw [weight_of_nonpositive count _ _ earlier nonpositive, ENNReal.mul_zero]

/-- The Dirichlet weight at the simplex point with free coordinates `point`:
shape `leading` on the leftover coordinate and shapes `free` on the free
coordinates. -/
@[expose] public def simplexWeight (dimension : Nat) (leading : Carrier)
    (free point : Fin dimension → Carrier) : ENNReal :=
  ENNReal.mul (shapePower leading (sub one (additiveLaws.finSum dimension point)))
    (weight dimension free point)

public theorem simplexWeight_measurable (dimension : Nat) (leading : Carrier)
    (free : Fin dimension → Carrier) :
    ENNRealMeasurable (Space.pi (fun _ : Fin dimension => borel))
      (simplexWeight dimension leading free) :=
  ((shapePower_measurable leading).comp (measurable_sub (MeasurableMap.constant _ borel one)
      (finSum_measurable dimension))).mul (weight_measurable dimension free)

/-- The simplex weight vanishes off the free region of the open simplex. -/
public theorem simplexWeight_of_not_mem {dimension : Nat} {point : Fin dimension → Carrier}
    (outside : ¬simplexRegion dimension point) (leading : Carrier)
    (free : Fin dimension → Carrier) :
    simplexWeight dimension leading free point = ENNReal.zero := by
  classical
  unfold simplexWeight
  by_cases positive : ∀ index, lt zero (point index)
  · have above : le one (additiveLaws.finSum dimension point) :=
      not_lt_iff_le.mp (fun below => outside ⟨positive, below⟩)
    have gap : le (sub one (additiveLaws.finSum dimension point)) zero := by
      apply not_lt_iff_le.mp
      intro gapPositive
      exact lt_irrefl _ (lt_of_lt_of_le (sub_positive_iff.mp gapPositive) above)
    rw [shapePower_of_nonpositive _ gap, ENNReal.zero_mul]
  · rcases Classical.not_forall.mp positive with ⟨index, notPositive⟩
    rw [weight_of_nonpositive dimension free point index (not_lt_iff_le.mp notPositive),
      ENNReal.mul_zero]

/-- The integral of the simplex weight over the free coordinates. -/
@[expose] public def simplexIntegral (dimension : Nat) (leading : Carrier)
    (free : Fin dimension → Carrier) : ENNReal :=
  lintegral (volumePi dimension) (simplexWeight dimension leading free)

/-- With no free coordinate, the leftover is one and so is the integral. -/
public theorem simplexIntegral_zero (leading : Carrier) (free : Fin 0 → Carrier) :
    simplexIntegral 0 leading free = ENNReal.one := by
  unfold simplexIntegral
  rw [volumePi_zero, lintegral_dirac _ _ (simplexWeight_measurable 0 leading free)]
  show ENNReal.mul (shapePower leading (sub one zero)) ENNReal.one = ENNReal.one
  rw [sub_zero, shapePower_of_positive _ one_positive, one_rpow, ENNReal.ofReal_one,
    ENNReal.mul_one]

private theorem leftover_split (value first rest : Carrier) :
    sub value (add first rest) = sub (sub value rest) first := by
  real_grind

/-- Integrating the first free coordinate first is a Beta integral at the
leftover budget. It merges that coordinate's shape into the leading one. -/
public theorem simplexIntegral_succ (dimension : Nat) (leading : Carrier)
    (free : Fin (dimension + 1) → Carrier) :
    simplexIntegral (dimension + 1) leading free =
      ENNReal.mul (betaIntegral (free 0) leading)
        (simplexIntegral dimension (add (free 0) leading) (finTail dimension free)) := by
  have joint : ENNRealMeasurable (Space.product borel (Space.pi (fun _ : Fin dimension => borel)))
      (fun pair => simplexWeight (dimension + 1) leading free (finCons dimension pair)) :=
    (simplexWeight_measurable (dimension + 1) leading free).comp (finCons_measurable dimension)
  have column : ∀ rest : Fin dimension → Carrier,
      lintegral volume (fun value =>
        simplexWeight (dimension + 1) leading free (finCons dimension (value, rest))) =
      ENNReal.mul (betaIntegral (free 0) leading)
        (simplexWeight dimension (add (free 0) leading) (finTail dimension free) rest) := by
    intro rest
    have pointwise : (fun value =>
        simplexWeight (dimension + 1) leading free (finCons dimension (value, rest))) =
        (fun value => ENNReal.mul (weight dimension (finTail dimension free) rest)
          (Beta.weight (free 0) leading (sub one (additiveLaws.finSum dimension rest)) value)) := by
      funext value
      show ENNReal.mul
          (shapePower leading (sub one (add value (additiveLaws.finSum dimension rest))))
          (ENNReal.mul (shapePower (free 0) value) (weight dimension (finTail dimension free) rest)) =
        ENNReal.mul (weight dimension (finTail dimension free) rest)
          (ENNReal.mul (shapePower (free 0) value)
            (shapePower leading (sub (sub one (additiveLaws.finSum dimension rest)) value)))
      rw [leftover_split]
      ac_rfl
    rw [pointwise, lintegral_smul _ _ (Beta.weight_measurable _ _ _), Beta.lintegral_weight]
    unfold simplexWeight
    ac_rfl
  unfold simplexIntegral
  rw [volumePi_succ, lintegral_map _ _ _ (simplexWeight_measurable (dimension + 1) leading free),
    lintegral_prod_symm _ _ volumeSFinite (volumePiSFinite dimension) joint,
    ← lintegral_smul _ _ (simplexWeight_measurable dimension _ _)]
  exact congrArg (lintegral (volumePi dimension)) (funext column)

/-- The simplex integral times the Gamma integral at the total shape is the
product of the Gamma integrals, at every shape. -/
public theorem simplexIntegral_mul_gammaIntegral : (dimension : Nat) → (leading : Carrier) →
    (free : Fin dimension → Carrier) →
    ENNReal.mul (simplexIntegral dimension leading free)
        (gammaIntegral (add leading (additiveLaws.finSum dimension free))) =
      ENNReal.mul (gammaIntegral leading)
        (ENNReal.multiplicativeLaws.finProduct dimension fun index => gammaIntegral (free index))
  | 0, leading, free => by
      rw [simplexIntegral_zero, ENNReal.one_mul]
      show gammaIntegral (add leading zero) = ENNReal.mul (gammaIntegral leading) ENNReal.one
      rw [add_zero, ENNReal.mul_one]
  | dimension + 1, leading, free => by
      have previous := simplexIntegral_mul_gammaIntegral dimension (add (free 0) leading)
        (finTail dimension free)
      have merged := gammaIntegral_mul_gammaIntegral (free 0) leading
      have total : add leading (additiveLaws.finSum (dimension + 1) free) =
          add (add (free 0) leading) (additiveLaws.finSum dimension (finTail dimension free)) := by
        show add leading (add (free 0) (additiveLaws.finSum dimension (finTail dimension free))) = _
        ac_rfl
      let rest := ENNReal.multiplicativeLaws.finProduct dimension fun index =>
        gammaIntegral (finTail dimension free index)
      rw [simplexIntegral_succ, total]
      calc ENNReal.mul (ENNReal.mul (betaIntegral (free 0) leading)
              (simplexIntegral dimension (add (free 0) leading) (finTail dimension free)))
            (gammaIntegral (add (add (free 0) leading)
              (additiveLaws.finSum dimension (finTail dimension free))))
          = ENNReal.mul (betaIntegral (free 0) leading)
              (ENNReal.mul (gammaIntegral (add (free 0) leading)) rest) := by
            rw [ENNReal.mul_assoc, previous]
        _ = ENNReal.mul (ENNReal.mul (gammaIntegral (add (free 0) leading))
              (betaIntegral (free 0) leading)) rest := by ac_rfl
        _ = ENNReal.mul (ENNReal.mul (gammaIntegral (free 0)) (gammaIntegral leading)) rest := by
            rw [← merged]
        _ = ENNReal.mul (gammaIntegral leading)
              (ENNReal.multiplicativeLaws.finProduct (dimension + 1) fun index =>
                gammaIntegral (free index)) := by
            show _ = ENNReal.mul (gammaIntegral leading)
              (ENNReal.mul (gammaIntegral (free 0)) rest)
            ac_rfl

/-- The Dirichlet mass `∫ ∏ wᵢ^(αᵢ-1)` over the simplex, the multivariate Beta
integral of the concentration. -/
@[expose] public def mass {dimension : Nat} (concentration : Fin (dimension + 1) → Carrier) :
    ENNReal :=
  lintegral (simplex dimension) (weight (dimension + 1) concentration)

/-- The mass is the simplex integral with the leading concentration on the
leftover coordinate. -/
public theorem mass_eq_simplexIntegral {dimension : Nat}
    (concentration : Fin (dimension + 1) → Carrier) :
    mass concentration =
      simplexIntegral dimension (concentration 0) (finTail dimension concentration) := by
  classical
  unfold mass simplexIntegral
  rw [lintegral_simplex dimension (weight_measurable (dimension + 1) concentration)]
  apply congrArg (lintegral (volumePi dimension))
  funext point
  by_cases member : simplexRegion dimension point
  · rw [ennrealIndicator_of_mem member]
    rfl
  · rw [ennrealIndicator_of_not_mem member]
    exact (simplexWeight_of_not_mem member _ _).symm

/-- `B(α)·Γ(Σα) = ∏ Γ(αᵢ)` at every concentration. -/
public theorem mass_mul_gammaIntegral {dimension : Nat}
    (concentration : Fin (dimension + 1) → Carrier) :
    ENNReal.mul (mass concentration)
        (gammaIntegral (additiveLaws.finSum (dimension + 1) concentration)) =
      ENNReal.multiplicativeLaws.finProduct (dimension + 1) fun index =>
        gammaIntegral (concentration index) := by
  rw [mass_eq_simplexIntegral]
  exact simplexIntegral_mul_gammaIntegral dimension (concentration 0)
    (finTail dimension concentration)

/-- Euler's integral vanishes at no nonnegative shape. -/
private theorem gammaIntegral_ne_zero {shape : Carrier} (nonnegative : le zero shape) :
    gammaIntegral shape ≠ ENNReal.zero := by
  classical
  by_cases positive : lt zero shape
  · exact ENNReal.zero_lt_iff_ne_zero.mp (gammaIntegral_positive positive)
  · rw [le_antisymm (not_lt_iff_le.mp positive) nonnegative, gammaIntegral_zero_eq_top]
    intro vanishing
    exact ENNReal.finite_iff_ne_top.mp (show ENNReal.Finite ENNReal.zero from True.intro)
      vanishing.symm

/-- The Dirichlet mass is finite at positive concentrations. -/
public theorem mass_finite {dimension : Nat} {concentration : Fin (dimension + 1) → Carrier}
    (positive : ∀ index, lt zero (concentration index)) :
    ENNReal.Finite (mass concentration) := by
  have identity := mass_mul_gammaIntegral concentration
  rw [ENNReal.finite_iff_ne_top]
  intro infinite
  rw [infinite, ENNReal.top_mul_of_ne_zero (ENNReal.zero_lt_iff_ne_zero.mp
    (gammaIntegral_positive (finSum_positive dimension positive)))] at identity
  exact ENNReal.finite_iff_ne_top.mp
    (ENNReal.finProduct_finite (dimension + 1)
      fun index => gammaIntegral_finite (positive index))
    identity.symm

/-- The Dirichlet mass is positive at positive concentrations. -/
public theorem mass_positive {dimension : Nat} {concentration : Fin (dimension + 1) → Carrier}
    (positive : ∀ index, lt zero (concentration index)) :
    ENNReal.lt ENNReal.zero (mass concentration) := by
  apply ENNReal.zero_lt_iff_ne_zero.mpr
  intro vanishing
  have identity := mass_mul_gammaIntegral concentration
  rw [vanishing, ENNReal.zero_mul] at identity
  exact ENNReal.finProduct_ne_zero (dimension + 1)
    (fun index => ENNReal.zero_lt_iff_ne_zero.mp (gammaIntegral_positive (positive index)))
    identity.symm

/-- A zero concentration makes the mass infinite when the others are
nonnegative with a positive total. Positivity of every concentration is
necessary for `mass_finite`. -/
public theorem mass_eq_top_of_zero {dimension : Nat}
    {concentration : Fin (dimension + 1) → Carrier}
    (nonnegative : ∀ index, le zero (concentration index))
    (totalPositive : lt zero (additiveLaws.finSum (dimension + 1) concentration))
    (index : Fin (dimension + 1)) (vanishing : concentration index = zero) :
    mass concentration = ENNReal.top := by
  have identity := mass_mul_gammaIntegral concentration
  rw [ENNReal.finProduct_eq_top (dimension + 1)
    (fun index => gammaIntegral_ne_zero (nonnegative index)) index
    (by rw [vanishing]; exact gammaIntegral_zero_eq_top)] at identity
  apply Classical.byContradiction
  intro finite
  have bounded := ENNReal.mul_finite (ENNReal.finite_iff_ne_top.mpr finite)
    (gammaIntegral_finite totalPositive)
  rw [identity] at bounded
  exact ENNReal.finite_iff_ne_top.mp bounded rfl

/-- With a zero concentration, the weighted simplex reference has infinite mass
and cannot be normalized. -/
public theorem weight_not_normalizable {dimension : Nat}
    {concentration : Fin (dimension + 1) → Carrier}
    (nonnegative : ∀ index, le zero (concentration index))
    (totalPositive : lt zero (additiveLaws.finSum (dimension + 1) concentration))
    (index : Fin (dimension + 1)) (vanishing : concentration index = zero) :
    ¬Measure.IsNormalizable
      ((simplex dimension).withDensity (weight (dimension + 1) concentration)) := by
  apply Measure.infinite_not_normalizable
  rw [Measure.withDensity_apply _ _ (Space.univ _), Measure.restrict_univ]
  exact mass_eq_top_of_zero nonnegative totalPositive index vanishing

private theorem mass_toReal_positive {dimension : Nat}
    {concentration : Fin (dimension + 1) → Carrier}
    (positive : ∀ index, lt zero (concentration index)) :
    lt zero (ENNReal.toReal (mass concentration)) := by
  have massPositive := mass_positive positive
  rw [← ENNReal.ofReal_toReal (mass_finite positive), ← ENNReal.ofReal_zero] at massPositive
  exact (ENNReal.ofReal_lt_ofReal_iff (le_refl zero) (ENNReal.toReal_nonnegative _)).mp
    massPositive

/-- The mass times the reciprocal of its real value is one. -/
public theorem mass_mul_inverse {dimension : Nat} {concentration : Fin (dimension + 1) → Carrier}
    (positive : ∀ index, lt zero (concentration index)) :
    ENNReal.mul (mass concentration)
      (ENNReal.ofReal (inverse (ENNReal.toReal (mass concentration)))) = ENNReal.one := by
  have projected := ENNReal.ofReal_toReal (mass_finite positive)
  calc ENNReal.mul (mass concentration)
        (ENNReal.ofReal (inverse (ENNReal.toReal (mass concentration))))
      = ENNReal.mul (ENNReal.ofReal (ENNReal.toReal (mass concentration)))
          (ENNReal.ofReal (inverse (ENNReal.toReal (mass concentration)))) := by
        rw [projected]
    _ = ENNReal.one := ofReal_mul_ofReal_inverse (mass_toReal_positive positive)

/-- The Dirichlet density against the simplex reference, `∏ wᵢ^(αᵢ-1)/B(α)`. -/
@[expose] public def density {dimension : Nat} (concentration : Fin (dimension + 1) → Carrier)
    (point : Fin (dimension + 1) → Carrier) : ENNReal :=
  ENNReal.mul (ENNReal.ofReal (inverse (ENNReal.toReal (mass concentration))))
    (weight (dimension + 1) concentration point)

public theorem density_measurable {dimension : Nat}
    (concentration : Fin (dimension + 1) → Carrier) :
    ENNRealMeasurable (Space.pi (fun _ : Fin (dimension + 1) => borel)) (density concentration) :=
  (ENNRealMeasurable.constant _ _).mul (weight_measurable (dimension + 1) concentration)

/-- The weighted simplex reference is normalizable at positive concentrations. -/
public theorem weight_normalizable {dimension : Nat}
    {concentration : Fin (dimension + 1) → Carrier}
    (positive : ∀ index, lt zero (concentration index)) :
    Measure.IsNormalizable
      ((simplex dimension).withDensity (weight (dimension + 1) concentration)) where
  finite := ⟨by
    rw [Measure.withDensity_apply _ _ (Space.univ _), Measure.restrict_univ]
    exact mass_finite positive⟩
  nonzero := by
    rw [Measure.withDensity_apply _ _ (Space.univ _), Measure.restrict_univ]
    exact ENNReal.zero_lt_iff_ne_zero.mp (mass_positive positive)

/-- The Dirichlet family on `dimension + 1` coordinates: the weight against the
simplex reference. Its constant fallback, the leading vertex, is arbitrary,
because the family has no single degenerate limit. -/
@[expose] public def family (dimension : Nat) :
    Kernel.NormalizedFamily (Space.pi (fun _ : Fin (dimension + 1) => borel))
      (Space.pi (fun _ : Fin (dimension + 1) => borel)) where
  reference := simplex dimension
  referenceFinite := simplexSFinite dimension
  weight := weight (dimension + 1)
  weight_measurable := weight_jointly_measurable (dimension + 1)
  fallback _ := simplexPoint dimension (fun _ => zero)
  fallback_measurable := MeasurableMap.constant _ _ (simplexPoint dimension (fun _ => zero))

/-- The family's normalizer is the Dirichlet mass `B(α)`. -/
public theorem family_normalizer {dimension : Nat}
    (concentration : Fin (dimension + 1) → Carrier) :
    (family dimension).normalizer concentration = mass concentration :=
  rfl

/-- A jointly measurable Dirichlet kernel over all concentrations. -/
@[expose] public def kernel (dimension : Nat) :
    Kernel (Space.pi (fun _ : Fin (dimension + 1) => borel))
      (Space.pi (fun _ : Fin (dimension + 1) => borel)) :=
  (family dimension).kernel

/-- The Dirichlet law on the open simplex. -/
@[expose] public def law {dimension : Nat} (concentration : Fin (dimension + 1) → Carrier) :
    Measure (Space.pi (fun _ : Fin (dimension + 1) => borel)) :=
  (family dimension).law concentration

public theorem kernel_apply {dimension : Nat} (concentration : Fin (dimension + 1) → Carrier) :
    kernel dimension concentration = law concentration :=
  rfl

/-- Every Dirichlet law is a probability measure. -/
public theorem law_isProbability {dimension : Nat}
    (concentration : Fin (dimension + 1) → Carrier) :
    Measure.IsProbability (law concentration) :=
  (family dimension).law_isProbability concentration

/-- The Dirichlet law is the normalization of the weight on the simplex. -/
public theorem law_eq_normalize {dimension : Nat}
    {concentration : Fin (dimension + 1) → Carrier}
    (positive : ∀ index, lt zero (concentration index)) :
    law concentration = Measure.normalize
      ((simplex dimension).withDensity (weight (dimension + 1) concentration))
      (weight_normalizable positive) :=
  (family dimension).law_eq_normalize (weight_normalizable positive)

/-- At positive concentrations the law is the simplex reference weighted by
the density. -/
public theorem law_eq_withDensity {dimension : Nat}
    {concentration : Fin (dimension + 1) → Carrier}
    (positive : ∀ index, lt zero (concentration index)) :
    law concentration = (simplex dimension).withDensity (density concentration) :=
  (family dimension).law_eq_of_scale
    ((ENNReal.mul_comm _ _).trans (mass_mul_inverse positive)) (fun _ => rfl)

/-- With one concentration zero, the rest nonnegative and a positive total, the
law is the fallback point mass at the leading vertex. -/
public theorem law_zero_concentration {dimension : Nat}
    {concentration : Fin (dimension + 1) → Carrier}
    (nonnegative : ∀ index, le zero (concentration index))
    (totalPositive : lt zero (additiveLaws.finSum (dimension + 1) concentration))
    (index : Fin (dimension + 1)) (vanishing : concentration index = zero) :
    law concentration = Measure.dirac _ (simplexPoint dimension (fun _ => zero)) :=
  (family dimension).law_eq_dirac
    (weight_not_normalizable nonnegative totalPositive index vanishing)

end

end Problib.Analysis.Dirichlet
