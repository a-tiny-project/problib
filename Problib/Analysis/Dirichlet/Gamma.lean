module

public import Problib.Analysis.Dirichlet.Density
public import Problib.Analysis.Gamma.Density
public import Problib.Measure.Real.Dilation
public import Problib.Measure.Kernel.Product.Finite
import Problib.Measure.Kernel.RadonNikodym.Product
import Problib.Measure.Kernel.Product
import Problib.Measure.Kernel.Measurable
import Problib.Measure.Integral.Lebesgue.Transport
import Problib.Measure.Integral.Density.Change
import Problib.Real.Grind

/-! Normalized independent Gamma draws are Dirichlet.

Draw `gᵢ ~ Gamma(αᵢ, 1)` independently, one lane per concentration (`gammas`).
The normalized vector `g/Σg` and the total `Σg` are independent, with laws
`Dirichlet.law α` and `Gamma(Σα, 1)` (`gammas_map_normalize_total`). Forgetting
the total gives `gammas_map_normalize`: normalized Gammas have law
`Dirichlet.law α`.

The proof is one change of variables in `dimension + 1` coordinates. The total
`s` replaces the leading coordinate (`lintegral_volumePi_total`), and the free
coordinates are the simplex's free coordinates dilated by `s`
(`lintegral_volumePi_scale`). At the dilated simplex point every lane's shape
power gives a power of `s`, and the lanes' exponentials multiply to `e^(-s)`.
With the Jacobian `s^dimension` the product is the Gamma weight at the total
shape, times the Dirichlet weight (`lineWeights_simplexPoint`). The normalizers
match by `B(α)·Γ(Σα) = ∏Γ(αᵢ)` (`gammaScale_eq`).
-/

set_option autoImplicit false

open scoped Problib.Real.AC

namespace Problib.Analysis.Dirichlet

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

noncomputable section

/-! ### Independent Gamma draws -/

/-- Reading one lane's shape at rate one is measurable. -/
public theorem laneShape_measurable (count : Nat) (lane : Fin count) :
    MeasurableMap (Space.pi (fun _ : Fin count => borel)) (Space.product borel borel)
      (fun shapes => (shapes lane, one)) :=
  Space.pair_measurable (Space.coordinate_measurable (fun _ : Fin count => borel) lane)
    (MeasurableMap.constant _ borel one)

/-- One lane's rate-one Gamma law, as a kernel of all the shapes. -/
@[expose] public def gammaLane (count : Nat) (lane : Fin count) :
    Kernel (Space.pi (fun _ : Fin count => borel)) borel :=
  Gamma.kernel.precomp (fun shapes => (shapes lane, one)) (laneShape_measurable count lane)

@[expose] public def gammaLane_finite (count : Nat) (lane : Fin count) :
    Kernel.IsSFinite (gammaLane count lane) :=
  Kernel.IsSFinite.ofMarkov (fun shapes => Gamma.law_isProbability (shapes lane) one)

/-- Independent rate-one Gamma draws, one per lane, at the given shapes. -/
@[expose] public def gammas (count : Nat) :
    Kernel (Space.pi (fun _ : Fin count => borel)) (Space.pi (fun _ : Fin count => borel)) :=
  Kernel.finProduct count (gammaLane count) (gammaLane_finite count)

/-- Independent draws are probability measures. -/
public theorem gammas_isProbability (count : Nat) (shapes : Fin count → Carrier) :
    Measure.IsProbability (gammas count shapes) :=
  Kernel.finProduct_markov count _ _
    (fun lane shapes => Gamma.law_isProbability (shapes lane) one) shapes

/-! ### The density of independent draws -/

/-- At rate one, the Gamma law is volume weighted by `1/Γ(α)` times the line
weight. -/
public theorem law_one_eq_withDensity {shape : Carrier} (positive : lt zero shape) :
    Gamma.law shape one = volume.withDensity (fun value =>
      ENNReal.mul (ENNReal.ofReal (inverse (gamma shape))) (Gamma.lineWeight shape one value)) := by
  apply Gamma.family.law_eq_of_scale _ (fun _ => rfl)
  show ENNReal.mul _ (lintegral volume (Gamma.lineWeight shape one)) = ENNReal.one
  have integral : lintegral volume (Gamma.lineWeight shape one) = gammaIntegral shape :=
    (gammaIntegral_eq_lintegral shape).symm
  rw [integral, ← ofReal_gamma positive, ENNReal.mul_comm]
  exact ofReal_mul_ofReal_inverse (gamma_positive positive)

public theorem lineWeight_one_measurable (shape : Carrier) :
    ENNRealMeasurable borel (Gamma.lineWeight shape one) :=
  (shapePower_measurable shape).mul (Exponential.weight_measurable one)

/-- The product of the lanes' Gamma line weights at rate one, lane `0` first. -/
@[expose] public def lineWeights : (count : Nat) → (Fin count → Carrier) →
    (Fin count → Carrier) → ENNReal
  | 0, _, _ => ENNReal.one
  | count + 1, shapes, point =>
      ENNReal.mul (Gamma.lineWeight (shapes 0) one (point 0))
        (lineWeights count (finTail count shapes) (finTail count point))

public theorem lineWeights_measurable : (count : Nat) → (shapes : Fin count → Carrier) →
    ENNRealMeasurable (Space.pi (fun _ : Fin count => borel)) (lineWeights count shapes)
  | 0, _ => ENNRealMeasurable.constant _ ENNReal.one
  | count + 1, shapes =>
      ((lineWeight_one_measurable (shapes 0)).comp
          (Space.coordinate_measurable (fun _ : Fin (count + 1) => borel) 0)).mul
        ((lineWeights_measurable count (finTail count shapes)).comp (finTail_measurable count))

/-- The line weights vanish at a point with a coordinate that is not positive. -/
public theorem lineWeights_of_nonpositive : (count : Nat) → (shapes point : Fin count → Carrier) →
    (index : Fin count) → le (point index) zero → lineWeights count shapes point = ENNReal.zero
  | 0, _, _, index, _ => Fin.elim0 index
  | count + 1, shapes, point, index, nonpositive => by
      show ENNReal.mul (ENNReal.mul (shapePower (shapes 0) (point 0)) _) _ = ENNReal.zero
      rcases Fin.eq_zero_or_eq_succ index with rfl | ⟨earlier, rfl⟩
      · rw [shapePower_of_nonpositive _ nonpositive, ENNReal.zero_mul, ENNReal.zero_mul]
      · rw [lineWeights_of_nonpositive count _ _ earlier nonpositive, ENNReal.mul_zero]

/-- `∏ 1/Γ(αᵢ)`, lane `0` first. -/
@[expose] public def gammaScale : (count : Nat) → (Fin count → Carrier) → ENNReal
  | 0, _ => ENNReal.one
  | count + 1, shapes =>
      ENNReal.mul (ENNReal.ofReal (inverse (gamma (shapes 0))))
        (gammaScale count (finTail count shapes))

/-- The lanes' densities multiply to `∏ 1/Γ(αᵢ)` times the line weights. -/
private theorem finProductDensity_eq {σ : Type} : (count : Nat) → (shapes : Fin count → Carrier) →
    (input : σ) → (point : Fin count → Carrier) →
    Kernel.finProductDensity count (fun lane (_ : σ) value =>
        ENNReal.mul (ENNReal.ofReal (inverse (gamma (shapes lane))))
          (Gamma.lineWeight (shapes lane) one value)) input point =
      ENNReal.mul (gammaScale count shapes) (lineWeights count shapes point)
  | 0, _, _, _ => (ENNReal.one_mul _).symm
  | count + 1, shapes, input, point => by
      show ENNReal.mul (ENNReal.mul _ _) (Kernel.finProductDensity count (fun lane (_ : σ) value =>
        ENNReal.mul (ENNReal.ofReal (inverse (gamma (finTail count shapes lane))))
          (Gamma.lineWeight (finTail count shapes lane) one value)) input (finTail count point)) = _
      rw [finProductDensity_eq count (finTail count shapes) input (finTail count point)]
      show _ = ENNReal.mul (ENNReal.mul _ _) (ENNReal.mul _ _)
      ac_rfl

/-- Independent draws at positive shapes have density `∏ 1/Γ(αᵢ)` times the
line weights against volume. -/
public theorem gammas_eq_withDensity {count : Nat} {shapes : Fin count → Carrier}
    (positive : ∀ lane, lt zero (shapes lane)) :
    gammas count shapes = (volumePi count).withDensity (fun point =>
      ENNReal.mul (gammaScale count shapes) (lineWeights count shapes point)) := by
  let source := Space.pi (fun _ : Fin count => borel)
  let lanes : Fin count → Kernel source borel := fun lane =>
    Kernel.const source (Gamma.law (shapes lane) one)
  let lanesFinite : ∀ lane, Kernel.IsSFinite (lanes lane) := fun lane =>
    Kernel.IsSFinite.ofMarkov (fun _ => Gamma.law_isProbability (shapes lane) one)
  let derivative : ∀ lane, Kernel.RadonNikodymDerivative (lanes lane) (Kernel.const source volume) :=
    fun lane => {
      density := fun _ value => ENNReal.mul (ENNReal.ofReal (inverse (gamma (shapes lane))))
        (Gamma.lineWeight (shapes lane) one value)
      density_measurable := ((ENNRealMeasurable.constant _ _).mul
        (lineWeight_one_measurable (shapes lane))).comp (Space.second_measurable _ _)
      reconstruct := fun _ => law_one_eq_withDensity (positive lane) }
  have same : gammas count shapes = Kernel.finProduct count lanes lanesFinite shapes :=
    Kernel.finProduct_congr_at count _ _ _ _ shapes shapes fun _ => rfl
  rw [same, Kernel.finProduct_withDensity count lanes (fun _ => Kernel.const source volume)
      lanesFinite (fun _ => Kernel.IsSFinite.const source volumeSFinite) derivative shapes,
    finProduct_const_volume source count shapes]
  congr 1
  funext point
  exact finProductDensity_eq count shapes shapes point

/-! ### The dilated simplex point -/

/-- The coordinates over their sum. -/
@[expose] public def normalize (count : Nat) (point : Fin count → Carrier) : Fin count → Carrier :=
  fun index => div (point index) (additiveLaws.finSum count point)

public theorem normalize_measurable (count : Nat) :
    MeasurableMap (Space.pi (fun _ : Fin count => borel)) (Space.pi (fun _ : Fin count => borel))
      (normalize count) :=
  Space.pi_measurable (fun index =>
    measurable_div (Space.coordinate_measurable (fun _ : Fin count => borel) index)
      (finSum_measurable count))

private theorem exponential_scale (factor value : Carrier) :
    Exponential.weight one (mul factor value) = Exponential.weight factor value := by
  unfold Exponential.weight
  rw [one_mul]

private theorem exponential_zero (factor : Carrier) :
    Exponential.weight factor zero = ENNReal.one := by
  unfold Exponential.weight
  rw [mul_zero, neg_zero, exp_zero, ENNReal.ofReal_one]

/-- Dilating the point by a positive `s`: each lane's shape power gives
`s^(αᵢ-1)`, the Jacobian's `s` per lane makes it `s^αᵢ`, and the exponentials
multiply to the exponential of the dilated sum. -/
public theorem lineWeights_scale {factor : Carrier} (positive : lt zero factor) :
    (count : Nat) → (shapes point : Fin count → Carrier) →
    ENNReal.mul (ENNReal.pow (ENNReal.ofReal factor) count)
        (lineWeights count shapes (scalePi count factor point)) =
      ENNReal.mul (ENNReal.ofReal (rpow factor (additiveLaws.finSum count shapes)))
        (ENNReal.mul (weight count shapes point)
          (Exponential.weight factor (additiveLaws.finSum count point)))
  | 0, _, _ => by
      show ENNReal.mul ENNReal.one ENNReal.one =
        ENNReal.mul (ENNReal.ofReal (rpow factor zero))
          (ENNReal.mul ENNReal.one (Exponential.weight factor zero))
      rw [rpow_zero, ENNReal.ofReal_one, exponential_zero, ENNReal.one_mul, ENNReal.one_mul]
  | count + 1, shapes, point => by
      have rest := lineWeights_scale positive count (finTail count shapes) (finTail count point)
      have split : rpow factor (add (shapes 0) (additiveLaws.finSum count (finTail count shapes))) =
          mul factor (mul (rpow factor (sub (shapes 0) one))
            (rpow factor (additiveLaws.finSum count (finTail count shapes)))) := by
        rw [rpow_add positive]
        calc mul (rpow factor (shapes 0)) (rpow factor _)
            = mul (rpow factor (add one (sub (shapes 0) one))) (rpow factor
                (additiveLaws.finSum count (finTail count shapes))) := by rw [add_sub_cancel]
          _ = _ := by rw [rpow_add positive, rpow_one positive.1]; real_grind
      show ENNReal.mul (ENNReal.mul (ENNReal.ofReal factor) (ENNReal.pow _ count))
          (ENNReal.mul (ENNReal.mul (shapePower (shapes 0) (mul factor (point 0)))
            (Exponential.weight one (mul factor (point 0))))
            (lineWeights count (finTail count shapes) (scalePi count factor (finTail count point)))) =
        ENNReal.mul (ENNReal.ofReal (rpow factor
            (add (shapes 0) (additiveLaws.finSum count (finTail count shapes)))))
          (ENNReal.mul (ENNReal.mul (shapePower (shapes 0) (point 0))
              (weight count (finTail count shapes) (finTail count point)))
            (Exponential.weight factor
              (add (point 0) (additiveLaws.finSum count (finTail count point)))))
      rw [shapePower_mul positive, exponential_scale, Exponential.weight_add, split,
        ofReal_mul positive.1 (mul_nonnegative (rpow_nonnegative _ _) (rpow_nonnegative _ _)),
        ofReal_mul (rpow_nonnegative _ _) (rpow_nonnegative _ _)]
      calc _ = ENNReal.mul (ENNReal.mul (ENNReal.ofReal factor)
              (ENNReal.mul (ENNReal.ofReal (rpow factor (sub (shapes 0) one)))
                (ENNReal.mul (shapePower (shapes 0) (point 0))
                  (Exponential.weight factor (point 0)))))
            (ENNReal.mul (ENNReal.pow (ENNReal.ofReal factor) count)
              (lineWeights count (finTail count shapes)
                (scalePi count factor (finTail count point)))) := by ac_rfl
        _ = _ := by rw [rest]; ac_rfl

/-- Multiplying by a positive real's embedding is injective. -/
private theorem ofReal_mul_cancel {factor : Carrier} (positive : lt zero factor)
    {first second : ENNReal}
    (equal : ENNReal.mul (ENNReal.ofReal factor) first = ENNReal.mul (ENNReal.ofReal factor) second) :
    first = second := by
  have cancel := ofReal_mul_ofReal_inverse positive
  rw [ENNReal.mul_comm] at cancel
  calc first = ENNReal.mul (ENNReal.mul (ENNReal.ofReal (inverse factor)) (ENNReal.ofReal factor))
        first := by rw [cancel, ENNReal.one_mul]
    _ = ENNReal.mul (ENNReal.ofReal (inverse factor))
        (ENNReal.mul (ENNReal.ofReal factor) first) := ENNReal.mul_assoc _ _ _
    _ = ENNReal.mul (ENNReal.ofReal (inverse factor))
        (ENNReal.mul (ENNReal.ofReal factor) second) := by rw [equal]
    _ = second := by rw [← ENNReal.mul_assoc, cancel, ENNReal.one_mul]

/-- At the simplex point dilated by a positive total `s`, the Jacobian
`s^dimension` times the line weights is the Gamma weight at the total shape
times the Dirichlet weight. -/
public theorem lineWeights_simplexPoint {dimension : Nat} {total : Carrier}
    (positive : lt zero total) (shapes : Fin (dimension + 1) → Carrier)
    (free : Fin dimension → Carrier) :
    ENNReal.mul (ENNReal.pow (ENNReal.ofReal total) dimension)
        (lineWeights (dimension + 1) shapes
          (scalePi (dimension + 1) total (simplexPoint dimension free))) =
      ENNReal.mul (Gamma.lineWeight (additiveLaws.finSum (dimension + 1) shapes) one total)
        (weight (dimension + 1) shapes (simplexPoint dimension free)) := by
  apply ofReal_mul_cancel positive
  have scaled := lineWeights_scale positive (dimension + 1) shapes (simplexPoint dimension free)
  rw [ENNReal.pow_succ, ENNReal.mul_assoc] at scaled
  rw [scaled, finSum_simplexPoint]
  have split : rpow total (additiveLaws.finSum (dimension + 1) shapes) =
      mul total (rpow total (sub (additiveLaws.finSum (dimension + 1) shapes) one)) := by
    calc rpow total (additiveLaws.finSum (dimension + 1) shapes)
        = rpow total (add one (sub (additiveLaws.finSum (dimension + 1) shapes) one)) := by
          rw [add_sub_cancel]
      _ = _ := by rw [rpow_add positive, rpow_one positive.1]
  have exponential : Exponential.weight total one = Exponential.weight one total := by
    unfold Exponential.weight
    rw [mul_one, one_mul]
  show _ = ENNReal.mul (ENNReal.ofReal total)
    (ENNReal.mul (ENNReal.mul (shapePower _ total) (Exponential.weight one total)) _)
  rw [split, ofReal_mul positive.1 (rpow_nonnegative _ _), shapePower_of_positive _ positive,
    exponential]
  ac_rfl

/-! ### The change of variables -/

/-- The sum of a point whose leading coordinate is a total less the others is
that total. -/
private theorem finSum_shifted (dimension : Nat) (total : Carrier) (rest : Fin dimension → Carrier) :
    additiveLaws.finSum (dimension + 1)
        (finCons dimension (add (neg (additiveLaws.finSum dimension rest)) total, rest)) = total := by
  show add (add (neg (additiveLaws.finSum dimension rest)) total)
    (additiveLaws.finSum dimension rest) = total
  real_grind

/-- The total less the dilated free coordinates, followed by them, is the
dilated simplex point. -/
private theorem shifted_scalePi (dimension : Nat) (total : Carrier) (free : Fin dimension → Carrier) :
    finCons dimension (add (neg (additiveLaws.finSum dimension (scalePi dimension total free))) total,
        scalePi dimension total free) =
      scalePi (dimension + 1) total (simplexPoint dimension free) := by
  rw [simplexPoint, scalePi_finCons, finSum_scalePi]
  congr 2
  real_grind

/-- The dilated simplex point sums to the total. -/
private theorem finSum_scalePi_simplexPoint (dimension : Nat) (total : Carrier)
    (free : Fin dimension → Carrier) :
    additiveLaws.finSum (dimension + 1) (scalePi (dimension + 1) total (simplexPoint dimension free)) =
      total := by
  rw [finSum_scalePi, finSum_simplexPoint, mul_one]

/-- Normalizing the dilated simplex point recovers the simplex point. -/
private theorem normalize_scalePi_simplexPoint {dimension : Nat} {total : Carrier}
    (positive : lt zero total) (free : Fin dimension → Carrier) :
    normalize (dimension + 1) (scalePi (dimension + 1) total (simplexPoint dimension free)) =
      simplexPoint dimension free := by
  funext index
  show div (mul total (simplexPoint dimension free index)) _ = _
  have cancel := mul_inverse_cancel (nonzero_of_positive positive)
  rw [finSum_scalePi_simplexPoint, div_eq_mul_inverse]
  real_grind

/-- Integrating the line weights against volume, through the normalized point
and the total: the Gamma weight at the total shape in the total, times the
Dirichlet weight over the simplex's free coordinates. -/
public theorem lintegral_lineWeights (dimension : Nat) (shapes : Fin (dimension + 1) → Carrier)
    {integrand : (Fin (dimension + 1) → Carrier) × Carrier → ENNReal}
    (measurable : ENNRealMeasurable
      (Space.product (Space.pi (fun _ : Fin (dimension + 1) => borel)) borel) integrand) :
    lintegral (volumePi (dimension + 1)) (fun point =>
        ENNReal.mul (lineWeights (dimension + 1) shapes point)
          (integrand (normalize (dimension + 1) point, additiveLaws.finSum (dimension + 1) point))) =
      lintegral volume (fun total =>
        ENNReal.mul (Gamma.lineWeight (additiveLaws.finSum (dimension + 1) shapes) one total)
          (lintegral (volumePi dimension) (fun free =>
            ENNReal.mul (weight (dimension + 1) shapes (simplexPoint dimension free))
              (integrand (simplexPoint dimension free, total))))) := by
  classical
  have whole : ENNRealMeasurable (Space.pi (fun _ : Fin (dimension + 1) => borel)) (fun point =>
      ENNReal.mul (lineWeights (dimension + 1) shapes point)
        (integrand (normalize (dimension + 1) point, additiveLaws.finSum (dimension + 1) point))) :=
    (lineWeights_measurable (dimension + 1) shapes).mul
      (measurable.comp (Space.pair_measurable (normalize_measurable (dimension + 1))
        (finSum_measurable (dimension + 1))))
  rw [lintegral_volumePi_total dimension whole]
  apply lintegral_congr
  intro total
  by_cases positive : lt zero total
  · have shifted : ENNRealMeasurable (Space.pi (fun _ : Fin dimension => borel)) (fun rest =>
        ENNReal.mul (lineWeights (dimension + 1) shapes
            (finCons dimension (add (neg (additiveLaws.finSum dimension rest)) total, rest)))
          (integrand (normalize (dimension + 1)
              (finCons dimension (add (neg (additiveLaws.finSum dimension rest)) total, rest)),
            additiveLaws.finSum (dimension + 1)
              (finCons dimension (add (neg (additiveLaws.finSum dimension rest)) total, rest))))) :=
      whole.comp (MeasurableMap.comp (finCons_measurable dimension)
        (Space.pair_measurable
          (measurable_add (MeasurableMap.comp neg_measurable (finSum_measurable dimension))
            (MeasurableMap.constant _ borel total))
          (MeasurableMap.identity _)))
    have freeMeasurable : ENNRealMeasurable (Space.pi (fun _ : Fin dimension => borel))
        (fun free => ENNReal.mul (weight (dimension + 1) shapes (simplexPoint dimension free))
          (integrand (simplexPoint dimension free, total))) :=
      ((weight_measurable (dimension + 1) shapes).comp (simplexPoint_measurable dimension)).mul
        (measurable.comp (Space.pair_measurable (simplexPoint_measurable dimension)
          (MeasurableMap.constant _ borel total)))
    rw [lintegral_volumePi_scale dimension positive shifted,
      ← lintegral_smul _ _ (shifted.comp (scalePi_measurable dimension total)),
      ← lintegral_smul _ _ freeMeasurable]
    apply lintegral_congr
    intro free
    simp only [shifted_scalePi, finSum_scalePi_simplexPoint, normalize_scalePi_simplexPoint positive]
    rw [← ENNReal.mul_assoc, lineWeights_simplexPoint positive, ENNReal.mul_assoc]
  · have nonpositive := not_lt_iff_le.mp positive
    have outside : Gamma.lineWeight (additiveLaws.finSum (dimension + 1) shapes) one total =
        ENNReal.zero := by
      unfold Gamma.lineWeight
      rw [shapePower_of_nonpositive _ nonpositive, ENNReal.zero_mul]
    rw [outside, ENNReal.zero_mul]
    have vanishing : ∀ rest : Fin dimension → Carrier,
        lineWeights (dimension + 1) shapes
          (finCons dimension (add (neg (additiveLaws.finSum dimension rest)) total, rest)) =
          ENNReal.zero := by
      intro rest
      by_cases all : ∀ index, lt zero
          (finCons dimension (add (neg (additiveLaws.finSum dimension rest)) total, rest) index)
      · have sumPositive := finSum_positive dimension all
        rw [finSum_shifted] at sumPositive
        exact absurd sumPositive positive
      · rcases Classical.not_forall.mp all with ⟨index, notPositive⟩
        exact lineWeights_of_nonpositive (dimension + 1) shapes _ index
          (not_lt_iff_le.mp notPositive)
    rw [lintegral_congr _ (fun rest => by rw [vanishing rest, ENNReal.zero_mul]),
      lintegral_zero]

/-! ### The normalizers -/

/-- `∏ 1/Γ(αᵢ)` cancels `∏ Γ(αᵢ)` at positive shapes. -/
private theorem gammaScale_mul_finProduct : (count : Nat) → {shapes : Fin count → Carrier} →
    (∀ lane, lt zero (shapes lane)) →
    ENNReal.mul (gammaScale count shapes)
      (ENNReal.multiplicativeLaws.finProduct count fun lane => gammaIntegral (shapes lane)) =
      ENNReal.one
  | 0, _, _ => ENNReal.one_mul _
  | count + 1, shapes, positive => by
      have rest := gammaScale_mul_finProduct count (shapes := finTail count shapes)
        fun lane => positive lane.succ
      have head : ENNReal.mul (ENNReal.ofReal (inverse (gamma (shapes 0))))
          (gammaIntegral (shapes 0)) = ENNReal.one := by
        rw [← ofReal_gamma (positive 0), ENNReal.mul_comm]
        exact ofReal_mul_ofReal_inverse (gamma_positive (positive 0))
      show ENNReal.mul (ENNReal.mul _ (gammaScale count (finTail count shapes)))
        (ENNReal.mul (gammaIntegral (shapes 0)) (ENNReal.multiplicativeLaws.finProduct count
          fun lane => gammaIntegral (finTail count shapes lane))) = ENNReal.one
      calc
        _ = ENNReal.mul (ENNReal.mul (ENNReal.ofReal (inverse (gamma (shapes 0))))
              (gammaIntegral (shapes 0)))
            (ENNReal.mul (gammaScale count (finTail count shapes))
              (ENNReal.multiplicativeLaws.finProduct count
                fun lane => gammaIntegral (finTail count shapes lane))) := by ac_rfl
        _ = ENNReal.one := by rw [head, rest, ENNReal.one_mul]

/-- `∏ 1/Γ(αᵢ) = 1/Γ(Σα) · 1/B(α)` at positive concentrations. -/
public theorem gammaScale_eq {dimension : Nat} {shapes : Fin (dimension + 1) → Carrier}
    (positive : ∀ lane, lt zero (shapes lane)) :
    gammaScale (dimension + 1) shapes =
      ENNReal.mul (ENNReal.ofReal (inverse (gamma (additiveLaws.finSum (dimension + 1) shapes))))
        (ENNReal.ofReal (inverse (ENNReal.toReal (mass shapes)))) := by
  have totalPositive := finSum_positive dimension positive
  let product := ENNReal.multiplicativeLaws.finProduct (dimension + 1)
    fun lane => gammaIntegral (shapes lane)
  have left := gammaScale_mul_finProduct (dimension + 1) positive
  have right : ENNReal.mul (ENNReal.mul
      (ENNReal.ofReal (inverse (gamma (additiveLaws.finSum (dimension + 1) shapes))))
      (ENNReal.ofReal (inverse (ENNReal.toReal (mass shapes))))) product = ENNReal.one := by
    have total : ENNReal.mul
        (ENNReal.ofReal (inverse (gamma (additiveLaws.finSum (dimension + 1) shapes))))
        (gammaIntegral (additiveLaws.finSum (dimension + 1) shapes)) = ENNReal.one := by
      rw [← ofReal_gamma totalPositive, ENNReal.mul_comm]
      exact ofReal_mul_ofReal_inverse (gamma_positive totalPositive)
    have normalizer := mass_mul_inverse positive
    show ENNReal.mul _ (ENNReal.multiplicativeLaws.finProduct (dimension + 1)
      fun lane => gammaIntegral (shapes lane)) = _
    rw [← mass_mul_gammaIntegral]
    calc
      _ = ENNReal.mul (ENNReal.mul (mass shapes)
            (ENNReal.ofReal (inverse (ENNReal.toReal (mass shapes)))))
          (ENNReal.mul
            (ENNReal.ofReal (inverse (gamma (additiveLaws.finSum (dimension + 1) shapes))))
            (gammaIntegral (additiveLaws.finSum (dimension + 1) shapes))) := by ac_rfl
      _ = ENNReal.one := by rw [normalizer, total, ENNReal.one_mul]
  calc gammaScale (dimension + 1) shapes
      = ENNReal.mul (gammaScale (dimension + 1) shapes)
          (ENNReal.mul (ENNReal.mul
            (ENNReal.ofReal (inverse (gamma (additiveLaws.finSum (dimension + 1) shapes))))
            (ENNReal.ofReal (inverse (ENNReal.toReal (mass shapes))))) product) := by
        rw [right, ENNReal.mul_one]
    _ = ENNReal.mul (ENNReal.mul (gammaScale (dimension + 1) shapes) product)
          (ENNReal.mul
            (ENNReal.ofReal (inverse (gamma (additiveLaws.finSum (dimension + 1) shapes))))
            (ENNReal.ofReal (inverse (ENNReal.toReal (mass shapes))))) := by ac_rfl
    _ = _ := by rw [left, ENNReal.one_mul]

/-! ### The laws -/

/-- A probability measure is s-finite. -/
@[expose] public def probability_sFinite {α : Type} {space : Space α} {measure : Measure space}
    (probability : Measure.IsProbability measure) : Measure.SFinite measure :=
  Measure.SFinite.ofFinite ⟨by rw [probability.univ_eq_one]; exact True.intro⟩

/-- A measure of a measurable set is the integral of its indicator. -/
private theorem measure_eq_lintegral {α : Type} {space : Space α} (measure : Measure space)
    {set : Set α} (measurable : space.Measurable set) :
    measure set = lintegral measure (ennrealIndicator set (fun _ => ENNReal.one)) := by
  rw [lintegral_indicator _ _ measurable, lintegral_const, Measure.restrict_apply_univ,
    ENNReal.one_mul]

/-- Reading a point and its total. -/
public theorem normalizeTotal_measurable (count : Nat) :
    MeasurableMap (Space.pi (fun _ : Fin count => borel))
      (Space.product (Space.pi (fun _ : Fin count => borel)) borel)
      (fun point => (normalize count point, additiveLaws.finSum count point)) :=
  Space.pair_measurable (normalize_measurable count) (finSum_measurable count)

/-- Normalized independent Gammas and their total are independent, with laws
`Dirichlet.law α` and `Gamma(Σα, 1)`, at positive concentrations. -/
public theorem gammas_map_normalize_total {dimension : Nat}
    {shapes : Fin (dimension + 1) → Carrier} (positive : ∀ lane, lt zero (shapes lane)) :
    (gammas (dimension + 1) shapes).map
        (fun point => (normalize (dimension + 1) point, additiveLaws.finSum (dimension + 1) point))
        (normalizeTotal_measurable (dimension + 1)) =
      Measure.prod (law shapes) (Gamma.law (additiveLaws.finSum (dimension + 1) shapes) one)
        (probability_sFinite (Gamma.law_isProbability _ one)) := by
  classical
  have totalPositive := finSum_positive dimension positive
  apply Measure.ext
  intro set setMeasurable
  have indicator := ENNRealMeasurable.indicator setMeasurable
    (ENNRealMeasurable.constant _ ENNReal.one)
  have core := lintegral_lineWeights dimension shapes indicator
  have freeMeasurable : ENNRealMeasurable
      (Space.product borel (Space.pi (fun _ : Fin dimension => borel)))
      (fun pair => ENNReal.mul (weight (dimension + 1) shapes (simplexPoint dimension pair.2))
        (ennrealIndicator set (fun _ => ENNReal.one) (simplexPoint dimension pair.2, pair.1))) :=
    ((weight_measurable (dimension + 1) shapes).comp
        (MeasurableMap.comp (simplexPoint_measurable dimension) (Space.second_measurable _ _))).mul
      (indicator.comp (Space.pair_measurable
        (MeasurableMap.comp (simplexPoint_measurable dimension) (Space.second_measurable _ _))
        (Space.first_measurable _ _)))
  have inner : ENNRealMeasurable borel (fun total =>
      lintegral (volumePi dimension) (fun free =>
        ENNReal.mul (weight (dimension + 1) shapes (simplexPoint dimension free))
          (ennrealIndicator set (fun _ => ENNReal.one) (simplexPoint dimension free, total)))) :=
    Kernel.lintegral_measurable_joint (Kernel.const borel (volumePi dimension))
      (Kernel.IsSFinite.const borel (volumePiSFinite dimension)) freeMeasurable
  -- The left side: the change of variables.
  rw [Measure.map_apply _ _ _ setMeasurable,
    measure_eq_lintegral _ ((normalizeTotal_measurable (dimension + 1)) setMeasurable),
    gammas_eq_withDensity positive,
    lintegral_withDensity _ ((ENNRealMeasurable.constant _ _).mul
      (lineWeights_measurable (dimension + 1) shapes))
      (ENNRealMeasurable.indicator ((normalizeTotal_measurable (dimension + 1)) setMeasurable)
        (ENNRealMeasurable.constant _ ENNReal.one))]
  have pulled : ∀ point : Fin (dimension + 1) → Carrier,
      ENNReal.mul (ENNReal.mul (gammaScale (dimension + 1) shapes)
          (lineWeights (dimension + 1) shapes point))
        (ennrealIndicator (Set.preimage (fun point =>
            (normalize (dimension + 1) point, additiveLaws.finSum (dimension + 1) point)) set)
          (fun _ => ENNReal.one) point) =
      ENNReal.mul (gammaScale (dimension + 1) shapes)
        (ENNReal.mul (lineWeights (dimension + 1) shapes point)
          (ennrealIndicator set (fun _ => ENNReal.one)
            (normalize (dimension + 1) point, additiveLaws.finSum (dimension + 1) point))) := by
    intro point
    rw [ENNReal.mul_assoc]
    rfl
  rw [lintegral_congr _ pulled, lintegral_smul _ _ ((lineWeights_measurable (dimension + 1) shapes).mul
      (indicator.comp (normalizeTotal_measurable (dimension + 1)))), core]
  -- The right side: the product of the two laws, total outermost.
  have lawSide : ENNRealMeasurable borel (fun total =>
      lintegral (law shapes) (fun point => ennrealIndicator set (fun _ => ENNReal.one) (point, total))) :=
    Kernel.lintegral_measurable_joint (Kernel.const borel (law shapes))
      (Kernel.IsSFinite.const borel (probability_sFinite (law_isProbability shapes)))
      (indicator.comp (Space.swap_measurable _ _))
  rw [measure_eq_lintegral _ setMeasurable,
    lintegral_prod_symm _ _ (probability_sFinite (law_isProbability shapes))
      (probability_sFinite (Gamma.law_isProbability _ one)) indicator,
    law_one_eq_withDensity totalPositive,
    lintegral_withDensity _ ((ENNRealMeasurable.constant _ _).mul
      (lineWeight_one_measurable _)) lawSide]
  have simplexSide : ∀ total : Carrier,
      lintegral (law shapes) (fun point => ennrealIndicator set (fun _ => ENNReal.one) (point, total)) =
        ENNReal.mul (ENNReal.ofReal (inverse (ENNReal.toReal (mass shapes))))
          (lintegral (volumePi dimension) (fun free =>
            ENNReal.mul (weight (dimension + 1) shapes (simplexPoint dimension free))
              (ennrealIndicator set (fun _ => ENNReal.one) (simplexPoint dimension free, total)))) := by
    intro total
    have slice : ENNRealMeasurable (Space.pi (fun _ : Fin (dimension + 1) => borel))
        (fun point => ennrealIndicator set (fun _ => ENNReal.one) (point, total)) :=
      indicator.comp (Space.pair_measurable (MeasurableMap.identity _)
        (MeasurableMap.constant _ borel total))
    rw [law_eq_withDensity positive, lintegral_withDensity _ (density_measurable shapes) slice,
      lintegral_simplex dimension ((density_measurable shapes).mul slice),
      ← lintegral_smul _ _ (((weight_measurable (dimension + 1) shapes).comp
        (simplexPoint_measurable dimension)).mul
        (slice.comp (simplexPoint_measurable dimension)))]
    apply lintegral_congr
    intro free
    by_cases member : simplexRegion dimension free
    · rw [ennrealIndicator_of_mem member]
      unfold density
      exact ENNReal.mul_assoc _ _ _
    · rw [ennrealIndicator_of_not_mem member]
      have vanishing : weight (dimension + 1) shapes (simplexPoint dimension free) = ENNReal.zero :=
        simplexWeight_of_not_mem member (shapes 0) (finTail dimension shapes)
      rw [vanishing, ENNReal.zero_mul, ENNReal.mul_zero]
  rw [gammaScale_eq positive, ← lintegral_smul _ _ ((lineWeight_one_measurable _).mul inner)]
  apply lintegral_congr
  intro total
  rw [simplexSide total]
  ac_rfl

/-- Normalized independent Gammas have law `Dirichlet.law α` at positive
concentrations. -/
public theorem gammas_map_normalize {dimension : Nat}
    {shapes : Fin (dimension + 1) → Carrier} (positive : ∀ lane, lt zero (shapes lane)) :
    (gammas (dimension + 1) shapes).map (normalize (dimension + 1))
        (normalize_measurable (dimension + 1)) = law shapes := by
  have joint := congrArg (fun measure => measure.map (fun pair => pair.1)
    (Space.first_measurable _ _)) (gammas_map_normalize_total positive)
  rw [Measure.map_comp, Measure.prod_map_first,
    (Gamma.law_isProbability _ one).univ_eq_one, Measure.one_smul] at joint
  exact joint

/-! ### Support and coordinatewise maps -/

/-- The points with every coordinate positive. -/
@[expose] public def positiveOrthant (count : Nat) : Set (Fin count → Carrier) :=
  fun point => ∀ index, lt zero (point index)

public theorem positiveOrthant_measurable : (count : Nat) →
    (Space.pi (fun _ : Fin count => borel)).Measurable (positiveOrthant count)
  | 0 => by
      have all : positiveOrthant 0 = Set.univ :=
        Set.ext (fun _ => ⟨fun _ => True.intro, fun _ index => Fin.elim0 index⟩)
      rw [all]
      exact Space.univ _
  | count + 1 => by
      have split : positiveOrthant (count + 1) =
          Set.inter (fun point => lt zero (point 0))
            (Set.preimage (finTail count) (positiveOrthant count)) :=
        Set.ext (fun point => ⟨fun all => ⟨all 0, fun index => all index.succ⟩,
          fun both index => Fin.cases both.1 both.2 index⟩)
      rw [split]
      exact Space.inter _
        (measurable_lt (MeasurableMap.constant _ borel zero)
          (Space.coordinate_measurable (fun _ : Fin (count + 1) => borel) 0))
        (finTail_measurable count (positiveOrthant_measurable count))

/-- Independent draws at positive shapes put no mass off the positive orthant. -/
public theorem gammas_positiveOrthant {count : Nat} {shapes : Fin count → Carrier}
    (positive : ∀ lane, lt zero (shapes lane)) :
    gammas count shapes (Set.complement (positiveOrthant count)) = ENNReal.zero := by
  classical
  have outsideMeasurable := Space.complement _ (positiveOrthant_measurable count)
  rw [gammas_eq_withDensity positive, Measure.withDensity_apply _ _ outsideMeasurable,
    ← lintegral_indicator _ _ outsideMeasurable]
  have vanishing : ∀ point : Fin count → Carrier,
      ennrealIndicator (Set.complement (positiveOrthant count)) (fun point =>
        ENNReal.mul (gammaScale count shapes) (lineWeights count shapes point)) point =
        ENNReal.zero := by
    intro point
    by_cases outside : Set.complement (positiveOrthant count) point
    · rw [ennrealIndicator_of_mem outside]
      rcases Classical.not_forall.mp outside with ⟨index, notPositive⟩
      rw [lineWeights_of_nonpositive count shapes point index (not_lt_iff_le.mp notPositive),
        ENNReal.mul_zero]
    · rw [ennrealIndicator_of_not_mem outside]
  rw [lintegral_congr _ vanishing, lintegral_zero]

end

end Problib.Analysis.Dirichlet
