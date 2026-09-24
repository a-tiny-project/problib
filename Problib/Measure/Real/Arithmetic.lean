module

public import Problib.Measure.Real.Affine
public import Problib.Measure.Real.Order
public import Problib.Measure.Extended.Conversion
public import Problib.Measure.Extended.Algebra.Binary
public import Problib.Measure.Product

set_option autoImplicit false

namespace Problib.Measure.Real

open Problib.Real
open Problib.Real.Construction.Dedekind

universe u
variable {α : Type u} {source : Space α} {left right : α → Carrier}

/-- A measurable choice between two real-valued maps. -/
public theorem measurable_piecewise {region : Set α}
    (regionMeasurable : source.Measurable region)
    (leftMeasurable : MeasurableMap source borel left)
    (rightMeasurable : MeasurableMap source borel right) :
    MeasurableMap source borel
      (fun x => @ite Carrier (region x) (Classical.propDecidable _) (left x) (right x)) := by
  classical
  intro set measurable
  have same : Set.preimage (fun x => if region x then left x else right x) set =
      Set.union (Set.inter region (Set.preimage left set))
        (Set.inter (Set.complement region) (Set.preimage right set)) := by
    apply Set.ext
    intro x
    by_cases member : region x <;> simp [Set.preimage, Set.union, Set.inter,
      Set.complement, member]
  rw [same]
  exact source.union (source.inter regionMeasurable (leftMeasurable measurable))
    (source.inter (source.complement regionMeasurable) (rightMeasurable measurable))

/-- Addition is measurable in both varying operands. -/
public theorem measurable_add (hl : MeasurableMap source borel left)
    (hr : MeasurableMap source borel right) :
    MeasurableMap source borel (fun x => add (left x) (right x)) := by
  apply measurableMap_borel_iff_iio.mpr
  intro upper
  have same : Set.preimage (fun x => add (left x) (right x)) (Iio upper) =
      Set.iUnion (fun n => Set.inter
        (fun x => lt (left x) (rationalBasis n))
        (fun x => lt (add (rationalBasis n) (right x)) upper)) := by
    apply Set.ext
    intro x
    constructor
    · intro below
      have gap : lt (left x) (sub upper (right x)) :=
        lt_sub_iff_add_lt.mpr (by rw [add_comm]; exact below)
      rcases exists_rationalBasis_between gap with ⟨n, low, high⟩
      exact ⟨n, low, by
        change lt (add (rationalBasis n) (right x)) upper
        rw [add_comm]
        exact lt_sub_iff_add_lt.mp high⟩
    · rintro ⟨n, low, high⟩
      exact lt_trans (add_lt_add_right_iff.mpr low) high
  rw [same]
  exact source.iUnion fun n => source.inter (hl (measurable_iio _))
    ((MeasurableMap.comp (translate_measurable (rationalBasis n)) hr) (measurable_iio upper))

public theorem add_measurable : MeasurableMap (Space.product borel borel) borel
    (fun p => add p.1 p.2) :=
  measurable_add (Space.first_measurable _ _) (Space.second_measurable _ _)

public theorem measurable_sub (hl : MeasurableMap source borel left)
    (hr : MeasurableMap source borel right) :
    MeasurableMap source borel (fun x => sub (left x) (right x)) := by
  change MeasurableMap source borel (fun x => add (left x) (neg (right x)))
  exact measurable_add hl (MeasurableMap.comp neg_measurable hr)

public theorem sub_measurable : MeasurableMap (Space.product borel borel) borel
    (fun p => sub p.1 p.2) :=
  measurable_sub (Space.first_measurable _ _) (Space.second_measurable _ _)

/-- Nonnegative multiplication commutes with the embedding into extended reals. -/
public theorem ofReal_mul {x y : Carrier} (hx : le zero x) (hy : le zero y) :
    ENNReal.ofReal (mul x y) = ENNReal.mul (ENNReal.ofReal x) (ENNReal.ofReal y) := by
  rw [ENNReal.ofReal_of_nonnegative (mul_nonnegative hx hy),
    ENNReal.ofReal_of_nonnegative hx, ENNReal.ofReal_of_nonnegative hy]
  rfl

/-- A positive value's embedding times its reciprocal's embedding is one. -/
public theorem ofReal_mul_ofReal_inverse {value : Carrier} (positive : lt zero value) :
    ENNReal.mul (ENNReal.ofReal value) (ENNReal.ofReal (inverse value)) = ENNReal.one := by
  rw [← ofReal_mul positive.1 (inverse_of_positive_positive positive).1,
    mul_inverse_cancel (positive_iff_nonnegative_and_nonzero.mp positive).2]
  exact ENNReal.ofReal_one

private noncomputable def positiveProduct (x y : Carrier) : Carrier :=
  ENNReal.toReal (ENNReal.mul (ENNReal.ofReal x) (ENNReal.ofReal y))

private theorem positiveProduct_eq {x y : Carrier} (hx : le zero x) (hy : le zero y) :
    positiveProduct x y = mul x y := by
  unfold positiveProduct
  rw [← ofReal_mul hx hy, ENNReal.toReal_ofReal (mul_nonnegative hx hy)]

private theorem positiveProduct_measurable (hl : MeasurableMap source borel left)
    (hr : MeasurableMap source borel right) :
    MeasurableMap source borel (fun x => positiveProduct (left x) (right x)) :=
  MeasurableMap.comp toReal_measurable
    ((ofReal_measurable.comp hl).mul (ofReal_measurable.comp hr)).measurableMap

private theorem neg_nonnegative {x : Carrier} (hx : ¬le zero x) : le zero (neg x) := by
  have result := neg_le_neg_iff.mpr (not_le_iff_lt.mp hx).1
  simpa only [neg_zero] using result

/-- Signed multiplication is a measurable choice among four nonnegative products. -/
public theorem measurable_mul (hl : MeasurableMap source borel left)
    (hr : MeasurableMap source borel right) :
    MeasurableMap source borel (fun x => mul (left x) (right x)) := by
  classical
  have nl : MeasurableMap source borel (fun x => neg (left x)) := MeasurableMap.comp neg_measurable hl
  have nr : MeasurableMap source borel (fun x => neg (right x)) := MeasurableMap.comp neg_measurable hr
  have lm := measurable_le (MeasurableMap.constant source borel zero) hl
  have rm := measurable_le (MeasurableMap.constant source borel zero) hr
  have branches : MeasurableMap source borel _ := measurable_piecewise lm
    (measurable_piecewise rm (positiveProduct_measurable hl hr)
      (MeasurableMap.comp neg_measurable (positiveProduct_measurable hl nr)))
    (measurable_piecewise rm
      (MeasurableMap.comp neg_measurable (positiveProduct_measurable nl hr))
      (positiveProduct_measurable nl nr))
  have same : (fun x => mul (left x) (right x)) = (fun x =>
      if le zero (left x) then
        if le zero (right x) then positiveProduct (left x) (right x)
        else neg (positiveProduct (left x) (neg (right x)))
      else if le zero (right x) then neg (positiveProduct (neg (left x)) (right x))
        else positiveProduct (neg (left x)) (neg (right x))) := by
    funext x
    by_cases lp : le zero (left x) <;> by_cases rp : le zero (right x)
    · simp only [lp, rp, if_true, positiveProduct_eq lp rp]
    · simp only [lp, rp, if_true, if_false,
        positiveProduct_eq lp (neg_nonnegative rp), mul_neg, neg_neg]
    · simp only [lp, rp, if_true, if_false,
        positiveProduct_eq (neg_nonnegative lp) rp, neg_mul, neg_neg]
    · simp only [lp, rp, if_false, positiveProduct_eq (neg_nonnegative lp) (neg_nonnegative rp),
        neg_mul_neg]
  rw [same]
  exact @branches

public theorem mul_measurable : MeasurableMap (Space.product borel borel) borel
    (fun p => mul p.1 p.2) :=
  measurable_mul (Space.first_measurable _ _) (Space.second_measurable _ _)


private noncomputable def positiveInversePart (x : Carrier) : Carrier := by
  classical
  exact if lt zero x then inverse x else zero

private theorem positiveInversePart_nonnegative (x : Carrier) :
    le zero (positiveInversePart x) := by
  classical
  unfold positiveInversePart
  split
  · exact (inverse_of_positive_positive ‹lt zero x›).1
  · exact le_refl _

private theorem positiveInversePart_measurable :
    MeasurableMap borel borel positiveInversePart := by
  classical
  apply measurableMap_borel_iff_iio.mpr
  intro upper
  by_cases positive : lt zero upper
  · have same : Set.preimage positiveInversePart (Iio upper) =
        Set.union (Iic zero) (Ioi (inverse upper)) := by
      apply Set.ext
      intro x
      change lt (positiveInversePart x) upper ↔ le x zero ∨ lt (inverse upper) x
      by_cases xp : lt zero x
      · have value : positiveInversePart x = inverse x := by
          unfold positiveInversePart
          rw [if_pos xp]
        rw [value]
        constructor
        · intro below
          have reversed := inverse_lt_inverse_of_positive (inverse_of_positive_positive xp)
            positive below
          exact Or.inr (by simpa only [inverse_inverse] using reversed)
        · intro member
          rcases member with nonpositive | above
          · exact False.elim (xp.2 nonpositive)
          · have reversed := inverse_lt_inverse_of_positive (inverse_of_positive_positive positive) xp above
            simpa only [inverse_inverse] using reversed
      · have value : positiveInversePart x = zero := by
          unfold positiveInversePart
          rw [if_neg xp]
        rw [value]
        exact ⟨fun _ => Or.inl (not_lt_iff_le.mp xp), fun _ => positive⟩
    rw [same]
    exact borel.union (measurable_iic zero) (measurable_ioi _)
  · have same : Set.preimage positiveInversePart (Iio upper) = Set.empty := by
      apply Set.ext
      intro x
      exact ⟨fun below => positive (lt_of_le_of_lt (positiveInversePart_nonnegative x) below),
        False.elim⟩
    rw [same]
    exact borel.empty

/-- The totalized reciprocal is measurable, including its value zero at zero. -/
public theorem inverse_measurable : MeasurableMap borel borel inverse := by
  classical
  have same : inverse = (fun x => sub (positiveInversePart x)
      (positiveInversePart (neg x))) := by
    funext x
    by_cases xp : lt zero x
    · have nx : ¬lt zero (neg x) := by
        intro h
        have bad := neg_le_neg_iff.mpr h.1
        exact xp.2 (by simpa only [neg_zero, neg_neg] using bad)
      simp only [positiveInversePart, if_pos xp, if_neg nx, sub_eq_add_neg, neg_zero, add_zero]
    · by_cases xn : lt x zero
      · have nx := neg_positive_of_negative xn
        rw [positiveInversePart, if_neg xp, positiveInversePart, if_pos nx,
          inverse_of_negative xn, inverse_of_positive nx, sub_eq_add_neg]
        exact (additive.group.zero_add _).symm
      · have xz : x = zero := le_antisymm (not_lt_iff_le.mp xp) (not_lt_iff_le.mp xn)
        subst x
        simp only [inverse_zero, positiveInversePart, lt_irrefl, if_false, neg_zero,
          sub_eq_add_neg, add_zero]
  rw [same]
  apply measurable_sub
  · exact positiveInversePart_measurable
  · exact MeasurableMap.comp positiveInversePart_measurable neg_measurable

public theorem measurable_div (hl : MeasurableMap source borel left)
    (hr : MeasurableMap source borel right) :
    MeasurableMap source borel (fun x => div (left x) (right x)) :=
  measurable_mul hl (MeasurableMap.comp inverse_measurable hr)

public theorem div_measurable : MeasurableMap (Space.product borel borel) borel
    (fun p => div p.1 p.2) :=
  measurable_div (Space.first_measurable _ _) (Space.second_measurable _ _)

/-- Two negative inputs refute unrestricted multiplicativity of `ofReal`. -/
public theorem signed_ofReal_mul_fails :
    ENNReal.ofReal (mul (neg one) (neg one)) ≠
      ENNReal.mul (ENNReal.ofReal (neg one)) (ENNReal.ofReal (neg one)) := by
  have nonpositive : le (neg one) zero := by
    simpa only [neg_zero] using neg_le_neg_iff.mpr one_nonnegative
  rw [neg_mul_neg, mul_one,
    ENNReal.ofReal_eq_zero_iff.mpr nonpositive, ENNReal.zero_mul]
  intro equal
  have zeroOne : one = zero := by
    have h := congrArg ENNReal.toReal equal
    simpa only [ENNReal.toReal_ofReal one_nonnegative, ENNReal.toReal_zero] using h
  exact one_ne_zero zeroOne

/-- Joint measurability of the Gaussian exponent in mean, variance, and value.
The formula is totalized for all variances, including zero. -/
public theorem gaussian_exponent_measurable :
    MeasurableMap (Space.product (Space.product borel borel) borel) borel
      (fun p => neg (div (mul (sub p.2 p.1.1) (sub p.2 p.1.1))
        (mul (selection.ofRat 2) p.1.2))) := by
  have parameters : MeasurableMap _ _ _ := Space.first_measurable (Space.product borel borel) borel
  have value : MeasurableMap _ _ _ := Space.second_measurable (Space.product borel borel) borel
  have mean : MeasurableMap _ _ _ := MeasurableMap.comp (Space.first_measurable borel borel) parameters
  have variance : MeasurableMap _ _ _ := MeasurableMap.comp (Space.second_measurable borel borel) parameters
  have centered : MeasurableMap _ _ _ := measurable_sub value mean
  apply MeasurableMap.comp neg_measurable
  exact measurable_div (measurable_mul centered centered)
    (measurable_mul (MeasurableMap.constant _ borel (selection.ofRat 2)) variance)

end Problib.Measure.Real
