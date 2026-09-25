module

public import Problib.Analysis.Real.PowerSeries.Continuity

/-! Small-radius coefficientwise majorants for analytic substitution. -/

set_option autoImplicit false

namespace Problib.Analysis.Real.PowerSeries

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real.SignedSeries

noncomputable section

private instance : Std.Associative (α := selection.Carrier) mul :=
  ⟨fun left middle right => mul_assoc left middle right⟩

private instance : Std.Commutative (α := selection.Carrier) mul :=
  ⟨mul_comm⟩

private theorem limit_le_of_eventually_le
    {values : Nat → selection.Carrier}
    {limit upper : selection.Carrier}
    (converges : Problib.Analysis.Real.ConvergesTo values limit)
    (stage : Nat)
    (bounded : ∀ index, stage ≤ index → le (values index) upper) :
    le limit upper := by
  apply Problib.Analysis.Real.le_of_forall_lt_add
  intro tolerance positive
  rcases converges tolerance positive with ⟨convergesStage, close⟩
  let index := max stage convergesStage
  have near := close index (Nat.le_max_right _ _)
  rw [abs_sub_comm] at near
  have upperNear := (abs_lt.mp near).right
  have summed := add_lt_add_le upperNear
    (bounded index (Nat.le_max_left _ _))
  rw [sub_add_cancel, add_comm tolerance upper] at summed
  exact summed

public theorem summable_sum_le {first second : Nat → selection.Carrier}
    (firstSummable : Summable first)
    (secondSummable : Summable second)
    (pointwise : ∀ index, le (first index) (second index)) :
    le (sum first firstSummable) (sum second secondSummable) := by
  have differenceConverges := converges_to_sub
    (partial_sum_converges first firstSummable)
    (partial_sum_converges second secondSummable)
  have finiteBound : ∀ count,
      le (sub (partialSum first count) (partialSum second count))
        zero := by
    intro count
    have included := partial_sum_le pointwise count
    have shifted := (add_le_add_right_iff
      (shift := neg (partialSum second count))).mpr included
    simpa only [sub_eq_add_neg, add_neg] using shifted
  have limitBound := limit_le_of_eventually_le differenceConverges
    0 (fun count _ => finiteBound count)
  have shifted := (add_le_add_right_iff
    (shift := sum second secondSummable)).mpr limitBound
  simpa only [sub_add_cancel, zero_add] using shifted

public theorem tail_majorant_sum_mono_radius {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    {small large : selection.Carrier}
    (smallPositive : lt zero small) (largePositive : lt zero large)
    (included : le small large)
    (smallSummable : Summable
      (tailMagnitudes coefficients (fun _ => small)))
    (largeSummable : Summable
      (tailMagnitudes coefficients (fun _ => large))) :
    le (sum (tailMagnitudes coefficients (fun _ => small))
      smallSummable)
      (sum (tailMagnitudes coefficients (fun _ => large))
        largeSummable) := by
  apply summable_sum_le smallSummable largeSummable
  intro degreeValue
  exact tailMagnitudes_le_constant coefficients (fun _ => small)
    (radius := large) largePositive.left
    (fun _ => by
      rw [abs_of_nonnegative smallPositive.left]
      exact included)
    degreeValue

public theorem tail_magnitude_scale_radius {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (ratio radius : selection.Carrier)
    (ratioNonnegative : le zero ratio)
    (radiusNonnegative : le zero radius)
    (degreeValue : Nat) :
    tailMagnitudes coefficients (fun _ => mul ratio radius)
      degreeValue =
    mul (power ratio (degreeValue + 1))
      (tailMagnitudes coefficients (fun _ => radius) degreeValue) := by
  unfold tailMagnitudes
  rw [shellMagnitude_constant_eq coefficients
      (mul_nonnegative ratioNonnegative radiusNonnegative),
    shellMagnitude_constant_eq coefficients radiusNonnegative,
    power_mul]
  ac_rfl

public theorem positive_power_le_ratio
    {ratio : selection.Carrier}
    (ratioNonnegative : le zero ratio)
    (ratioAtMostOne : le ratio one)
    (degreeValue : Nat) :
    le (power ratio (degreeValue + 1)) ratio := by
  rw [power_succ]
  have bounded := power_le_one ratioNonnegative ratioAtMostOne degreeValue
  have scaled := mul_le_mul_nonnegative_left bounded ratioNonnegative
  rwa [mul_one] at scaled

public theorem tailMagnitudes_small_radius {dimension : Nat}
    (series : Convergent dimension)
    {tolerance : selection.Carrier}
    (tolerancePositive : lt zero tolerance) :
    ∃ radius : selection.Carrier,
      lt zero radius ∧ lt radius series.radius ∧
      ∀ count,
        lt (partialSum
          (tailMagnitudes series.coefficients (fun _ => radius)) count)
          tolerance := by
  let outer := Problib.Analysis.Real.half series.radius
  have outerPositive := Problib.Analysis.Real.half_positive
    series.radiusPositive
  have outerBelow : lt outer series.radius := by
    have raised := add_lt_add_left outer outerPositive
    rwa [add_zero, Problib.Analysis.Real.add_half] at raised
  have outerInside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius
      (fun _ => outer) := by
    intro coordinate
    change lt (abs (sub outer zero)) series.radius
    rw [sub_zero, abs_of_nonnegative outerPositive.left]
    exact outerBelow
  rcases series.normalOn (fun _ => outer) outerInside with
    ⟨upper, upperBound⟩
  have upperNonnegative : le zero upper := by
    have atZero := upperBound 0
    rwa [partial_sum_zero] at atZero
  let margin := add upper one
  have marginPositive : lt zero margin := by
    have raised := add_lt_add_left upper one_positive
    rw [add_zero] at raised
    exact lt_of_le_of_lt upperNonnegative raised
  have upperLeMargin : le upper margin := by
    have raised := (add_le_add_right_iff (shift := upper)).mpr
      one_nonnegative
    simpa only [margin, zero_add, add_comm one upper] using raised
  have halfPositive := Problib.Analysis.Real.half_positive
    tolerancePositive
  have quotientPositive : lt zero
      (div (Problib.Analysis.Real.half tolerance) margin) :=
    div_positive halfPositive marginPositive
  rcases small_positive one_positive quotientPositive with
    ⟨ratio, ratioPositive, ratioAtMostOne, ratioAtMostQuotient⟩
  let radius := mul ratio outer
  have radiusPositive : lt zero radius :=
    mul_positive ratioPositive outerPositive
  have radiusBelow : lt radius series.radius := by
    have scaled := mul_le_mul_nonnegative_right ratioAtMostOne
      outerPositive.left
    rw [one_mul] at scaled
    exact lt_of_le_of_lt scaled outerBelow
  refine ⟨radius, radiusPositive, radiusBelow, fun count => ?_⟩
  have pointwise : ∀ degreeValue,
      le (tailMagnitudes series.coefficients (fun _ => radius)
        degreeValue)
        (mul ratio (tailMagnitudes series.coefficients
          (fun _ => outer) degreeValue)) := by
    intro degreeValue
    rw [tail_magnitude_scale_radius series.coefficients ratio outer
      ratioPositive.left outerPositive.left]
    exact mul_le_mul_nonnegative_right
      (positive_power_le_ratio ratioPositive.left ratioAtMostOne
        degreeValue)
      (shellMagnitude_nonnegative series.coefficients
        (fun _ => outer) (degreeValue + 1))
  have finiteBound := partial_sum_le pointwise count
  rw [partial_sum_scale] at finiteBound
  have originalBound := upperBound count
  have scaledUpper := mul_le_mul_nonnegative_left originalBound
    ratioPositive.left
  have upperMargin := mul_le_mul_nonnegative_left upperLeMargin
    ratioPositive.left
  have quotientBound := mul_le_mul_nonnegative_right
    ratioAtMostQuotient marginPositive.left
  have cancel : mul
      (div (Problib.Analysis.Real.half tolerance) margin)
      margin = Problib.Analysis.Real.half tolerance :=
    div_mul_cancel _ (nonzero_of_positive marginPositive)
  rw [cancel] at quotientBound
  have halfBelow : lt
      (Problib.Analysis.Real.half tolerance) tolerance := by
    have raised := add_lt_add_left
      (Problib.Analysis.Real.half tolerance) halfPositive
    rwa [add_zero, Problib.Analysis.Real.add_half] at raised
  exact lt_of_le_of_lt
    (le_trans finiteBound
      (le_trans scaledUpper (le_trans upperMargin quotientBound)))
    halfBelow

public theorem tail_majorant_sum_small_radius {dimension : Nat}
    (series : Convergent dimension)
    {tolerance : selection.Carrier}
    (tolerancePositive : lt zero tolerance) :
    ∃ radius : selection.Carrier,
      lt zero radius ∧ lt radius series.radius ∧
      ∃ certificate : Summable
        (tailMagnitudes series.coefficients (fun _ => radius)),
        lt (sum
          (tailMagnitudes series.coefficients (fun _ => radius))
          certificate) tolerance := by
  have halfPositive := Problib.Analysis.Real.half_positive
    tolerancePositive
  rcases tailMagnitudes_small_radius series halfPositive with
    ⟨radius, radiusPositive, radiusBelow, finiteBound⟩
  have inside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius
      (fun _ => radius) := by
    intro coordinate
    change lt (abs (sub radius zero)) series.radius
    rw [sub_zero, abs_of_nonnegative radiusPositive.left]
    exact radiusBelow
  let values := tailMagnitudes series.coefficients (fun _ => radius)
  have nonnegative : ∀ degreeValue, le zero (values degreeValue) :=
    fun degreeValue => shellMagnitude_nonnegative
      series.coefficients (fun _ => radius) (degreeValue + 1)
  have certificate : Summable values :=
    summable_of_nonnegative_bounded nonnegative
      (series.normalOn (fun _ => radius) inside)
  refine ⟨radius, radiusPositive, radiusBelow, certificate, ?_⟩
  have partialBound : ∀ count,
      le (abs (partialSum values count))
        (Problib.Analysis.Real.half tolerance) := by
    intro count
    rw [abs_of_nonnegative
      (partial_sum_nonnegative nonnegative count)]
    exact (finiteBound count).left
  have limitBound := abs_le_of_convergesTo
    (partial_sum_converges values certificate) partialBound
  have halfBelow : lt
      (Problib.Analysis.Real.half tolerance) tolerance := by
    have raised := add_lt_add_left
      (Problib.Analysis.Real.half tolerance) halfPositive
    rwa [add_zero, Problib.Analysis.Real.add_half] at raised
  exact lt_of_le_of_lt (le_trans (le_abs _) limitBound) halfBelow

/-- All components of a finite analytic map admit one source box on which
their positive-degree coefficient majorants lie below a prescribed bound. -/
public theorem component_tail_majorants_small_radius
    {source target : Nat} (series : Fin target → Convergent source)
    {bound : selection.Carrier} (boundPositive : lt zero bound) :
    ∃ radius : selection.Carrier,
      lt zero radius ∧
      ∀ coordinate : Fin target,
        lt radius (series coordinate).radius ∧
        ∃ _inside : FiniteVector.ball
            (FiniteVector.zeroVector source)
            (series coordinate).radius (fun _ => radius),
          ∃ certificate : Summable
              (tailMagnitudes (series coordinate).coefficients
                (fun _ => radius)),
            lt (sum
              (tailMagnitudes (series coordinate).coefficients
                (fun _ => radius)) certificate) bound := by
  let witness := fun coordinate : Fin target =>
    tail_majorant_sum_small_radius (series coordinate) boundPositive
  let selectedRadius := fun coordinate : Fin target =>
    Classical.choose (witness coordinate)
  have selectedPositive : ∀ coordinate,
      lt zero (selectedRadius coordinate) := fun coordinate =>
    (Classical.choose_spec (witness coordinate)).1
  rcases finite_small_radius selectedRadius selectedPositive
    (List.finRange target) with ⟨radius, radiusPositive, radiusBelow⟩
  refine ⟨radius, radiusPositive, fun coordinate => ?_⟩
  have chosen := Classical.choose_spec (witness coordinate)
  have belowSelected := radiusBelow coordinate
    (List.mem_finRange coordinate)
  have belowSeries : lt radius (series coordinate).radius :=
    lt_of_le_of_lt belowSelected chosen.2.1
  have inside : FiniteVector.ball
      (FiniteVector.zeroVector source)
      (series coordinate).radius (fun _ => radius) := by
    intro input
    change lt (abs (sub radius zero)) (series coordinate).radius
    rw [sub_zero, abs_of_nonnegative radiusPositive.left]
    exact belowSeries
  have selectedInside : FiniteVector.ball
      (FiniteVector.zeroVector source)
      (series coordinate).radius
      (fun _ => selectedRadius coordinate) := by
    intro input
    change lt (abs (sub (selectedRadius coordinate) zero))
      (series coordinate).radius
    rw [sub_zero, abs_of_nonnegative chosen.1.left]
    exact chosen.2.1
  let smallValues := tailMagnitudes (series coordinate).coefficients
    (fun _ => radius)
  let largeValues := tailMagnitudes (series coordinate).coefficients
    (fun _ => selectedRadius coordinate)
  have smallCertificate : Summable smallValues :=
    summable_of_nonnegative_bounded
      (fun degreeValue => shellMagnitude_nonnegative
        (series coordinate).coefficients (fun _ => radius)
        (degreeValue + 1))
      ((series coordinate).normalOn (fun _ => radius) inside)
  rcases chosen.2.2 with ⟨largeCertificate, largeBelow⟩
  refine ⟨belowSeries, inside, smallCertificate, ?_⟩
  exact lt_of_le_of_lt
    (tail_majorant_sum_mono_radius (series coordinate).coefficients
      radiusPositive chosen.1 belowSelected
      smallCertificate largeCertificate)
    largeBelow

public theorem abs_partial_sum_le_magnitudes
    {dimension : Nat}
    (coefficients : MultiIndex.carrier dimension → selection.Carrier)
    (displacement : FiniteVector.carrier dimension)
    (count : Nat) :
    le (abs (partialSum (tailTerms coefficients displacement) count))
      (partialSum (tailMagnitudes coefficients displacement) count) := by
  induction count with
  | zero =>
      rw [partial_sum_zero, partial_sum_zero, abs_zero]
      exact le_refl zero
  | succ count induction =>
      rw [partial_sum_succ, partial_sum_succ]
      exact le_trans (abs_add_le _ _)
        (add_le_add induction
          (abs_shellTerm_le_magnitude coefficients displacement
            (count + 1)))

/-- The nonconstant value is bounded by its normal coefficient sum on a
smaller constant-radius box. -/
public theorem value_tail_abs_le_constant_majorant {dimension : Nat}
    (series : Convergent dimension)
    (displacement : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius displacement)
    {radius : selection.Carrier}
    (radiusPositive : lt zero radius)
    (coordinates : ∀ coordinate,
      le (abs (displacement coordinate)) radius)
    (majorantSummable : Summable
      (tailMagnitudes series.coefficients (fun _ => radius))) :
    le (abs (sub (value series displacement inside)
        (series.coefficients (MultiIndex.zeroIndex dimension))))
      (sum (tailMagnitudes series.coefficients (fun _ => radius))
        majorantSummable) := by
  let terms := tailTerms series.coefficients displacement
  let magnitudes := tailMagnitudes series.coefficients (fun _ => radius)
  have finiteBound : ∀ count,
      le (abs (partialSum terms count)) (sum magnitudes majorantSummable) := by
    intro count
    exact le_trans
      (abs_partial_sum_le_magnitudes series.coefficients displacement count)
      (le_trans
        (partial_sum_le
          (fun degreeValue => tailMagnitudes_le_constant
            series.coefficients displacement radiusPositive.left
            coordinates degreeValue) count)
        (partial_sum_le_sum_nonnegative
          (fun degreeValue => shellMagnitude_nonnegative
            series.coefficients (fun _ => radius) (degreeValue + 1))
          majorantSummable count))
  have bounded := abs_le_of_convergesTo
    (partial_sum_converges terms
      (summable_of_absolute_bound (series.absoluteOn _ inside)))
    finiteBound
  simpa only [value, add_sub_self] using bounded

end

end Problib.Analysis.Real.PowerSeries
