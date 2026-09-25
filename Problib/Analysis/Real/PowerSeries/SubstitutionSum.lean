module

public import Problib.Analysis.Real.PowerSeries.SubstitutionNorm

/-! Fixed-radius sums for finite outer Taylor polynomials. -/

set_option autoImplicit false

namespace Problib.Analysis.Real.PowerSeries

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real.SignedSeries

noncomputable section

private instance : Std.Associative (α := selection.Carrier) add :=
  ⟨fun left middle right => add_assoc left middle right⟩

private instance : Std.Commutative (α := selection.Carrier) add :=
  ⟨add_comm⟩

@[expose] public noncomputable def addSeriesWithin {dimension : Nat}
    (first second : Convergent dimension)
    (radius : selection.Carrier) (positive : lt zero radius)
    (belowFirst : le radius first.radius)
    (belowSecond : le radius second.radius) : Convergent dimension where
  coefficients := fun index => add (first.coefficients index)
    (second.coefficients index)
  radius := radius
  radiusPositive := positive
  normalOn := by
    intro displacement inside
    exact normally_convergent_add
      (first.normalOn displacement
        (FiniteVector.ball_mono belowFirst inside))
      (second.normalOn displacement
        (FiniteVector.ball_mono belowSecond inside))

public theorem addSeriesWithin_value {dimension : Nat}
    (first second : Convergent dimension)
    (radius : selection.Carrier) (positive : lt zero radius)
    (belowFirst : le radius first.radius)
    (belowSecond : le radius second.radius)
    (displacement : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball (FiniteVector.zeroVector dimension)
      (addSeriesWithin first second radius positive belowFirst
        belowSecond).radius displacement) :
    value (addSeriesWithin first second radius positive belowFirst
        belowSecond) displacement inside =
      add
        (value first displacement
          (FiniteVector.ball_mono belowFirst inside))
        (value second displacement
          (FiniteVector.ball_mono belowSecond inside)) := by
  let firstInside := FiniteVector.ball_mono belowFirst inside
  let secondInside := FiniteVector.ball_mono belowSecond inside
  have termsEqual :
      tailTerms
        (addSeriesWithin first second radius positive belowFirst
          belowSecond).coefficients displacement =
      (fun degreeValue => add
        (tailTerms first.coefficients displacement degreeValue)
        (tailTerms second.coefficients displacement degreeValue)) := by
    funext degreeValue
    exact tailTerms_add first.coefficients second.coefficients
      displacement degreeValue
  have sum_congr {left right : Nat → selection.Carrier}
      (equal : left = right)
      (leftSummable : Summable left) (rightSummable : Summable right) :
      sum left leftSummable = sum right rightSummable := by
    cases equal
    rfl
  have seriesEqual :
      sum (tailTerms
          (addSeriesWithin first second radius positive belowFirst
            belowSecond).coefficients displacement)
        (summable_of_absolute_bound
          ((addSeriesWithin first second radius positive belowFirst
            belowSecond).absoluteOn displacement inside)) =
      add
        (sum (tailTerms first.coefficients displacement)
          (summable_of_absolute_bound
            (first.absoluteOn displacement firstInside)))
        (sum (tailTerms second.coefficients displacement)
          (summable_of_absolute_bound
            (second.absoluteOn displacement secondInside))) := by
    let firstSummable := summable_of_absolute_bound
      (first.absoluteOn displacement firstInside)
    let secondSummable := summable_of_absolute_bound
      (second.absoluteOn displacement secondInside)
    calc
      sum (tailTerms
          (addSeriesWithin first second radius positive belowFirst
            belowSecond).coefficients displacement)
          (summable_of_absolute_bound
            ((addSeriesWithin first second radius positive belowFirst
              belowSecond).absoluteOn displacement inside)) =
        sum (fun degreeValue => add
          (tailTerms first.coefficients displacement degreeValue)
          (tailTerms second.coefficients displacement degreeValue))
          (summable_add firstSummable secondSummable) :=
        sum_congr termsEqual _ _
      _ = add
          (sum (tailTerms first.coefficients displacement) firstSummable)
          (sum (tailTerms second.coefficients displacement) secondSummable) :=
        sum_add firstSummable secondSummable
  unfold value
  change add (add (first.coefficients (MultiIndex.zeroIndex dimension))
      (second.coefficients (MultiIndex.zeroIndex dimension)))
      (sum (tailTerms
        (addSeriesWithin first second radius positive belowFirst
          belowSecond).coefficients displacement)
        (summable_of_absolute_bound
          ((addSeriesWithin first second radius positive belowFirst
            belowSecond).absoluteOn displacement inside))) =
    add
      (add (first.coefficients (MultiIndex.zeroIndex dimension))
        (sum (tailTerms first.coefficients displacement)
          (summable_of_absolute_bound
            (first.absoluteOn displacement firstInside))))
      (add (second.coefficients (MultiIndex.zeroIndex dimension))
        (sum (tailTerms second.coefficients displacement)
          (summable_of_absolute_bound
            (second.absoluteOn displacement secondInside))))
  rw [seriesEqual]
  ac_rfl

public theorem normalSum_add_within_le {dimension : Nat}
    (first second : Convergent dimension)
    (radius : selection.Carrier) (positive : lt zero radius)
    (belowFirst : le radius first.radius)
    (belowSecond : le radius second.radius)
    (displacement : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball (FiniteVector.zeroVector dimension)
      (addSeriesWithin first second radius positive belowFirst
        belowSecond).radius displacement) :
    le (normalSum
        (addSeriesWithin first second radius positive belowFirst
          belowSecond) displacement inside)
      (add (normalSum first displacement
          (FiniteVector.ball_mono belowFirst inside))
        (normalSum second displacement
          (FiniteVector.ball_mono belowSecond inside))) := by
  let firstInside := FiniteVector.ball_mono belowFirst inside
  let secondInside := FiniteVector.ball_mono belowSecond inside
  have firstSummable := fullShellMagnitudes_summable first displacement
    firstInside
  have secondSummable := fullShellMagnitudes_summable second displacement
    secondInside
  have pointwise : ∀ degreeValue,
      le (fullShellMagnitudes
          (addSeriesWithin first second radius positive belowFirst
            belowSecond) displacement degreeValue)
        (add (fullShellMagnitudes first displacement degreeValue)
          (fullShellMagnitudes second displacement degreeValue)) := by
    intro degreeValue
    exact shellMagnitude_add_le first.coefficients second.coefficients
      displacement degreeValue
  have bound := summable_sum_le
    (fullShellMagnitudes_summable
      (addSeriesWithin first second radius positive belowFirst
        belowSecond) displacement inside)
    (summable_add firstSummable secondSummable) pointwise
  rw [sum_add firstSummable secondSummable] at bound
  exact bound

public theorem normalSum_scale {dimension : Nat}
    (factor : selection.Carrier) (series : Convergent dimension)
    (displacement : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius displacement) :
    normalSum (scaleSeries factor series) displacement inside =
      mul (abs factor) (normalSum series displacement inside) := by
  let original := fullShellMagnitudes series displacement
  have equal : fullShellMagnitudes (scaleSeries factor series)
      displacement = fun degreeValue => mul (abs factor)
        (original degreeValue) := by
    funext degreeValue
    exact shellMagnitude_scale factor series.coefficients
      displacement degreeValue
  have sum_congr {left right : Nat → selection.Carrier}
      (same : left = right)
      (firstSummable : Summable left) (secondSummable : Summable right) :
      sum left firstSummable = sum right secondSummable := by
    cases same
    rfl
  calc
    normalSum (scaleSeries factor series) displacement inside =
      sum (fun degreeValue => mul (abs factor) (original degreeValue))
        (summable_scale (abs factor)
          (fullShellMagnitudes_summable series displacement inside)) :=
      sum_congr equal _ _
    _ = mul (abs factor) (normalSum series displacement inside) :=
      sum_scale (abs factor)
        (fullShellMagnitudes_summable series displacement inside)

@[expose] public noncomputable def finiteSeriesSumWitness
    {dimension : Nat} {α : Type}
    (terms : α → Convergent dimension)
    (radius : selection.Carrier) (positive : lt zero radius)
    (termRadius : ∀ index, (terms index).radius = radius) :
    List α → { total : Convergent dimension // total.radius = radius }
  | [] => ⟨constantSeries dimension zero radius positive, rfl⟩
  | index :: rest => by
      let previous := finiteSeriesSumWitness terms radius positive
        termRadius rest
      have belowTerm : le radius (terms index).radius := by
        rw [termRadius index]
        exact le_refl radius
      have belowPrevious : le radius previous.val.radius := by
        rw [previous.property]
        exact le_refl radius
      exact ⟨addSeriesWithin (terms index) previous.val radius positive
        belowTerm belowPrevious, rfl⟩

@[expose] public noncomputable def finiteSeriesSum
    {dimension : Nat} {α : Type}
    (terms : α → Convergent dimension)
    (radius : selection.Carrier) (positive : lt zero radius)
    (termRadius : ∀ index, (terms index).radius = radius)
    (indices : List α) : Convergent dimension :=
  (finiteSeriesSumWitness terms radius positive termRadius indices).val

public theorem finiteSeriesSum_radius
    {dimension : Nat} {α : Type}
    (terms : α → Convergent dimension)
    (radius : selection.Carrier) (positive : lt zero radius)
    (termRadius : ∀ index, (terms index).radius = radius)
    (indices : List α) :
    (finiteSeriesSum terms radius positive termRadius indices).radius =
      radius :=
  (finiteSeriesSumWitness terms radius positive termRadius indices).property

public theorem finiteSeriesSum_coefficients
    {dimension : Nat} {α : Type}
    (terms : α → Convergent dimension)
    (radius : selection.Carrier) (positive : lt zero radius)
    (termRadius : ∀ index, (terms index).radius = radius)
    (indices : List α) (coefficientIndex : MultiIndex.carrier dimension) :
    (finiteSeriesSum terms radius positive termRadius indices).coefficients
      coefficientIndex =
    indices.foldr (fun index total =>
      add ((terms index).coefficients coefficientIndex) total) zero := by
  induction indices with
  | nil =>
      simp only [finiteSeriesSum, finiteSeriesSumWitness]
      change constantCoefficients dimension zero coefficientIndex = zero
      by_cases degreeZero : MultiIndex.degree dimension coefficientIndex = 0
      · simp [constantCoefficients, degreeZero]
      · simp [constantCoefficients, degreeZero]
  | cons index rest induction =>
      change add ((terms index).coefficients coefficientIndex)
        ((finiteSeriesSum terms radius positive termRadius rest).coefficients
          coefficientIndex) = _
      rw [induction]
      rfl

public theorem finiteSeriesSum_value
    {dimension : Nat} {α : Type}
    (terms : α → Convergent dimension)
    (radius : selection.Carrier) (positive : lt zero radius)
    (termRadius : ∀ index, (terms index).radius = radius)
    (indices : List α)
    (displacement : FiniteVector.carrier dimension)
    (insideRadius : FiniteVector.ball
      (FiniteVector.zeroVector dimension) radius displacement) :
    value (finiteSeriesSum terms radius positive termRadius indices)
      displacement (by simpa only [finiteSeriesSum_radius] using
        insideRadius) =
    indices.foldr (fun index total =>
      add (value (terms index) displacement
        (by rw [termRadius index]; exact insideRadius)) total) zero := by
  induction indices with
  | nil =>
      change value (constantSeries dimension zero radius positive)
        displacement insideRadius = zero
      exact constantSeries_value dimension zero radius positive
        displacement insideRadius
  | cons index rest induction =>
      change value
        (addSeriesWithin (terms index)
          (finiteSeriesSum terms radius positive termRadius rest) radius
          positive
          (by rw [termRadius index]; exact le_refl radius)
          (by rw [finiteSeriesSum_radius]; exact le_refl radius))
        displacement insideRadius = _
      rw [addSeriesWithin_value]
      rw [induction]
      rfl

public theorem normalSum_finite_series_le
    {dimension : Nat} {α : Type}
    (terms : α → Convergent dimension)
    (radius : selection.Carrier) (positive : lt zero radius)
    (termRadius : ∀ index, (terms index).radius = radius)
    (indices : List α)
    (displacement : FiniteVector.carrier dimension)
    (insideRadius : FiniteVector.ball
      (FiniteVector.zeroVector dimension) radius displacement) :
    le (normalSum (finiteSeriesSum terms radius positive termRadius
          indices) displacement
        (by simpa only [finiteSeriesSum_radius] using insideRadius))
      (indices.foldr (fun index total =>
        add (normalSum (terms index) displacement
          (by rw [termRadius index]; exact insideRadius)) total) zero) := by
  induction indices with
  | nil =>
      change le (normalSum
        (constantSeries dimension zero radius positive) displacement
        insideRadius) zero
      rw [normalSum_constant, abs_zero]
      exact le_refl zero
  | cons index rest induction =>
      have productInside : FiniteVector.ball
          (FiniteVector.zeroVector dimension)
          (addSeriesWithin (terms index)
            (finiteSeriesSum terms radius positive termRadius rest) radius
            positive
            (by rw [termRadius index]; exact le_refl radius)
            (by rw [finiteSeriesSum_radius]; exact le_refl radius)).radius
          displacement := insideRadius
      have addBound := normalSum_add_within_le (terms index)
        (finiteSeriesSum terms radius positive termRadius rest)
        radius positive
        (by rw [termRadius index]; exact le_refl radius)
        (by rw [finiteSeriesSum_radius]; exact le_refl radius)
        displacement productInside
      have combined := add_le_add (le_refl
        (normalSum (terms index) displacement
          (by rw [termRadius index]; exact insideRadius))) induction
      exact le_trans addBound combined

end

end Problib.Analysis.Real.PowerSeries
