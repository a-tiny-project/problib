module

public import Problib.Analysis.Real.PowerSeries.TaylorCoefficients

/-! Coordinate derivatives of analytic maps, using their local series. -/

set_option autoImplicit false

namespace Problib.Analysis.Real.PowerSeries

open Problib.Real.Construction.Dedekind

noncomputable section

@[expose] public def coordinateSliceAt {dimension : Nat}
    (function : FiniteVector.carrier dimension → selection.Carrier)
    (point : FiniteVector.carrier dimension) (selected : Fin dimension)
    (step : selection.Carrier) : selection.Carrier :=
  function (FiniteVector.addVector point
    (replaceCoordinate (FiniteVector.zeroVector dimension) selected step))

@[expose] public noncomputable def partialDerivativeAt {dimension : Nat}
    (function : FiniteVector.carrier dimension → selection.Carrier)
    (point : FiniteVector.carrier dimension) (selected : Fin dimension) :
    selection.Carrier := by
  classical
  exact if existsDerivative : ∃ derivative,
      Problib.Analysis.Real.HasDerivative
        (coordinateSliceAt function point selected) zero derivative then
    Classical.choose existsDerivative
  else zero

public theorem partialDerivativeAt_eq {dimension : Nat}
    (function : FiniteVector.carrier dimension → selection.Carrier)
    (point : FiniteVector.carrier dimension) (selected : Fin dimension)
    (derivative : selection.Carrier)
    (differentiable : Problib.Analysis.Real.HasDerivative
      (coordinateSliceAt function point selected) zero derivative) :
    partialDerivativeAt function point selected = derivative := by
  classical
  let existsDerivative : ∃ derivative,
      Problib.Analysis.Real.HasDerivative
        (coordinateSliceAt function point selected) zero derivative :=
    ⟨derivative, differentiable⟩
  unfold partialDerivativeAt
  rw [dif_pos existsDerivative]
  exact Problib.Analysis.Real.HasDerivative.unique
    (Classical.choose_spec existsDerivative) differentiable

public theorem analytic_partialDerivativeAt_center {dimension : Nat}
    {region : FiniteVector.carrier dimension → Prop}
    {function : FiniteVector.carrier dimension → selection.Carrier}
    (analytic : AnalyticOn region function)
    (center : FiniteVector.carrier dimension) (member : region center)
    (selected : Fin dimension) :
    ∃ series : Convergent dimension,
      partialDerivativeAt function center selected =
        series.coefficients (MultiIndex.unitIndex selected) := by
  rcases analytic_on_coordinate_derivative_at_center analytic center member
    selected with ⟨series, differentiable⟩
  refine ⟨series, ?_⟩
  exact partialDerivativeAt_eq function center selected
    _ differentiable

public theorem partialDerivativeSeries_radius_le {dimension : Nat}
    (series : Convergent dimension) (selected : Fin dimension) :
    le (partialDerivativeSeries series selected).radius series.radius := by
  let ratio := Problib.Analysis.Real.half one
  let outer := Problib.Analysis.Real.half series.radius
  have ratioPositive := Problib.Analysis.Real.half_positive one_positive
  have outerPositive := Problib.Analysis.Real.half_positive
    series.radiusPositive
  have ratioBelowOne : lt ratio one := by
    have raised := add_lt_add_left ratio ratioPositive
    rwa [add_zero, Problib.Analysis.Real.add_half] at raised
  have outerBelow : lt outer series.radius := by
    have raised := add_lt_add_left outer outerPositive
    rwa [add_zero, Problib.Analysis.Real.add_half] at raised
  rw [partialDerivativeSeries_radius]
  have bound := mul_le_mul_nonnegative_right ratioBelowOne.left
    outerPositive.left
  rw [one_mul] at bound
  exact le_trans bound outerBelow.left

private theorem perturb_displacement {dimension : Nat}
    (center point : FiniteVector.carrier dimension)
    (selected : Fin dimension) (step : selection.Carrier) :
    FiniteVector.subVector
      (FiniteVector.addVector point
        (replaceCoordinate (FiniteVector.zeroVector dimension)
          selected step)) center =
    replaceCoordinate (FiniteVector.subVector point center) selected
      (add ((FiniteVector.subVector point center) selected) step) := by
  funext coordinate
  by_cases same : coordinate = selected
  · subst coordinate
    simp only [FiniteVector.subVector, FiniteVector.addVector,
      replaceCoordinate, FiniteVector.zeroVector]
    change sub (add (point selected) step) (center selected) =
      add (sub (point selected) (center selected)) step
    calc
      sub (add (point selected) step) (center selected) =
          add (sub (add (point selected) step) (point selected))
            (sub (point selected) (center selected)) :=
        (sub_add_sub _ _ _).symm
      _ = add (sub (point selected) (center selected)) step := by
        rw [add_sub_self, add_comm]
  · simp [FiniteVector.subVector, FiniteVector.addVector,
      FiniteVector.zeroVector, replaceCoordinate, same, add_zero]

private theorem perturb_inside_ball {dimension : Nat}
    (point : FiniteVector.carrier dimension)
    (selected : Fin dimension) (step : selection.Carrier)
    {radius : selection.Carrier} (positive : lt zero radius)
    (small : lt (abs step) radius) :
    FiniteVector.ball point radius
      (FiniteVector.addVector point
        (replaceCoordinate (FiniteVector.zeroVector dimension)
          selected step)) := by
  intro coordinate
  by_cases same : coordinate = selected
  · subst coordinate
    simp only [FiniteVector.addVector,
      replaceCoordinate, FiniteVector.zeroVector]
    change lt (abs (sub (add (point selected) step)
      (point selected))) radius
    rwa [add_sub_self]
  · simp only [FiniteVector.addVector, replaceCoordinate,
      if_neg same, FiniteVector.zeroVector]
    rw [add_zero, sub_self, abs_zero]
    exact positive

private theorem value_congr_displacement {dimension : Nat}
    (series : Convergent dimension)
    {first second : FiniteVector.carrier dimension}
    (equal : first = second)
    (firstInside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius first)
    (secondInside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius second) :
    value series first firstInside = value series second secondInside := by
  subst second
  rfl

/-- The derivative of an analytic local witness is represented by the
formal coordinate derivative series throughout its smaller ball. -/
public theorem analytic_representation_partial_derivative
    {dimension : Nat}
    (function : FiniteVector.carrier dimension → selection.Carrier)
    (center : FiniteVector.carrier dimension)
    (series : Convergent dimension)
    (selected : Fin dimension)
    (agree : ∀ point,
      (inside : FiniteVector.ball center series.radius point) →
      function point =
        value series (FiniteVector.subVector point center)
          (by
            intro coordinate
            simpa only [FiniteVector.ball, FiniteVector.zeroVector,
              FiniteVector.subVector, sub_zero] using inside coordinate))
    (point : FiniteVector.carrier dimension)
    (nearCenter : FiniteVector.ball center
      (partialDerivativeSeries series selected).radius point) :
    partialDerivativeAt function point selected =
      value (partialDerivativeSeries series selected)
        (FiniteVector.subVector point center)
        (by
          intro coordinate
          simpa only [FiniteVector.ball, FiniteVector.zeroVector,
            FiniteVector.subVector, sub_zero] using nearCenter coordinate) := by
  let displacement := FiniteVector.subVector point center
  have displacementInside : FiniteVector.ball
      (FiniteVector.zeroVector dimension)
      (partialDerivativeSeries series selected).radius displacement := by
    intro coordinate
    simpa [displacement, FiniteVector.ball, FiniteVector.zeroVector,
      FiniteVector.subVector, sub_zero] using nearCenter coordinate
  have originalDisplacementInside := FiniteVector.ball_mono
    (partialDerivativeSeries_radius_le series selected)
    displacementInside
  have pointInside : FiniteVector.ball center series.radius point := by
    intro coordinate
    simpa [displacement, FiniteVector.ball, FiniteVector.zeroVector,
      FiniteVector.subVector, sub_zero] using
      originalDisplacementInside coordinate
  rcases (FiniteVector.ball_is_open center series.radiusPositive)
    point pointInside with ⟨gap, gapPositive, near⟩
  have localAgree : Problib.Analysis.Real.NearZero
      (fun step => coordinateValueAround series displacement selected step =
        coordinateSliceAt function point selected step) := by
    refine ⟨gap, gapPositive, fun step small => ?_⟩
    let perturbed := FiniteVector.addVector point
      (replaceCoordinate (FiniteVector.zeroVector dimension)
        selected step)
    have nearby : FiniteVector.ball point gap perturbed :=
      perturb_inside_ball point selected step gapPositive small
    have perturbedInside : FiniteVector.ball center series.radius perturbed :=
      near perturbed nearby
    have displaced : FiniteVector.subVector perturbed center =
        replaceCoordinate displacement selected
          (add (displacement selected) step) :=
      perturb_displacement center point selected step
    have seriesInside : FiniteVector.ball
        (FiniteVector.zeroVector dimension) series.radius
        (replaceCoordinate displacement selected
          (add (displacement selected) step)) := by
      intro coordinate
      have close := perturbedInside coordinate
      change lt (abs (sub
        ((replaceCoordinate displacement selected
          (add (displacement selected) step)) coordinate) zero))
        series.radius
      rw [← congrFun displaced coordinate]
      simpa only [sub_zero, FiniteVector.subVector] using close
    have seriesEqual := coordinateValueAround_of_inside series
      displacement selected step seriesInside
    have functionEqual := agree perturbed perturbedInside
    have valueEqual := value_congr_displacement series displaced
      (by
        intro coordinate
        simpa only [FiniteVector.ball, FiniteVector.zeroVector,
          FiniteVector.subVector, sub_zero] using
          perturbedInside coordinate) seriesInside
    change coordinateValueAround series displacement selected step =
      function perturbed
    rw [seriesEqual]
    exact valueEqual.symm.trans functionEqual.symm
  have seriesDerivative :=
    coordinateValueAround_has_derivative_partial_series series
      displacement selected displacementInside
  have functionDerivative :=
    Problib.Analysis.Real.HasDerivative.congr_near_zero
      localAgree seriesDerivative
  exact partialDerivativeAt_eq function point selected _
    functionDerivative

/-- The coordinate derivative of an analytic scalar map is analytic on the
same open domain. Its local witness is the differentiated coefficient series,
with a smaller certified radius. -/
public theorem analytic_on_partial_derivative {dimension : Nat}
    {region : FiniteVector.carrier dimension → Prop}
    {function : FiniteVector.carrier dimension → selection.Carrier}
    (analytic : AnalyticOn region function)
    (selected : Fin dimension) :
    AnalyticOn region
      (fun point => partialDerivativeAt function point selected) := by
  refine ⟨analytic.left, ?_⟩
  intro center member
  rcases analytic.right center member with
    ⟨series, included, agree⟩
  let derivative := partialDerivativeSeries series selected
  refine ⟨derivative, ?_, ?_⟩
  · intro point inside
    exact included point
      (FiniteVector.ball_mono
        (partialDerivativeSeries_radius_le series selected) inside)
  · intro point inside
    exact analytic_representation_partial_derivative function center
      series selected agree point inside

@[expose] public noncomputable def iteratedPartialFunction {dimension : Nat}
    (function : FiniteVector.carrier dimension → selection.Carrier) :
    List (Fin dimension) → FiniteVector.carrier dimension →
      selection.Carrier
  | [] => function
  | selected :: rest =>
      iteratedPartialFunction
        (fun point => partialDerivativeAt function point selected) rest

public theorem iterated_partial_representation {dimension : Nat}
    (function : FiniteVector.carrier dimension → selection.Carrier)
    (center : FiniteVector.carrier dimension)
    (series : Convergent dimension)
    (agree : ∀ point,
      (inside : FiniteVector.ball center series.radius point) →
      function point =
        value series (FiniteVector.subVector point center)
          (by
            intro coordinate
            simpa only [FiniteVector.ball, FiniteVector.zeroVector,
              FiniteVector.subVector, sub_zero] using inside coordinate))
    (steps : List (Fin dimension))
    (point : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball center
      (iteratedPartialSeries series steps).radius point) :
    iteratedPartialFunction function steps point =
      value (iteratedPartialSeries series steps)
        (FiniteVector.subVector point center)
        (by
          intro coordinate
          simpa only [FiniteVector.ball, FiniteVector.zeroVector,
            FiniteVector.subVector, sub_zero] using inside coordinate) := by
  induction steps generalizing function series with
  | nil => exact agree point inside
  | cons selected rest induction =>
      let derivativeSeries := partialDerivativeSeries series selected
      let derivativeFunction := fun point =>
        partialDerivativeAt function point selected
      have derivativeAgree : ∀ point,
          (near : FiniteVector.ball center derivativeSeries.radius point) →
          derivativeFunction point =
            value derivativeSeries (FiniteVector.subVector point center)
              (by
                intro coordinate
                simpa only [FiniteVector.ball, FiniteVector.zeroVector,
                  FiniteVector.subVector, sub_zero] using near coordinate) := by
        intro point near
        exact analytic_representation_partial_derivative function center
          series selected agree point near
      exact induction derivativeFunction derivativeSeries derivativeAgree
        inside

public theorem iterated_partial_value_at_center {dimension : Nat}
    (function : FiniteVector.carrier dimension → selection.Carrier)
    (center : FiniteVector.carrier dimension)
    (series : Convergent dimension)
    (agree : ∀ point,
      (inside : FiniteVector.ball center series.radius point) →
      function point =
        value series (FiniteVector.subVector point center)
          (by
            intro coordinate
            simpa only [FiniteVector.ball, FiniteVector.zeroVector,
              FiniteVector.subVector, sub_zero] using inside coordinate))
    (steps : List (Fin dimension)) :
    iteratedPartialFunction function steps center =
      (iteratedPartialSeries series steps).coefficients
        (MultiIndex.zeroIndex dimension) := by
  let repeated := iteratedPartialSeries series steps
  have centerInside : FiniteVector.ball center repeated.radius center :=
    FiniteVector.ball_center center repeated.radiusPositive
  have represented := iterated_partial_representation function center series
    agree steps center centerInside
  have zeroDisplacement : FiniteVector.subVector center center =
      FiniteVector.zeroVector dimension := by
    funext coordinate
    simp [FiniteVector.subVector, FiniteVector.zeroVector, sub_self]
  have originInside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) repeated.radius
      (FiniteVector.zeroVector dimension) :=
    FiniteVector.ball_center _ repeated.radiusPositive
  have valueEqual := value_congr_displacement repeated zeroDisplacement
    (by
      intro coordinate
      simpa only [FiniteVector.ball, FiniteVector.zeroVector,
        FiniteVector.subVector, sub_zero] using centerInside coordinate)
    originInside
  rw [valueEqual, value_at_origin repeated originInside] at represented
  exact represented

/-- The local coefficient of an analytic witness equals the corresponding
canonical mixed coordinate derivative, divided by its positive factor. -/
public theorem analytic_taylor_coefficient {dimension : Nat}
    {region : FiniteVector.carrier dimension → Prop}
    {function : FiniteVector.carrier dimension → selection.Carrier}
    (analytic : AnalyticOn region function)
    (center : FiniteVector.carrier dimension) (member : region center)
    (index : MultiIndex.carrier dimension) :
    ∃ series : Convergent dimension,
      series.coefficients index =
        div (iteratedPartialFunction function
          (canonicalDerivativeSteps index) center)
          (multiFactorial index) := by
  rcases analytic.right center member with ⟨series, _, agree⟩
  refine ⟨series, ?_⟩
  rw [taylor_coefficient_of_iterated_partial]
  rw [iterated_partial_value_at_center function center series agree]

/-- The Taylor formulation of analyticity: at every point of the open
domain, the normalized mixed derivatives form a convergent local series and
that series evaluates to the function. -/
@[expose] public def TaylorAnalyticOn {dimension : Nat}
    (region : FiniteVector.carrier dimension → Prop)
    (function : FiniteVector.carrier dimension → selection.Carrier) : Prop :=
  FiniteVector.IsOpen region ∧
    ∀ center, region center →
      ∃ series : Convergent dimension,
        (∀ point, FiniteVector.ball center series.radius point →
          region point) ∧
        (∀ point (inside : FiniteVector.ball center series.radius point),
          function point = value series (FiniteVector.subVector point center)
            (by
              intro coordinate
              simpa only [FiniteVector.ball, FiniteVector.zeroVector,
                FiniteVector.subVector, sub_zero] using inside coordinate)) ∧
        ∀ index,
          series.coefficients index =
            div (iteratedPartialFunction function
              (canonicalDerivativeSteps index) center)
              (multiFactorial index)

public theorem analytic_on_iff_taylor_analytic_on {dimension : Nat}
    {region : FiniteVector.carrier dimension → Prop}
    {function : FiniteVector.carrier dimension → selection.Carrier} :
    AnalyticOn region function ↔ TaylorAnalyticOn region function := by
  constructor
  · intro analytic
    refine ⟨analytic.left, fun center member => ?_⟩
    rcases analytic.right center member with ⟨series, within, agrees⟩
    refine ⟨series, within, agrees, fun index => ?_⟩
    rw [taylor_coefficient_of_iterated_partial]
    rw [iterated_partial_value_at_center function center series agrees]
  · intro taylor
    exact ⟨taylor.left, fun center member => by
      rcases taylor.right center member with
        ⟨series, within, agrees, _⟩
      exact ⟨series, within, agrees⟩⟩

end

end Problib.Analysis.Real.PowerSeries
