module

public import Problib.Analysis.Real.PowerSeries.SubstitutionIdentity

/-! Remove the constant coefficient of a local analytic representation before
substituting it into a series centered at the image point. -/

set_option autoImplicit false

namespace Problib.Analysis.Real.PowerSeries

open Problib.Real.Construction.Dedekind

noncomputable section

@[expose] public noncomputable def centerSeries {dimension : Nat}
    (series : Convergent dimension) : Convergent dimension :=
  addSeriesWithin series
    (constantSeries dimension
      (neg (series.coefficients (MultiIndex.zeroIndex dimension)))
      series.radius series.radiusPositive)
    series.radius series.radiusPositive (le_refl series.radius)
    (le_refl series.radius)

public theorem centerSeries_radius {dimension : Nat}
    (series : Convergent dimension) :
    (centerSeries series).radius = series.radius := rfl

public theorem centerSeries_zero_constant {dimension : Nat}
    (series : Convergent dimension) :
    (centerSeries series).coefficients
      (MultiIndex.zeroIndex dimension) = zero := by
  change add (series.coefficients (MultiIndex.zeroIndex dimension))
    (constantCoefficients dimension
      (neg (series.coefficients (MultiIndex.zeroIndex dimension)))
      (MultiIndex.zeroIndex dimension)) = zero
  simp only [constantCoefficients, MultiIndex.degree_zeroIndex,
    ↓reduceIte]
  exact add_neg _

public theorem centerSeries_value {dimension : Nat}
    (series : Convergent dimension)
    (displacement : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius displacement) :
    value (centerSeries series) displacement
      (by simpa only [centerSeries_radius] using inside) =
    sub (value series displacement inside)
      (series.coefficients (MultiIndex.zeroIndex dimension)) := by
  unfold centerSeries
  rw [addSeriesWithin_value]
  rw [constantSeries_value]
  exact (sub_eq_add_neg _ _).symm

public theorem local_series_constant {dimension : Nat}
    (series : Convergent dimension)
    (center : FiniteVector.carrier dimension)
    (function : FiniteVector.carrier dimension → selection.Carrier)
    (agrees : ∀ point
      (inside : FiniteVector.ball center series.radius point),
      function point = value series (FiniteVector.subVector point center)
        (by
          intro coordinate
          simpa only [FiniteVector.ball, FiniteVector.zeroVector,
            FiniteVector.subVector, sub_zero] using inside coordinate)) :
    series.coefficients (MultiIndex.zeroIndex dimension) =
      function center := by
  have insideCenter := FiniteVector.ball_center center
    series.radiusPositive
  have centerAgree := agrees center insideCenter
  have displacementZero : FiniteVector.subVector center center =
      FiniteVector.zeroVector dimension := by
    funext coordinate
    exact sub_self (center coordinate)
  have originInside := FiniteVector.ball_center
    (FiniteVector.zeroVector dimension) series.radiusPositive
  have originAgree : function center =
      value series (FiniteVector.zeroVector dimension) originInside := by
    simpa only [displacementZero] using centerAgree
  rw [value_at_origin] at originAgree
  exact originAgree.symm

public theorem centered_local_value {dimension : Nat}
    (series : Convergent dimension)
    (center : FiniteVector.carrier dimension)
    (function : FiniteVector.carrier dimension → selection.Carrier)
    (agrees : ∀ point
      (inside : FiniteVector.ball center series.radius point),
      function point = value series (FiniteVector.subVector point center)
        (by
          intro coordinate
          simpa only [FiniteVector.ball, FiniteVector.zeroVector,
            FiniteVector.subVector, sub_zero] using inside coordinate))
    (point : FiniteVector.carrier dimension)
    (inside : FiniteVector.ball center series.radius point) :
    value (centerSeries series) (FiniteVector.subVector point center)
      (by
        change FiniteVector.ball (FiniteVector.zeroVector dimension)
          series.radius (FiniteVector.subVector point center)
        intro coordinate
        change lt (abs (sub
          (sub (point coordinate) (center coordinate)) zero))
          series.radius
        rw [sub_zero]
        exact inside coordinate) =
      sub (function point) (function center) := by
  have displacementInside : FiniteVector.ball
      (FiniteVector.zeroVector dimension) series.radius
      (FiniteVector.subVector point center) := by
    intro coordinate
    change lt (abs (sub
      (sub (point coordinate) (center coordinate)) zero))
      series.radius
    rw [sub_zero]
    exact inside coordinate
  rw [centerSeries_value series _ displacementInside]
  rw [← agrees point inside]
  rw [local_series_constant series center function agrees]

end

end Problib.Analysis.Real.PowerSeries
