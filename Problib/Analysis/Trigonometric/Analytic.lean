module

public import Problib.Analysis.Trigonometric.Derivative
public import Problib.Analysis.Real.PowerSeries.SubstitutionComposition

/-! Sine and cosine are analytic everywhere.

Around a center `c`, the addition formulas write `sin (c + d)` as
`sin c · cos d + cos c · sin d`, one weighted factorial series in `d` whose
weights mix the cosine and sine weights. Its local series has radius one at
every center, so no series is recentered. Composition then carries sine and
cosine through any analytic function.
-/

set_option autoImplicit false

namespace Problib.Analysis

open Problib.Real.Construction.Dedekind
open Problib.Analysis.Real
open Problib.Analysis.Real.PowerSeries
open Problib.Analysis.Trigonometric

noncomputable section

/-- Sine is analytic on the whole line. -/
public theorem analytic_on_sin :
    AnalyticOn (fun _ : FiniteVector.carrier 1 => True)
      (fun point => sin (point 0)) := by
  refine ⟨FiniteVector.is_open_univ 1, fun center _ => ?_⟩
  let weight := Weight.combine (sin (center 0)) cosineWeight (cos (center 0)) sineWeight
  refine ⟨weightedSeries weight one one_positive, fun _ _ => True.intro, ?_⟩
  intro point inside
  rw [weightedSeries_value, weighted_combine]
  change sin (point 0) = add (mul (sin (center 0)) (cos (sub (point 0) (center 0))))
    (mul (cos (center 0)) (sin (sub (point 0) (center 0))))
  rw [← sin_add, add_sub_cancel]

/-- Cosine is analytic on the whole line. -/
public theorem analytic_on_cos :
    AnalyticOn (fun _ : FiniteVector.carrier 1 => True)
      (fun point => cos (point 0)) := by
  refine ⟨FiniteVector.is_open_univ 1, fun center _ => ?_⟩
  let weight := Weight.combine (cos (center 0)) cosineWeight (neg (sin (center 0)))
    sineWeight
  refine ⟨weightedSeries weight one one_positive, fun _ _ => True.intro, ?_⟩
  intro point inside
  rw [weightedSeries_value, weighted_combine]
  change cos (point 0) = add (mul (cos (center 0)) (cos (sub (point 0) (center 0))))
    (mul (neg (sin (center 0))) (sin (sub (point 0) (center 0))))
  rw [neg_mul, ← sub_eq_add_neg, ← cos_add, add_sub_cancel]

/-- The sine of an analytic function is analytic. -/
public theorem analytic_on_sin_comp {dimension : Nat}
    {region : FiniteVector.carrier dimension → Prop}
    {function : FiniteVector.carrier dimension → selection.Carrier}
    (analytic : AnalyticOn region function) :
    AnalyticOn region (fun point => sin (function point)) :=
  analytic_on_comp (inner := fun point _ => function point)
    analytic.left (fun _ => analytic) analytic_on_sin (fun _ _ => True.intro)

/-- The cosine of an analytic function is analytic. -/
public theorem analytic_on_cos_comp {dimension : Nat}
    {region : FiniteVector.carrier dimension → Prop}
    {function : FiniteVector.carrier dimension → selection.Carrier}
    (analytic : AnalyticOn region function) :
    AnalyticOn region (fun point => cos (function point)) :=
  analytic_on_comp (inner := fun point _ => function point)
    analytic.left (fun _ => analytic) analytic_on_cos (fun _ _ => True.intro)

end

end Problib.Analysis
