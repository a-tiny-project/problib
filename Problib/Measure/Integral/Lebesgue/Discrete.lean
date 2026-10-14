module

public import Problib.Measure.Integral.Lebesgue.Algebra

set_option autoImplicit false

/-! Integrals against a measure on the natural numbers in which every set is
measurable. The measure is fixed by its singleton masses, and an integral is
the series of each value weighted by its singleton's mass. -/

namespace Problib.Measure

open Problib.Real

public section

/-- A function on discrete naturals is the series of its values, each placed
on its own singleton. -/
theorem discrete_series (function : Nat → ENNReal) (point : Nat) :
    ENNReal.tsum (fun index =>
        ennrealIndicator (Set.singleton index) (fun _ => function index) point) =
      function point := by
  rw [ENNReal.tsum_eq_of_at_most_one_nonzero _ point]
  · simp [ennrealIndicator, ennrealPiecewise, Set.singleton]
  · intro current different
    have outside : ¬Set.singleton current point := fun same => different same.symm
    simp [ennrealIndicator, ennrealPiecewise, outside]

/-- The integral against a measure on discrete naturals is the series of each
value times its singleton's mass. -/
theorem lintegral_discrete (measure : Measure (Space.discrete Nat))
    (function : Nat → ENNReal) :
    lintegral measure function =
      ENNReal.tsum (fun index =>
        ENNReal.mul (function index) (measure (Set.singleton index))) := by
  have pointwise : function = fun point => ENNReal.tsum (fun index =>
      ennrealIndicator (Set.singleton index) (fun _ => function index) point) :=
    funext fun point => (discrete_series function point).symm
  rw [congrArg (lintegral measure) pointwise, lintegral_tsum _ _ (fun _ _ => True.intro)]
  apply ENNReal.tsum_congr
  intro index
  rw [lintegral_indicator _ _ (Space.discrete_measurable _), lintegral_const,
    Measure.restrict_apply_univ]

end

end Problib.Measure
