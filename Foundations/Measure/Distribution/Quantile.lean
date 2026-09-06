module

public import Foundations.Measure.Distribution.Basic

set_option autoImplicit false

namespace Foundations.Measure.Real

open Foundations.Real
open Foundations.Real.Construction

public section

/-- Existence of the generalized inverse (quantile) `Q(u) = inf {x ∈ [0, 1] | u ≤ F(x)}`
via Dedekind completeness (`exists_glb`). -/
theorem DistributionFunction.existsQuantile (distribution : DistributionFunction) (threshold : UnitInterval) :
    ∃ quantile : UnitInterval,
      (∀ point, Dedekind.le threshold.val (distribution.function point).val →
        Dedekind.le quantile.val point.val) ∧
      ∀ lower, (∀ point, Dedekind.le threshold.val (distribution.function point).val →
        Dedekind.le lower point.val) → Dedekind.le lower quantile.val := by
  let level := fun value => ∃ point : UnitInterval, point.val = value ∧
    Dedekind.le threshold.val (distribution.function point).val
  have upperIn : Dedekind.le threshold.val (distribution.function unitOne).val := by
    rw [distribution.upper]
    exact threshold.property.2
  have nonnegative : ∀ point, level point → Dedekind.le Dedekind.zero point := by
    rintro point ⟨value, rfl, _⟩
    exact value.property.1
  rcases Dedekind.selection.completeOrder.complete.exists_glb level ⟨Dedekind.one, unitOne, rfl, upperIn⟩
      ⟨Dedekind.zero, nonnegative⟩ with ⟨quantile, lower, greatest⟩
  refine ⟨⟨quantile, greatest _ nonnegative,
      lower _ ⟨unitOne, rfl, upperIn⟩⟩, ?_, ?_⟩
  · intro point included
    exact lower _ ⟨point, rfl, included⟩
  · intro candidate bound
    apply greatest candidate
    rintro point ⟨value, rfl, included⟩
    exact bound value included

@[expose] noncomputable def DistributionFunction.quantile (distribution : DistributionFunction)
    (threshold : UnitInterval) : UnitInterval :=
  Classical.choose (distribution.existsQuantile threshold)

theorem DistributionFunction.quantile_lower (distribution : DistributionFunction)
    (threshold point : UnitInterval)
    (included : Dedekind.le threshold.val (distribution.function point).val) :
    Dedekind.le (distribution.quantile threshold).val point.val :=
  (Classical.choose_spec (distribution.existsQuantile threshold)).1 point included

theorem DistributionFunction.quantile_greatest (distribution : DistributionFunction)
    (threshold : UnitInterval) (lower : Carrier)
    (bound : ∀ point, Dedekind.le threshold.val (distribution.function point).val →
      Dedekind.le lower point.val) :
    Dedekind.le lower (distribution.quantile threshold).val :=
  (Classical.choose_spec (distribution.existsQuantile threshold)).2 lower bound

/-- Right-continuity and completeness ensure threshold attainment: `u ≤ F(Q(u))`. -/
theorem DistributionFunction.quantile_member (distribution : DistributionFunction)
    (threshold : UnitInterval) :
    Dedekind.le threshold.val (distribution.function (distribution.quantile threshold)).val := by
  classical
  apply Classical.byContradiction
  intro missing
  have strictlyBelow := notLeIffLt.mp missing
  have notUpper : ¬Dedekind.le Dedekind.one (distribution.quantile threshold).val := by
    intro above
    have same : distribution.quantile threshold = unitOne :=
      Subtype.ext (Dedekind.leAntisymm (distribution.quantile threshold).property.2 above)
    rw [same, distribution.upper] at missing
    exact missing threshold.property.2
  rcases distribution.rightContinuous (distribution.quantile threshold)
      ⟨(distribution.quantile threshold).property.2, notUpper⟩ threshold.val strictlyBelow with
    ⟨right, aboveQuantile, valueBelow⟩
  apply aboveQuantile.2
  apply distribution.quantile_greatest threshold right.val
  intro point pointIn
  apply Classical.byContradiction
  intro missingOrder
  have pointBelow := notLeIffLt.mp missingOrder
  exact valueBelow.2 (Dedekind.leTrans pointIn (distribution.monotone pointBelow.1))

/-- The fundamental Galois connection (threshold equivalence):
`Q(u) ≤ x ↔ u ≤ F(x)` for all `u, x ∈ [0, 1]`. -/
theorem DistributionFunction.quantile_le_iff (distribution : DistributionFunction)
    (threshold point : UnitInterval) :
    Dedekind.le (distribution.quantile threshold).val point.val ↔
      Dedekind.le threshold.val (distribution.function point).val :=
  ⟨fun included => Dedekind.leTrans (distribution.quantile_member threshold)
      (distribution.monotone included), distribution.quantile_lower threshold point⟩

theorem DistributionFunction.quantile_monotone (distribution : DistributionFunction)
    {left right : UnitInterval} (included : Dedekind.le left.val right.val) :
    Dedekind.le (distribution.quantile left).val (distribution.quantile right).val :=
  (distribution.quantile_le_iff left (distribution.quantile right)).mpr
    (Dedekind.leTrans included (distribution.quantile_member right))

theorem DistributionFunction.quantile_measurable (distribution : DistributionFunction) :
    MeasurableMap unitBorel unitBorel distribution.quantile :=
  unitMonotone_measurable (fun included => distribution.quantile_monotone included)

theorem DistributionFunction.quantile_zero (distribution : DistributionFunction) :
    distribution.quantile unitZero = unitZero := by
  apply Subtype.ext
  exact Dedekind.leAntisymm
    (distribution.quantile_lower unitZero unitZero (distribution.function unitZero).property.1)
    (distribution.quantile unitZero).property.1

end

end Foundations.Measure.Real
