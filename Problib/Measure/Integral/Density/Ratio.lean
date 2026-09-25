module

public import Problib.Measure.Integral.Density.AlmostEverywhere
public import Problib.Measure.Integral.Density.Change
public import Problib.Measure.Integral.Lebesgue.Markov
public import Problib.Measure.Null.Basic
public import Problib.Measure.Extended.Ratio

set_option autoImplicit false

/-! The density of one measure against another, read off their densities
against a shared base: where the proposal's density `q` is positive, the
target's density against the proposal is `p/q` (`isDensity_densityRatio`). -/

namespace Problib.Measure

open Problib.Real
open Measure

universe u

variable {alpha : Type u} {space : Space alpha}


open Classical in
/-- `p/q` as a finite weight. It is zero where `q` vanishes, and zero where
either side is infinite. -/
@[expose] public noncomputable def densityRatio (p q : alpha → ENNReal) : alpha → NNReal :=
  fun value => if q value = ENNReal.zero then NNReal.zero else
    match p value, q value with
    | .finite numerator, .finite denominator => NNReal.div numerator denominator
    | _, _ => NNReal.zero

/-- Where the denominator is finite and nonzero and the numerator finite, the
ratio times the denominator is the numerator. -/
public theorem mul_densityRatio {p q : alpha → ENNReal} {value : alpha}
    (numeratorFinite : p value ≠ ENNReal.top) (denominatorFinite : q value ≠ ENNReal.top)
    (vanishing : q value = ENNReal.zero → p value = ENNReal.zero) :
    ENNReal.mul (q value) (ENNReal.finite (densityRatio p q value)) = p value := by
  classical
  by_cases zero : q value = ENNReal.zero
  · rw [zero, vanishing zero, ENNReal.zero_mul]
  · unfold densityRatio
    rw [if_neg zero]
    cases numerator : p value with
    | top => exact absurd numerator numeratorFinite
    | finite top =>
      cases denominator : q value with
      | top => exact absurd denominator denominatorFinite
      | finite bottom =>
        have nonzero : bottom ≠ NNReal.zero := fun equal =>
          zero (by rw [denominator, equal]; rfl)
        rw [ENNReal.finite_mul_finite, NNReal.mul_div_cancel top nonzero]

/-- The ratio of measurable densities is measurable.

Route: off the measurable set `{q ≠ 0} ∩ {q ≠ ⊤} ∩ {p ≠ ⊤}` both sides are zero.
On it the ratio is `ofReal (toReal p / toReal q)`, and `div_measurable`
(Measure/Real/Arithmetic.lean:234) composed with `toReal` and `ofReal` is
measurable. `ENNRealMeasurable.indicator` joins the two pieces. -/
public theorem densityRatio_measurable {p q : alpha → ENNReal}
    (numeratorMeasurable : ENNRealMeasurable space p)
    (denominatorMeasurable : ENNRealMeasurable space q) :
    ENNRealMeasurable space (fun value => ENNReal.finite (densityRatio p q value)) := by
  classical
  have constant := ENNRealMeasurable.constant space
  have pieces := ENNRealMeasurable.piecewise
    (denominatorMeasurable.eq_set (constant ENNReal.zero)) (constant ENNReal.zero)
    (ENNRealMeasurable.piecewise (denominatorMeasurable.eq_set (constant ENNReal.top))
      (constant ENNReal.zero)
      (ENNRealMeasurable.piecewise (numeratorMeasurable.eq_set (constant ENNReal.top))
        (constant ENNReal.zero)
        (ENNRealMeasurable.densityRatio numeratorMeasurable denominatorMeasurable)))
  refine (congrArg (ENNRealMeasurable space) (funext fun value => ?_)).mpr pieces
  unfold ennrealPiecewise
  by_cases zero : q value = ENNReal.zero
  · rw [if_pos zero]
    unfold densityRatio
    rw [if_pos zero]
    rfl
  rw [if_neg zero]
  by_cases top : q value = ENNReal.top
  · rw [if_pos top]
    unfold densityRatio
    rw [if_neg zero, top]
    cases p value <;> rfl
  rw [if_neg top]
  by_cases numeratorTop : p value = ENNReal.top
  · rw [if_pos numeratorTop]
    unfold densityRatio
    rw [if_neg zero, numeratorTop]
    rfl
  rw [if_neg numeratorTop]
  have product := mul_densityRatio numeratorTop top fun equal => absurd equal zero
  show ENNReal.finite (densityRatio p q value) = ENNReal.densityRatio (p value) (q value)
  rw [← product]
  exact (ENNReal.densityRatio_mul_of_finite (ENNReal.finite_iff_ne_top.mpr top) zero _).symm

/-- The support step: a target with density `p` and a proposal with density `q`
against one base have density `p/q` between them, provided the target vanishes
wherever the proposal does. The set where `q` is infinite is base-null because
the proposal's mass is finite, so it needs no premise. -/
public theorem isDensity_densityRatio {target proposal base : Measure space}
    {p q : alpha → ENNReal}
    (numeratorMeasurable : ENNRealMeasurable space p)
    (denominatorMeasurable : ENNRealMeasurable space q)
    (targetDensity : IsDensity target base p) (proposalDensity : IsDensity proposal base q)
    (proposalFinite : proposal Set.univ ≠ ENNReal.top)
    (finite : ∀ value, p value ≠ ENNReal.top)
    (support : base (fun value => q value = ENNReal.zero ∧ p value ≠ ENNReal.zero) = ENNReal.zero) :
    IsDensity target proposal (fun value => ENNReal.finite (densityRatio p q value)) := by
  have infiniteNull : base.NullSet (upperLevel q ENNReal.top) := by
    -- `markov` at ⊤ gives ⊤ · base{q ≥ ⊤} ≤ ∫ q d base. The right side is
    -- `proposal univ` (`proposalDensity`, `withDensity_apply` at `univ`, and
    -- restriction to `univ`), which is finite. If base{q ≥ ⊤} were nonzero,
    -- `ENNReal.top_mul_of_ne_zero` would make the left side ⊤.
    have bound := markov base denominatorMeasurable ENNReal.top
    have total : lintegral base q = proposal Set.univ := by
      rw [proposalDensity.eq_withDensity, Measure.withDensity_apply base q space.univ,
        Measure.restrict_univ]
    rw [total] at bound
    apply Classical.byContradiction
    intro nonzero
    rw [ENNReal.top_mul_of_ne_zero nonzero, ENNReal.top_le_iff] at bound
    exact proposalFinite bound
  have agree : base.AEEq (fun value => ENNReal.mul (q value)
      (ENNReal.finite (densityRatio p q value))) p := by
    refine (infiniteNull.union support).mono fun value disagree => ?_
    -- Outside both null sets, `q value < ⊤` and `q value = 0 → p value = 0`.
    apply Classical.byContradiction
    intro outside
    apply disagree
    have notTop : q value ≠ ENNReal.top := fun top => outside (Or.inl (by
      show ENNReal.le ENNReal.top (q value)
      rw [top]
      exact ENNReal.le_refl _))
    exact mul_densityRatio (finite value) notTop fun zero =>
      Classical.byContradiction fun nonzero => outside (Or.inr ⟨zero, nonzero⟩)
  rw [IsDensity, targetDensity.eq_withDensity, proposalDensity.eq_withDensity,
    Measure.withDensity_withDensity base denominatorMeasurable
      (densityRatio_measurable numeratorMeasurable denominatorMeasurable)]
  exact (withDensity_congr_ae agree).symm


end Problib.Measure
