module

public import Problib.QuasiBorel.SFinite.Mass
public import Problib.Measure.Kernel.Density
public import Problib.Measure.Integral.Density.Algebra

/-!
# S-finite score morphism and terminal law weights

This module identifies s-finite laws on the terminal quasi-Borel space with
extended nonnegative weights in $[0, \infty]$, proving that the score morphism
forms a two-sided quasi-Borel isomorphism with mass evaluation on terminal laws.
A terminal law is a probability law if and only if its score weight is one.
-/

set_option autoImplicit false

namespace Problib.QuasiBorel.SFinite

public section

open Problib.Measure hiding Space
open Problib.Measure.Real (Carrier borel)
open Problib.Real (ENNReal)

private def scoreSeed : Carrier := Problib.Real.Construction.Dedekind.zero

private noncomputable def scoreBase : Kernel ennrealBorel borel :=
  Kernel.const ennrealBorel (Measure.dirac borel scoreSeed)

private noncomputable def scoreBase_sfinite : Kernel.IsSFinite scoreBase :=
  Kernel.IsSFinite.const ennrealBorel (Measure.SFinite.ofFinite (Measure.IsFinite.dirac borel scoreSeed))

private theorem score_density_measurable :
    ENNRealMeasurable (Problib.Measure.Space.product ennrealBorel borel)
      (fun pair => pair.1) :=
  ENNRealMeasurable.identity.comp (Problib.Measure.Space.first_measurable ennrealBorel borel)

private noncomputable def scoreSource : Kernel ennrealBorel borel :=
  scoreBase.withDensity scoreBase_sfinite (fun weight _ => weight) score_density_measurable

private noncomputable def scoreSource_sfinite : Kernel.IsSFinite scoreSource :=
  scoreBase_sfinite.withDensity (fun weight _ => weight) score_density_measurable

private theorem scoreSource_apply (weight : ENNReal) :
    scoreSource weight = Measure.smul weight (Measure.dirac borel scoreSeed) :=
  Measure.withDensity_const (Measure.dirac borel scoreSeed) weight

/-- Quasi-Borel morphism embedding an extended nonnegative weight as an s-finite law on the terminal unit. -/
noncomputable def score : Hom weightSpace (object (Space.terminal realSource)) where
  toFun := by
    intro weight
    refine ⟨Measure.smul weight (Measure.dirac (Space.terminal realSource).toMeasurable ()), ?_⟩
    refine ⟨Presentation.total (fun _ => ()) ((Space.terminal realSource).constant ())
      (scoreSource weight) (scoreSource_sfinite.measure weight), ?_⟩
    rw [Presentation.total_toMeasure, scoreSource_apply, Measure.map_smul, Measure.map_dirac]
  map_random := by
    intro random accepted
    refine ⟨{
      random := fun _ => Sum.inr ()
      accepted := (withFailure (Space.terminal realSource)).constant (Sum.inr ())
      kernel := scoreSource.precomp random accepted
      sfinite := scoreSource_sfinite.precomp random accepted
      law := ?_
    }⟩
    intro seed
    change (Presentation.total (space := Space.terminal realSource)
      (fun _ => ()) ((Space.terminal realSource).constant ())
      (scoreSource (random seed)) (scoreSource_sfinite.measure (random seed))).toMeasure =
        Measure.smul (random seed) (Measure.dirac (Space.terminal realSource).toMeasurable ())
    rw [Presentation.total_toMeasure, scoreSource_apply, Measure.map_smul, Measure.map_dirac]

@[simp] theorem score_val (weight : ENNReal) :
    (score weight).val = Measure.smul weight (Measure.dirac (Space.terminal realSource).toMeasurable ()) := by
  rfl

@[simp] theorem score_zero : score ENNReal.zero = zero (Space.terminal realSource) := by
  apply Law.ext
  rw [score_val, Measure.zero_smul]
  rfl

@[simp] theorem score_one : score ENNReal.one = pure (Space.terminal realSource) () := by
  apply Law.ext
  rw [score_val, Measure.one_smul]
  rfl

@[simp] theorem mass_score (weight : ENNReal) :
    mass (Space.terminal realSource) (score weight) = weight := by
  rw [mass_apply, score_val,
    Measure.smul_apply_measurable _ _ (by exact (Space.terminal realSource).toMeasurable.univ),
    Measure.dirac_apply_univ, ENNReal.mul_one]

@[simp] theorem score_mass (law : Law (Space.terminal realSource)) :
    score (mass (Space.terminal realSource) law) = law := by
  classical
  apply Law.ext
  apply Measure.ext
  intro region measurable
  by_cases member : region ()
  · have equal : region = Set.univ := by
      apply Set.ext
      intro point
      cases point
      exact ⟨fun _ => True.intro, fun _ => member⟩
    rw [equal]
    exact mass_score (mass (Space.terminal realSource) law)
  · have equal : region = Set.empty := by
      apply Set.ext
      intro point
      cases point
      exact ⟨fun present => member present, False.elim⟩
    rw [equal, Measure.empty_apply, Measure.empty_apply]

theorem score_injective : Function.Injective score := by
  intro left right equal
  have same := congrArg (mass (Space.terminal realSource)) equal
  simpa only [mass_score] using same

/-- A scored terminal law is a probability measure if and only if its weight is one. -/
theorem score_probability (weight : ENNReal) :
    Measure.IsProbability (score weight).val ↔ weight = ENNReal.one := by
  constructor
  · intro normalized
    exact (mass_score weight).symm.trans normalized.univ_eq_one
  · intro equal
    rw [equal, score_one, pure_val]
    exact Measure.IsProbability.dirac (Space.terminal realSource).toMeasurable ()

theorem mass_score_hom :
    Hom.comp (mass (Space.terminal realSource)) score = Hom.identity weightSpace := by
  apply Hom.ext
  exact mass_score

theorem score_mass_hom :
    Hom.comp score (mass (Space.terminal realSource)) = Hom.identity (object (Space.terminal realSource)) := by
  apply Hom.ext
  exact score_mass

end

end Problib.QuasiBorel.SFinite
