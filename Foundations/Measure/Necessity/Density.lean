module

public import Foundations.Measure.Decomposition.RadonNikodym

set_option autoImplicit false

namespace Foundations.Measure.Necessity.Density

open Foundations.Real

/-- Countable sum of unit Dirac measures on the one-point discrete space. -/
public noncomputable def reference : Measure (Space.discrete Unit) :=
  Measure.sum (fun _ : Nat => Measure.dirac (Space.discrete Unit) ())

/-- The countable sum of finite Dirac measures is s-finite. -/
public noncomputable def reference_sFinite : Measure.SFinite reference :=
  Measure.SFinite.sum _ (fun _ =>
    Measure.SFinite.ofFinite (Measure.IsFinite.dirac (Space.discrete Unit) ()))

/-- The infinite-atom reference measure equals infinite scalar scaling of the
underlying Dirac measure. -/
public theorem reference_eq_top_smul :
    reference = Measure.smul ENNReal.top (Measure.dirac (Space.discrete Unit) ()) :=
  Measure.sum_const _

/-- Total mass of the infinite-atom reference measure is infinite. -/
public theorem reference_univ : reference Set.univ = ENNReal.top := by
  rw [reference_eq_top_smul, Measure.smul_apply_measurable _ _ True.intro,
    Measure.dirac_apply_univ, ENNReal.mulOne]

/-- The infinite-atom reference measure on the singleton space is not
sigma-finite. -/
public theorem reference_not_sigmaFinite : ¬Nonempty (Measure.SigmaFinite reference) := by
  rintro ⟨finite⟩
  have covered : Set.iUnion finite.sets () := by
    rw [finite.cover]
    exact True.intro
  rcases covered with ⟨index, member⟩
  have whole : finite.sets index = Set.univ := by
    apply Set.ext
    intro value
    cases value
    exact ⟨fun _ => True.intro, fun _ => member⟩
  have bound := finite.finite index
  rw [whole, reference_univ] at bound
  exact bound

@[expose] public def two : ENNReal := ENNReal.ofRat 2 (by decide)

public theorem one_lt_two : ENNReal.lt ENNReal.one two := by
  rw [two, ← ENNReal.ofRatOne]
  exact (ENNReal.ofRatLtIff 1 2 (by decide) (by decide)).mpr (by decide)

public theorem one_ne_two : ENNReal.one ≠ two := by
  intro equal
  have less := one_lt_two
  rw [equal] at less
  exact less.2 less.1

public theorem two_ne_zero : two ≠ ENNReal.zero := by
  intro equal
  have included := one_lt_two.1
  rw [equal] at included
  exact ENNReal.oneNeZero (ENNReal.eqZeroOfLeZero included)

/-- Weighting the infinite-atom reference measure by any nonzero scalar density
reproduces the reference measure. -/
public theorem reference_withDensity_nonzero (factor : ENNReal)
    (nonzero : factor ≠ ENNReal.zero) :
    reference.withDensity (fun _ => factor) = reference := by
  rw [reference.withDensity_const, reference_eq_top_smul,
    Measure.smul_smul, ENNReal.mulTopOfNeZero nonzero]

/-- Constant densities one and two produce the same weighted measure under the
infinite-atom reference measure. -/
public theorem same_weighted_measure :
    reference.withDensity (fun _ => ENNReal.one) =
      reference.withDensity (fun _ => two) := by
  rw [reference_withDensity_nonzero _ ENNReal.oneNeZero,
    reference_withDensity_nonzero _ two_ne_zero]

/-- Constant densities one and two are not almost everywhere equal under the
infinite-atom reference measure. -/
public theorem densities_not_ae_equal :
    ¬reference.AEEq (fun _ => ENNReal.one) (fun _ => two) := by
  intro equal
  have failureSet :
      Set.complement (fun _ : Unit => ENNReal.one = two) = Set.univ := by
    apply Set.ext
    intro value
    exact ⟨fun _ => True.intro, fun _ => one_ne_two⟩
  change reference (Set.complement (fun _ : Unit => ENNReal.one = two)) =
    ENNReal.zero at equal
  rw [failureSet, reference_univ] at equal
  exact ENNReal.topNeFinite NNReal.zero equal

/-- Finite-valued measurable densities are not uniquely determined by their
weighted measures under an s-finite reference measure. -/
public theorem finite_valued_densities_are_not_unique_for_sFinite :
    Nonempty (Measure.SFinite reference) ∧
      ¬Nonempty (Measure.SigmaFinite reference) ∧
      ENNReal.Finite ENNReal.one ∧ ENNReal.Finite two ∧
      ENNRealMeasurable (Space.discrete Unit) (fun _ => ENNReal.one) ∧
      ENNRealMeasurable (Space.discrete Unit) (fun _ => two) ∧
      reference.withDensity (fun _ => ENNReal.one) =
        reference.withDensity (fun _ => two) ∧
      ¬reference.AEEq (fun _ => ENNReal.one) (fun _ => two) :=
  ⟨⟨reference_sFinite⟩, reference_not_sigmaFinite,
    True.intro, True.intro, ENNRealMeasurable.constant _ _,
    ENNRealMeasurable.constant _ _, same_weighted_measure, densities_not_ae_equal⟩

/-- An s-finite reference measure does not imply almost-everywhere density
uniqueness for identical weighted measures. -/
public theorem sFinite_reference_does_not_imply_density_uniqueness :
    ¬(∀ {alpha : Type} {space : Space alpha} (measure : Measure space),
      Measure.SFinite measure → ∀ (left right : alpha → ENNReal),
      ENNRealMeasurable space left → ENNRealMeasurable space right →
      measure.withDensity left = measure.withDensity right →
      measure.AEEq left right) := by
  intro unique
  exact densities_not_ae_equal
    (unique reference reference_sFinite _ _
      (ENNRealMeasurable.constant _ _) (ENNRealMeasurable.constant _ _)
      same_weighted_measure)

/-- The finite Dirac measure is absolutely continuous with respect to the
infinite-atom reference measure. -/
public theorem dirac_absolutelyContinuous :
    Measure.AbsolutelyContinuous (Measure.dirac (Space.discrete Unit) ()) reference := by
  intro set measurable nullSet
  rw [reference_eq_top_smul, Measure.smul_apply_measurable _ _ measurable] at nullSet
  rcases ENNReal.mulEqZeroIff.mp nullSet with topZero | diracZero
  · exact False.elim (ENNReal.topNeFinite NNReal.zero topZero)
  · exact diracZero

/-- The finite Dirac target measure has no density with respect to the
infinite-atom reference measure. -/
public theorem dirac_has_no_density (density : Unit → ENNReal) :
    ¬Measure.IsDensity (Measure.dirac (Space.discrete Unit) ()) reference density := by
  intro reconstruct
  have mass := reconstruct.apply (Space.discrete Unit).univ
  rw [Measure.dirac_apply_univ, reference.restrict_univ] at mass
  have constant : density = fun _ => density () := by
    funext value
    cases value
    rfl
  rw [constant, lintegral_const, reference_univ] at mass
  by_cases zero : density () = ENNReal.zero
  · rw [zero, ENNReal.zeroMul] at mass
    exact ENNReal.oneNeZero mass
  · rw [ENNReal.mulTopOfNeZero zero] at mass
    exact ENNReal.finiteNeTop NNReal.one mass

/-- Absolute continuity between s-finite measures does not imply existence of a
Radon-Nikodym derivative. -/
public theorem sFinite_absoluteContinuity_does_not_imply_derivative :
    ¬(∀ {alpha : Type} {space : Space alpha} (target reference : Measure space),
      Measure.SFinite target → Measure.SFinite reference →
      Measure.AbsolutelyContinuous target reference →
      Nonempty (Measure.RadonNikodymDerivative target reference)) := by
  intro select
  rcases select (Measure.dirac (Space.discrete Unit) ()) reference
    (Measure.SFinite.ofFinite (Measure.IsFinite.dirac _ ())) reference_sFinite
    dirac_absolutelyContinuous with ⟨derivative⟩
  exact dirac_has_no_density derivative.density derivative.reconstruct

end Foundations.Measure.Necessity.Density
