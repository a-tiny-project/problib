module

public import Problib.Measure.Decomposition.RadonNikodym
public import Problib.Measure.Real.Density
public import Problib.Measure.Integral.Density.AlmostEverywhere

set_option autoImplicit false

namespace Problib.Measure.Necessity.Density

open Problib.Real

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
    Measure.dirac_apply_univ, ENNReal.mul_one]

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
  rw [two, ← ENNReal.ofRat_one]
  exact (ENNReal.ofRat_lt_iff 1 2 (by decide) (by decide)).mpr (by decide)

public theorem one_ne_two : ENNReal.one ≠ two := by
  intro equal
  have less := one_lt_two
  rw [equal] at less
  exact less.2 less.1

public theorem two_ne_zero : two ≠ ENNReal.zero := by
  intro equal
  have included := one_lt_two.1
  rw [equal] at included
  exact ENNReal.one_ne_zero (ENNReal.eq_zero_of_le_zero included)

/-- Weighting the infinite-atom reference measure by any nonzero scalar density
reproduces the reference measure. -/
public theorem reference_withDensity_nonzero (factor : ENNReal)
    (nonzero : factor ≠ ENNReal.zero) :
    reference.withDensity (fun _ => factor) = reference := by
  rw [reference.withDensity_const, reference_eq_top_smul,
    Measure.smul_smul, ENNReal.mul_top_of_ne_zero nonzero]

/-- Constant densities one and two produce the same weighted measure under the
infinite-atom reference measure. -/
public theorem same_weighted_measure :
    reference.withDensity (fun _ => ENNReal.one) =
      reference.withDensity (fun _ => two) := by
  rw [reference_withDensity_nonzero _ ENNReal.one_ne_zero,
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
  exact ENNReal.top_ne_finite NNReal.zero equal

/-- Finite-valued measurable densities are not uniquely determined by their
weighted measures under an s-finite reference measure. -/
public theorem finite_valued_densities_are_not_unique_for_s_finite :
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
public theorem s_finite_reference_does_not_imply_density_uniqueness :
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
  rcases ENNReal.mul_eq_zero_iff.mp nullSet with topZero | diracZero
  · exact False.elim (ENNReal.top_ne_finite NNReal.zero topZero)
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
  · rw [zero, ENNReal.zero_mul] at mass
    exact ENNReal.one_ne_zero mass
  · rw [ENNReal.mul_top_of_ne_zero zero] at mass
    exact ENNReal.finite_ne_top NNReal.one mass

/-- Absolute continuity between s-finite measures does not imply existence of a
Radon-Nikodym derivative. -/
public theorem s_finite_absolute_continuity_does_not_imply_derivative :
    ¬(∀ {alpha : Type} {space : Space alpha} (target reference : Measure space),
      Measure.SFinite target → Measure.SFinite reference →
      Measure.AbsolutelyContinuous target reference →
      Nonempty (Measure.RadonNikodymDerivative target reference)) := by
  intro select
  rcases select (Measure.dirac (Space.discrete Unit) ()) reference
    (Measure.SFinite.ofFinite (Measure.IsFinite.dirac _ ())) reference_sFinite
    dirac_absolutelyContinuous with ⟨derivative⟩
  exact dirac_has_no_density derivative.density derivative.reconstruct

end Problib.Measure.Necessity.Density

-- D1a additions below. The original necessity results above are preserved.

namespace Problib.Measure.Necessity.Density

open Problib.Real Problib.Measure.Real

/-- A Dirac conditional cannot have a density against atomless uniform
measure, although a mixture of these conditionals can. -/
public theorem dirac_not_density_uniform01 (point : UnitInterval)
    (p : UnitInterval → ENNReal) :
    ¬Measure.IsDensity (Measure.dirac unitBorel point) uniform01 p := by
  intro density
  have dominated : Measure.AbsolutelyContinuous
      (Measure.dirac unitBorel point) uniform01 :=
    density.absolutelyContinuous
  have nullPoint : uniform01.NullSet (Set.singleton point) :=
    uniform01_singleton point
  have forced := dominated (unit_singleton_measurable point) nullPoint
  rw [Measure.dirac_apply_of_mem unitBorel point
    (unit_singleton_measurable point) (show point ∈ Set.singleton point from rfl)] at forced
  exact ENNReal.one_ne_zero forced

/-- The identity mixture has the uniform law even though every conditional
is singular to that same law. -/
public theorem singular_conditional_mixture_is_uniform :
    uniform01.bind
      (Kernel.deterministic (fun x : UnitInterval => x)
        (MeasurableMap.identity unitBorel)) = uniform01 := by
  rw [Measure.bind_deterministic]
  exact Measure.map_id uniform01

public theorem singular_conditionals_have_no_common_uniform_density :
    ¬∃ b : UnitInterval → UnitInterval → ENNReal,
      ∀ point, Measure.IsDensity
        (Measure.dirac unitBorel point) uniform01 (b point) := by
  rintro ⟨b, all⟩
  exact dirac_not_density_uniform01 unitZero _ (all unitZero)

/-- The diagonal pushforward of uniform01 charges a product-null set. -/
public theorem diagonal_not_dominated
    (productFinite : Measure.SFinite uniform01) :
    ¬Measure.AbsolutelyContinuous
      (uniform01.map (fun x : UnitInterval => (x, x))
        (Space.pair_measurable (MeasurableMap.identity unitBorel)
          (MeasurableMap.identity unitBorel)))
      (Measure.prod uniform01 uniform01 productFinite) := by
  intro dominated
  have nullDiagonal := Real.uniform01_prod_diagonal_null productFinite
  have graphMass :
      (uniform01.map (fun x : UnitInterval => (x, x))
        (Space.pair_measurable (MeasurableMap.identity unitBorel)
          (MeasurableMap.identity unitBorel)))
        (fun pair => pair.1 = pair.2) = ENNReal.one := by
    rw [Measure.map_apply _ _ _ unit_diagonal_measurable]
    have preimage : Set.preimage (fun x : UnitInterval => (x, x))
        (fun pair : UnitInterval × UnitInterval => pair.1 = pair.2) =
        Set.univ := by
      apply Set.ext
      intro point
      exact ⟨fun _ => True.intro, fun _ => rfl⟩
    rw [preimage, uniform01_univ]
  have zeroMass := dominated unit_diagonal_measurable nullDiagonal
  rw [graphMass] at zeroMass
  exact ENNReal.one_ne_zero zeroMass

end Problib.Measure.Necessity.Density
