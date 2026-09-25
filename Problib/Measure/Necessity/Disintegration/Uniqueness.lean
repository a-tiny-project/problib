module

public import Problib.Measure.Necessity.Density
public import Problib.Measure.Disintegration.Reconstruction
public import Problib.Measure.Kernel.Product.Algebra
public import Problib.Measure.StandardBorel.Countable

set_option autoImplicit false

namespace Problib.Measure.Necessity.Disintegration.Uniqueness

public section

open Problib.Measure
open Problib.Real

attribute [local instance] Classical.propDecidable

theorem first_positive_rat : (0 : Rat) < 1 / 3 := by
  apply (Rat.lt_div_iff (by decide : (0 : Rat) < 3)).mpr
  rw [Rat.zero_mul]
  decide

theorem second_positive_rat : (0 : Rat) < 2 / 3 := by
  apply (Rat.lt_div_iff (by decide : (0 : Rat) < 3)).mpr
  rw [Rat.zero_mul]
  decide

def firstWeight : ENNReal := ENNReal.ofRat (1 / 3) (Rat.le_of_lt first_positive_rat)
def secondWeight : ENNReal := ENNReal.ofRat (2 / 3) (Rat.le_of_lt second_positive_rat)

theorem weights_sum : ENNReal.add firstWeight secondWeight = ENNReal.one := by
  change ENNReal.finite (NNReal.add (NNReal.ofRat (1 / 3) (Rat.le_of_lt first_positive_rat))
    (NNReal.ofRat (2 / 3) (Rat.le_of_lt second_positive_rat))) = ENNReal.one
  rw [← NNReal.ofRat_add]
  have sum : (1 / 3 : Rat) + 2 / 3 = 1 := by
    have numeric : (1 : Rat) + 2 = 3 := by
      simp [Rat.add_def']
      rfl
    rw [Rat.div_def, Rat.div_def, ← Rat.add_mul, numeric,
      Rat.mul_inv_cancel _ (by decide : (3 : Rat) ≠ 0)]
  simp only [sum, NNReal.ofRat_one]
  rfl

theorem first_nonzero : firstWeight ≠ ENNReal.zero := by
  have positive : ENNReal.lt ENNReal.zero firstWeight := by
    rw [firstWeight, ← ENNReal.ofRat_zero]
    exact (ENNReal.ofRat_lt_iff _ _ _ _).mpr first_positive_rat
  intro equal
  rw [equal] at positive
  exact positive.2 positive.1

theorem second_nonzero : secondWeight ≠ ENNReal.zero := by
  have positive : ENNReal.lt ENNReal.zero secondWeight := by
    rw [secondWeight, ← ENNReal.ofRat_zero]
    exact (ENNReal.ofRat_lt_iff _ _ _ _).mpr second_positive_rat
  intro equal
  rw [equal] at positive
  exact positive.2 positive.1

theorem weights_different : firstWeight ≠ secondWeight := by
  have less : ENNReal.lt firstWeight secondWeight :=
    (ENNReal.ofRat_lt_iff _ _ _ _).mpr (by
      apply (Rat.div_lt_iff (by decide : (0 : Rat) < 3)).mpr
      rw [Rat.div_mul_cancel (by decide : (3 : Rat) ≠ 0)]
      decide)
  intro equal
  rw [equal] at less
  exact less.2 less.1

noncomputable def distribution (first second : ENNReal) : Measure (Space.discrete Bool) :=
  Measure.add (Measure.smul first (Measure.dirac (Space.discrete Bool) false))
    (Measure.smul second (Measure.dirac (Space.discrete Bool) true))

theorem distribution_apply (first second : ENNReal) (set : Set Bool) :
    distribution first second set =
      ENNReal.add (ENNReal.mul first (if set false then ENNReal.one else ENNReal.zero))
        (ENNReal.mul second (if set true then ENNReal.one else ENNReal.zero)) := by
  classical
  rw [distribution, Measure.add_apply_measurable _ _ True.intro,
    Measure.smul_apply_measurable _ _ True.intro,
    Measure.smul_apply_measurable _ _ True.intro,
    Measure.dirac_apply _ _ True.intro, Measure.dirac_apply _ _ True.intro]

theorem distribution_probability (first second : ENNReal)
    (normalized : ENNReal.add first second = ENNReal.one) :
    Measure.IsProbability (distribution first second) := by
  constructor
  simpa only [distribution_apply, Set.univ, if_true, ENNReal.mul_one] using normalized

noncomputable def conditional (first second : ENNReal) :
    Kernel (Space.discrete Unit) (Space.discrete Bool) :=
  Kernel.const _ (distribution first second)

theorem conditional_finite (first second : ENNReal)
    (normalized : ENNReal.add first second = ENNReal.one) :
    Kernel.IsFinite (conditional first second) :=
  Kernel.IsFinite.const _ (distribution_probability first second normalized).to_finite

noncomputable def product (first second : ENNReal)
    (normalized : ENNReal.add first second = ENNReal.one) :
    Measure (Space.product (Space.discrete Bool) (Space.discrete Unit)) :=
  Measure.reverseSemiproduct Necessity.Density.reference (conditional first second)
    (conditional_finite first second normalized).toSFinite

theorem product_apply (first second : ENNReal)
    (normalized : ENNReal.add first second = ENNReal.one)
    {set : Set (Bool × Unit)}
    (measurable : (Space.product (Space.discrete Bool) (Space.discrete Unit)).Measurable set) :
    product first second normalized set =
      ENNReal.mul (distribution first second (fun value => set (value, ()))) ENNReal.top := by
  rw [product, Measure.reverseSemiproduct_apply _ _ _ measurable]
  have constant : (fun secondValue => conditional first second secondValue
      (Set.preimage (fun firstValue => (firstValue, secondValue)) set)) =
      (fun _ : Unit => distribution first second (fun value => set (value, ()))) := by
    funext input
    cases input
    rfl
  rw [constant, lintegral_const, Necessity.Density.reference_univ]

/-- Both probability kernels yield the same s-finite joint measure under the
infinite-atom parameter reference measure. -/
theorem products_equal : product firstWeight secondWeight weights_sum =
    product secondWeight firstWeight ((ENNReal.add_comm _ _).trans weights_sum) := by
  apply Measure.ext
  intro set measurable
  rw [product_apply _ _ _ measurable, product_apply _ _ _ measurable]
  classical
  by_cases first : set (false, ()) <;> by_cases second : set (true, ()) <;>
    simp only [distribution_apply, first, second, if_true, if_false,
      ENNReal.mul_one, ENNReal.mul_zero, ENNReal.add_zero, ENNReal.zero_add,
      ENNReal.zero_mul, ENNReal.mul_top_of_ne_zero first_nonzero,
      ENNReal.mul_top_of_ne_zero second_nonzero, ENNReal.add_comm secondWeight firstWeight]

theorem product_univ (first second : ENNReal)
    (normalized : ENNReal.add first second = ENNReal.one) :
    product first second normalized Set.univ = ENNReal.top := by
  rw [product_apply _ _ _ (Space.product _ _).univ]
  change ENNReal.mul (distribution first second Set.univ) ENNReal.top = _
  rw [(distribution_probability first second normalized).univ_eq_one, ENNReal.one_mul]

theorem marginal_eq (first second : ENNReal)
    (normalized : ENNReal.add first second = ENNReal.one) :
    Measure.secondMarginal (product first second normalized) = Necessity.Density.reference := by
  apply Measure.ext
  intro set _
  classical
  by_cases member : set ()
  · have equal : set = Set.univ := by
      apply Set.ext
      intro input
      cases input
      exact ⟨fun _ => True.intro, fun _ => member⟩
    rw [equal, Measure.secondMarginal_apply _ True.intro,
      Set.preimage_univ, product_univ, Necessity.Density.reference_univ]
  · have equal : set = Set.empty := by
      apply Set.ext
      intro input
      cases input
      exact ⟨fun present => member present, False.elim⟩
    rw [equal, (Measure.secondMarginal _).empty_apply, Necessity.Density.reference.empty_apply]

/-- First exact disintegration record for the shared s-finite joint measure. -/
noncomputable def firstDisintegration :
    Measure.Disintegration (product firstWeight secondWeight weights_sum) where
  conditional := conditional firstWeight secondWeight
  conditionalSFinite := (conditional_finite _ _ weights_sum).toSFinite
  reconstruction := by
    rw [Measure.Disintegrates, marginal_eq]
    rfl

/-- Second exact disintegration record for the shared s-finite joint measure. -/
noncomputable def secondDisintegration :
    Measure.Disintegration (product firstWeight secondWeight weights_sum) where
  conditional := conditional secondWeight firstWeight
  conditionalSFinite := (conditional_finite _ _ ((ENNReal.add_comm _ _).trans weights_sum)).toSFinite
  reconstruction := by
    rw [Measure.Disintegrates, marginal_eq]
    exact products_equal.symm

theorem conditional_different (input : Unit) :
    firstDisintegration.conditional input ≠ secondDisintegration.conditional input := by
  intro equal
  have masses := congrArg (fun measure => measure (fun value => value = false)) equal
  change distribution firstWeight secondWeight (fun value => value = false) =
    distribution secondWeight firstWeight (fun value => value = false) at masses
  simp only [distribution_apply, Bool.true_eq_false, if_true, if_false,
    ENNReal.mul_one, ENNReal.mul_zero, ENNReal.add_zero] at masses
  exact weights_different masses

/-- The two conditional kernels disagree on the false singleton at every input,
so their disagreement set is not marginal-null. -/
theorem conditional_not_ae_equal :
    ¬(Measure.secondMarginal (product firstWeight secondWeight weights_sum)).AEEq
      (fun input => firstDisintegration.conditional input)
      (fun input => secondDisintegration.conditional input) := by
  intro equal
  have failed : Set.complement (fun input => firstDisintegration.conditional input =
      secondDisintegration.conditional input) = Set.univ := by
    apply Set.ext
    intro input
    exact ⟨fun _ => True.intro, fun _ => conditional_different input⟩
  change Measure.secondMarginal _ (Set.complement (fun input =>
    firstDisintegration.conditional input = secondDisintegration.conditional input)) = ENNReal.zero at equal
  rw [failed, marginal_eq, Necessity.Density.reference_univ] at equal
  exact ENNReal.top_ne_finite NNReal.zero equal

/-- The constructed joint measure on Bool times Unit is s-finite. -/
noncomputable def product_sFinite (first second : ENNReal)
    (normalized : ENNReal.add first second = ENNReal.one) :
    Measure.SFinite (product first second normalized) :=
  (Necessity.Density.reference_sFinite.semiproduct
    (conditional_finite first second normalized).toSFinite).map
      (fun value => (value.2, value.1)) (Space.swap_measurable _ _)

/-- The discrete Boolean space is standard Borel. -/
noncomputable def source_standardBorel : StandardBorel (Space.discrete Bool) :=
  StandardBorel.ofNatInjection (fun value => match value with | false => 0 | true => 1) (by
    intro first second equal
    cases first <;> cases second <;> simp_all)

/-- Both conditional kernels are probability measures at every parameter input. -/
theorem both_probability (input : Unit) :
    Measure.IsProbability (firstDisintegration.conditional input) ∧
      Measure.IsProbability (secondDisintegration.conditional input) :=
  ⟨distribution_probability _ _ weights_sum,
    distribution_probability _ _ ((ENNReal.add_comm _ _).trans weights_sum)⟩

/-- The second marginal of the joint measure is not σ-finite. -/
theorem marginal_not_sigmaFinite :
    ¬Nonempty (Measure.SigmaFinite (Measure.secondMarginal (product firstWeight secondWeight weights_sum))) := by
  rw [marginal_eq]
  exact Necessity.Density.reference_not_sigmaFinite

/-- An s-finite joint measure can admit two exact disintegration kernels that
are everywhere probability kernels yet fail almost-everywhere equality under
the non-σ-finite second marginal. -/
theorem s_finite_probability_conditionals_not_unique :
    ∃ joint : Measure (Space.product (Space.discrete Bool) (Space.discrete Unit)),
      Nonempty (Measure.SFinite joint) ∧
      ∃ first second : Measure.Disintegration joint,
        (∀ input, Measure.IsProbability (first.conditional input)) ∧
        (∀ input, Measure.IsProbability (second.conditional input)) ∧
        ¬(Measure.secondMarginal joint).AEEq
          (fun input => first.conditional input) (fun input => second.conditional input) :=
  ⟨product firstWeight secondWeight weights_sum, ⟨product_sFinite _ _ weights_sum⟩,
    firstDisintegration, secondDisintegration, (fun input => (both_probability input).1),
    (fun input => (both_probability input).2), conditional_not_ae_equal⟩

end

end Problib.Measure.Necessity.Disintegration.Uniqueness
