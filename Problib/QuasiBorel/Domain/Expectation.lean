module

public import Problib.QuasiBorel.Domain.Exponential
public import Problib.QuasiBorel.Domain.Weight
public import Problib.QuasiBorel.Measurable.Hom
public import Problib.QuasiBorel.SFinite.Counting
public import Problib.QuasiBorel.SFinite.Weight
public import Problib.Measure.Integral.Lebesgue.Algebra
public import Problib.Measure.Integral.Lebesgue.Convergence
public import Problib.Measure.Integral.Lebesgue.Measure
public import Problib.Measure.Integral.Lebesgue.Transport
public import Problib.Real.Series.Algebra
public import Problib.Real.Series.Tail

/-!
# Expectation as a continuous functional

For a predomain `D` and an s-finite law `μ` on its space, this module defines
expectation against `μ` as a continuous map `(D ⇒ W) → W`. Its value at a
test `f` is the Lebesgue integral of `f` against `μ`. It preserves suprema of
increasing test sequences by monotone convergence. Neither statement needs a
finite-mass, probability or integrability premise. The assignment
`μ ↦ expectation μ` is a quasi-Borel morphism into the continuation object
`J D = (D ⇒ W) ⇒ W` of Vákár, Kammar and Staton.

Not claimed: a predomain order on laws; that expectations against continuous
tests separate laws on a nondiscrete `D`; and the probabilistic powerdomain,
its closure under random families, or the identification of Problib's
represented laws with that paper's randomisable expectation operators.

Witnesses: the zero law gives zero expectation. An infinite point mass gives
infinite expectation to the constant test one. A two-step sequence reaches its
supremum at stage one. On counting measure over the naturals, the tests that
count the first `stage` naturals have finite expectation at every stage. Their
supremum is infinite and is never reached.
-/

set_option autoImplicit false

namespace Problib.QuasiBorel.Domain.Predomain

public section

open Problib.Domain
open Problib.Measure hiding Space
open Problib.Measure.Real (borel)
open Problib.Real (ENNReal)
open Problib.QuasiBorel.SFinite (realSource weightSpace Law object mass)

universe v

section Expectation

variable {D : Predomain.{0, v} realSource}

/-- Integration against a law is continuous in the test. -/
theorem lintegral_continuous (law : Law D.space) :
    (homOrder D weight).Continuous weightOrder
      (fun test : Hom D weight => lintegral law.val test.val) where
  monotone := fun below => lintegral_mono law.val (fun point => below point)
  preserves := by
    intro tests increasing
    exact lintegral_iSup law.val (fun index point => (tests index).val point)
      (fun index => SFinite.weight_measurable (tests index).val)
      (fun index point => increasing index (index + 1) (Nat.le_succ index) point)

/-- Pairing of a continuous test with a law, as a quasi-Borel morphism: the
s-finite integral read at the test's underlying morphism. -/
@[expose] noncomputable def testValue (D : Predomain.{0, v} realSource) :
    QuasiBorel.Hom (Space.product (exponential D weight).space (object D.space))
      weightSpace :=
  QuasiBorel.Hom.comp (SFinite.integral D.space)
    (Space.productMap
      (Space.subtypeVal (Space.exponential D.space weightSpace)
        (fun test => D.order.Continuous weight.order test.toFun))
      (QuasiBorel.Hom.identity (object D.space)))

theorem testValue_apply (test : Hom D weight) (law : Law D.space) :
    testValue D (test, law) = lintegral law.val test.val :=
  SFinite.integral_apply test.val law

/-- Expectation against a law, a continuous map `(D ⇒ W) → W`. -/
@[expose] noncomputable def expectation (law : Law D.space) :
    Hom (exponential D weight) weight :=
  ⟨QuasiBorel.Hom.comp (testValue D)
      (Space.pair (QuasiBorel.Hom.identity (exponential D weight).space)
        (QuasiBorel.Hom.constant (exponential D weight).space (object D.space) law)), by
    show (homOrder D weight).Continuous weightOrder
      (fun test : Hom D weight => testValue D (test, law))
    rw [show (fun test : Hom D weight => testValue D (test, law)) =
        fun test => lintegral law.val test.val from
      funext (fun test => testValue_apply test law)]
    exact lintegral_continuous law⟩

theorem expectation_apply (law : Law D.space) (test : Hom D weight) :
    expectation law test = lintegral law.val test.val :=
  testValue_apply test law

/-- Monotone convergence: expectation of the supremum of increasing tests is
the supremum of their expectations, with no premise on the law's mass. -/
theorem expectation_homSup (law : Law D.space) (tests : Nat → Hom D weight)
    (increasing : ∀ point, weight.order.Chain (fun index => tests index point)) :
    expectation law (homSup D weight tests increasing) =
      ENNReal.iSup (fun index => expectation law (tests index)) := by
  simp only [expectation_apply]
  exact lintegral_iSup law.val (fun index point => (tests index).val point)
    (fun index => SFinite.weight_measurable (tests index).val)
    (fun index point => increasing point index (index + 1) (Nat.le_succ index))

theorem expectation_constant (law : Law D.space) (value : ENNReal) :
    expectation law (Hom.constant D weight value) =
      ENNReal.mul value (mass D.space law) := by
  rw [expectation_apply, SFinite.mass_apply]
  exact lintegral_const law.val value

theorem expectation_pure_constant (point : D.space.Carrier) (value : ENNReal) :
    expectation (SFinite.pure D.space point) (Hom.constant D weight value) = value := by
  rw [expectation_constant, SFinite.mass_pure, ENNReal.mul_one]

/-- The continuation object `J D = (D ⇒ W) ⇒ W`. -/
@[expose] noncomputable def continuation (D : Predomain.{0, v} realSource) :
    Predomain realSource :=
  exponential (exponential D weight) weight

/-- Laws as expectation functionals, a quasi-Borel morphism into `J D`. -/
@[expose] noncomputable def expectationMap (D : Predomain.{0, v} realSource) :
    QuasiBorel.Hom (object D.space) (continuation D).space :=
  (Space.curry (QuasiBorel.Hom.comp (testValue D)
      (Space.pair (Space.second (object D.space) (exponential D weight).space)
        (Space.first (object D.space) (exponential D weight).space)))).subtypeLift
    (fun functional => (homOrder D weight).Continuous weightOrder functional.toFun)
    (fun law => (expectation law).property)

theorem expectationMap_apply (law : Law D.space) :
    (expectationMap D law : Hom (exponential D weight) weight) = expectation law :=
  Hom.ext (fun _ => rfl)

end Expectation

section Witness

/-- The zero law gives every test zero expectation. -/
theorem expectation_zero {D : Predomain.{0, v} realSource} (test : Hom D weight) :
    expectation (SFinite.zero D.space) test = ENNReal.zero := by
  rw [expectation_apply, SFinite.zero_val]
  exact lintegral_zero_measure _

/-- The naturals with every subset measurable, as a discrete predomain. -/
@[expose, implicit_reducible] noncomputable def naturals : Predomain realSource where
  space := Space.ofMeasurable borel (Problib.Measure.Space.discrete Nat)
  order := CPO.discrete Nat
  random_sup := fun _ _ accepted => accepted 0

/-- An infinite point mass gives the constant test one infinite expectation. -/
theorem expectation_infinitePoint :
    expectation (SFinite.scale naturals.space
        (ENNReal.top, SFinite.pure naturals.space (0 : Nat)))
      (Hom.constant naturals weight ENNReal.one) = ENNReal.top := by
  rw [expectation_constant, SFinite.mass_scale, SFinite.mass_pure, ENNReal.mul_one,
    ENNReal.one_mul]

/-- Constant tests stepping from zero to one after stage zero. -/
@[expose] noncomputable def stepTest (stage : Nat) : Hom naturals weight :=
  Hom.constant naturals weight (if stage = 0 then ENNReal.zero else ENNReal.one)

theorem stepTest_le_one (stage index : Nat) :
    ENNReal.le (stepTest stage index) ENNReal.one := by
  change ENNReal.le (if stage = 0 then ENNReal.zero else ENNReal.one) ENNReal.one
  by_cases first : stage = 0
  · rw [ite_eq_left first]
    exact ENNReal.zero_le _
  · rw [ite_eq_right first]
    exact ENNReal.le_refl _

theorem stepTest_increasing (index : Nat) :
    weight.order.Chain (fun stage => stepTest stage index) := by
  intro first second before
  change ENNReal.le (if first = 0 then ENNReal.zero else ENNReal.one)
    (if second = 0 then ENNReal.zero else ENNReal.one)
  by_cases initial : first = 0
  · rw [ite_eq_left initial]
    exact ENNReal.zero_le _
  · rw [ite_eq_right initial, ite_eq_right (by omega : ¬second = 0)]
    exact ENNReal.le_refl _

theorem homSup_stepTest :
    homSup naturals weight stepTest stepTest_increasing =
      Hom.constant naturals weight ENNReal.one := by
  apply Hom.ext
  intro index
  apply ENNReal.le_antisymm
  · exact ENNReal.iSup_le (fun stage => stepTest_le_one stage index)
  · exact ENNReal.le_iSup (fun stage => stepTest stage index) 1

theorem expectation_stepTest_zero :
    expectation (SFinite.pure naturals.space (0 : Nat)) (stepTest 0) = ENNReal.zero := by
  exact (expectation_pure_constant _ _).trans (ite_eq_left rfl)

theorem expectation_stepTest_iSup :
    ENNReal.iSup (fun stage =>
        expectation (SFinite.pure naturals.space (0 : Nat)) (stepTest stage)) =
      ENNReal.one := by
  rw [← expectation_homSup _ _ stepTest_increasing, homSup_stepTest, expectation_constant,
    SFinite.mass_pure, ENNReal.mul_one]

/-- A natural number as a point of `naturals`. -/
@[expose] def natural (index : Nat) : naturals.space.Carrier := index

/-- Counting measure on the naturals, a law of infinite mass. -/
@[expose] noncomputable def counting : Law naturals.space :=
  SFinite.Law.sum (fun index => SFinite.pure naturals.space (natural index))

theorem expectation_counting (test : Hom naturals weight) :
    expectation counting test = ENNReal.tsum (fun index => test (natural index)) := by
  rw [expectation_apply, counting, SFinite.Law.sum_val, lintegral_sum]
  congr 1
  funext index
  rw [SFinite.pure_val, lintegral_dirac _ _ (SFinite.weight_measurable test.val)]

theorem expectation_counting_one :
    expectation counting (Hom.constant naturals weight ENNReal.one) = ENNReal.top := by
  rw [expectation_counting]
  exact ENNReal.tsum_const_of_ne_zero ENNReal.one_ne_zero

theorem mass_counting : mass naturals.space counting = ENNReal.top := by
  rw [← ENNReal.one_mul (mass naturals.space counting), ← expectation_constant]
  exact expectation_counting_one

/-- Indicator of the naturals below `stage`. -/
@[expose] noncomputable def prefixValue (stage index : Nat) : ENNReal :=
  if index < stage then ENNReal.one else ENNReal.zero

/-- The test that counts the naturals below `stage`. -/
@[expose] noncomputable def prefixTest (stage : Nat) : Hom naturals weight :=
  ⟨QuasiBorel.Hom.ofMeasurable (source := borel)
      (domain := Problib.Measure.Space.discrete Nat) (codomain := ennrealBorel)
      (function := prefixValue stage)
      (fun _ => True.intro),
    CPO.continuous_from_discrete _ _⟩

theorem prefixTest_le_one (stage index : Nat) :
    ENNReal.le (prefixTest stage index) ENNReal.one := by
  change ENNReal.le (if index < stage then ENNReal.one else ENNReal.zero) ENNReal.one
  by_cases inside : index < stage
  · rw [ite_eq_left inside]
    exact ENNReal.le_refl _
  · rw [ite_eq_right inside]
    exact ENNReal.zero_le _

theorem prefixTest_increasing (index : Nat) :
    weight.order.Chain (fun stage => prefixTest stage index) := by
  intro first second before
  change ENNReal.le (if index < first then ENNReal.one else ENNReal.zero)
    (if index < second then ENNReal.one else ENNReal.zero)
  by_cases inside : index < first
  · rw [ite_eq_left inside, ite_eq_left (by omega : index < second)]
    exact ENNReal.le_refl _
  · rw [ite_eq_right inside]
    exact ENNReal.zero_le _

theorem prefixTest_reached (index : Nat) :
    ENNReal.le ENNReal.one (prefixTest (index + 1) index) := by
  change ENNReal.le ENNReal.one (if index < index + 1 then ENNReal.one else ENNReal.zero)
  rw [ite_eq_left (Nat.lt_succ_self index)]
  exact ENNReal.le_refl _

theorem homSup_prefixTest :
    homSup naturals weight prefixTest prefixTest_increasing =
      Hom.constant naturals weight ENNReal.one := by
  refine Hom.ext (fun (index : Nat) => ENNReal.le_antisymm ?_ ?_)
  · exact ENNReal.iSup_le (fun stage => prefixTest_le_one stage index)
  · exact ENNReal.le_trans (prefixTest_reached index)
      (ENNReal.le_iSup (fun stage => prefixTest stage index) (index + 1))

private theorem partialSum_finite {values : Nat → ENNReal}
    (finite : ∀ index, ENNReal.Finite (values index)) :
    ∀ count, ENNReal.Finite (ENNReal.partialSum values count)
  | 0 => True.intro
  | count + 1 => ENNReal.add_finite (partialSum_finite finite count) (finite count)

/-- Every stage of the counting sequence has finite expectation. -/
theorem expectation_prefixTest_finite (stage : Nat) :
    ENNReal.Finite (expectation counting (prefixTest stage)) := by
  rw [expectation_counting]
  change ENNReal.Finite (ENNReal.tsum (prefixValue stage))
  rw [← ENNReal.partialSum_add_tail _ stage]
  have outside : (fun index => prefixValue stage (stage + index)) = fun _ => ENNReal.zero :=
    funext (fun index => ite_eq_right (by omega))
  have tail : ENNReal.tsum (fun index => prefixValue stage (stage + index)) =
      ENNReal.zero := by
    rw [outside, ENNReal.tsum, show ENNReal.partialSum (fun _ => ENNReal.zero) =
      fun _ => ENNReal.zero from funext ENNReal.partialSum_zero]
    exact ENNReal.iSup_const _
  rw [tail, ENNReal.add_zero]
  apply partialSum_finite
  intro index
  unfold prefixValue
  by_cases inside : index < stage
  · rw [ite_eq_left inside]
    exact True.intro
  · rw [ite_eq_right inside]
    exact True.intro

/-- The counting sequence's expectations increase to infinity without reaching
it, and their supremum is the expectation of the constant test one. -/
theorem expectation_prefixTest_iSup :
    ENNReal.iSup (fun stage => expectation counting (prefixTest stage)) = ENNReal.top := by
  rw [← expectation_homSup counting prefixTest prefixTest_increasing, homSup_prefixTest,
    expectation_counting_one]

end Witness

end

end Problib.QuasiBorel.Domain.Predomain
