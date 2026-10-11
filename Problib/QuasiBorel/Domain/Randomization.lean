module

public import Problib.QuasiBorel.Domain.Expectation
public import Problib.QuasiBorel.Domain.Lifting
public import Problib.QuasiBorel.SFinite.Random
public import Problib.QuasiBorel.SFinite.Scale
public import Problib.QuasiBorel.SFinite.Unit
public import Problib.Measure.Kernel.Randomization.Partial
public import Problib.Measure.Integral.Lebesgue.Comap
public import Problib.Measure.Real.Finiteness

/-!
# Randomizations of a predomain

A randomization of a predomain `D` is a map from the real line into the lift
`lift D`: each real seed either fails or returns a point of `D`. Its expectation
integrates a test, extended by zero on failure, against Lebesgue volume on the
seed. The randomizations form the predomain `randomizations D = ℝ ⇒ lift D`, with
the line discrete, and expectation is a continuous map from it into the
continuation object `J D = (D ⇒ W) ⇒ W`. It is continuous in the test and in
the randomization, both by monotone convergence.

Every accepted random family of s-finite laws on `D` has one random
randomization `α` with `randomExpectation (α s) = expectation (μ s)` at every
parameter `s`. The randomization runs the family's own generator on the seeds
that the partial Lebesgue randomizer of its global s-finite kernel returns. It
chooses nothing per parameter, so zero laws, laws of infinite mass and an empty
`D` need no separate case.

Witnesses: the everywhere-failing randomization is the bottom and has zero
expectation. A point mass, an infinite atom and the parameter-dependent family
of point masses on the line are randomized. A pointwise family that is a point
mass on a set `V` of parameters and zero off it has an accepted family only
when `V` is Borel.

Not claimed: that expectation separates randomizations, the quotient of
randomizations by expectation, or the probabilistic powerdomain built from it.
-/

set_option autoImplicit false

namespace Problib.QuasiBorel.Domain.Predomain

public section

open Problib.Domain
open Problib.Measure hiding Space
open Problib.Measure.Real (borel Carrier volume volumeSFinite)
open Problib.Real (ENNReal)
open Problib.QuasiBorel.SFinite (realSource weightSpace Law object mass)

universe v

/-! ### The line and Lebesgue volume -/

/-- The real line with its Borel random elements, as a discrete predomain. -/
@[expose, implicit_reducible] def line : Predomain realSource :=
  discrete (Space.ofMeasurable borel borel)

/-- Lebesgue volume on the line, as a represented law. -/
@[expose] noncomputable def lebesgue : Law line.space :=
  (SFinite.Presentation.total (space := line.space) (fun seed => seed)
    (MeasurableMap.identity borel) volume volumeSFinite).toLaw

/-- A function measurable on the line's induced space is Borel measurable. -/
theorem line_measurable {function : Carrier → ENNReal}
    (measurable : ENNRealMeasurable line.space.toMeasurable function) :
    ENNRealMeasurable borel function :=
  fun threshold => measurable threshold (MeasurableMap.identity borel)

theorem lintegral_lebesgue {function : Carrier → ENNReal}
    (measurable : ENNRealMeasurable line.space.toMeasurable function) :
    lintegral lebesgue.val function = lintegral volume function := by
  have equal := SFinite.Presentation.total_toMeasure (space := line.space)
    (fun seed : Carrier => (seed : line.space.Carrier)) (MeasurableMap.identity borel)
    volume volumeSFinite
  exact (congrArg (fun measure => lintegral measure function) equal).trans
    (lintegral_map volume (fun seed => seed) _ measurable)

/-! ### Randomizations and their expectation -/

variable {D : Predomain.{0, v} realSource}

/-- Randomizations of `D`: continuous maps from the discrete line into the lift. -/
@[expose] noncomputable def randomizations (D : Predomain.{0, v} realSource) :
    Predomain realSource :=
  exponential line (lift D)

theorem extend_le_of_le {lower upper : Hom D weight} (below : (homOrder D weight).le lower upper)
    (point : (lift D).space.Carrier) : ENNReal.le (extend lower point) (extend upper point) := by
  cases point with
  | inl _ => exact ENNReal.zero_le _
  | inr value => exact below value

theorem extend_homSup (tests : Nat → Hom D weight)
    (increasing : ∀ point, weight.order.Chain (fun index => tests index point))
    (point : (lift D).space.Carrier) :
    extend (homSup D weight tests increasing) point =
      ENNReal.iSup (fun index => extend (tests index) point) := by
  cases point with
  | inl _ => exact (ENNReal.iSup_const ENNReal.zero).symm
  | inr _ => rfl

/-- A test read along a randomization, zero where it fails, jointly in the
randomization, the test and the seed. -/
@[expose] noncomputable def alongMap (D : Predomain.{0, v} realSource) :
    QuasiBorel.Hom (Space.product
      (Space.product (randomizations D).space (exponential D weight).space) line.space)
      weightSpace :=
  QuasiBorel.Hom.comp (extendMap D)
    (Space.pair
      (QuasiBorel.Hom.comp
        (Space.second (randomizations D).space (exponential D weight).space)
        (Space.first
          (Space.product (randomizations D).space (exponential D weight).space) line.space))
      (QuasiBorel.Hom.comp (Space.evaluate line.space (lift D).space)
        (Space.productMap
          (QuasiBorel.Hom.comp
            (Space.subtypeVal (Space.exponential line.space (lift D).space)
              (fun function => line.order.Continuous (lift D).order function.toFun))
            (Space.first (randomizations D).space (exponential D weight).space))
          (QuasiBorel.Hom.identity line.space))))

/-- The expectation of a test along a randomization, jointly in both. -/
@[expose] noncomputable def valueMap (D : Predomain.{0, v} realSource) :
    QuasiBorel.Hom (Space.product (randomizations D).space (exponential D weight).space)
      weightSpace :=
  QuasiBorel.Hom.comp (SFinite.integral line.space)
    (Space.pair (Space.curry (alongMap D))
      (QuasiBorel.Hom.constant
        (Space.product (randomizations D).space (exponential D weight).space)
        (object line.space) lebesgue))

theorem along_measurable (random : Hom line (lift D)) (test : Hom D weight) :
    ENNRealMeasurable borel (fun seed => extend test (random seed)) :=
  line_measurable (SFinite.weight_measurable (QuasiBorel.Hom.comp (extend test).val random.val))

theorem valueMap_apply (random : Hom line (lift D)) (test : Hom D weight) :
    valueMap D (random, test) = lintegral volume (fun seed => extend test (random seed)) := by
  change SFinite.integral line.space (Space.curry (alongMap D) (random, test), lebesgue) = _
  rw [SFinite.integral_apply]
  exact lintegral_lebesgue (SFinite.weight_measurable _)

/-- Expectation along a randomization is continuous in the test. -/
theorem along_continuous (random : Hom line (lift D)) :
    (homOrder D weight).Continuous weightOrder
      (fun test : Hom D weight => lintegral volume (fun seed => extend test (random seed))) where
  monotone := fun below => lintegral_mono volume (fun seed => extend_le_of_le below (random seed))
  preserves := by
    intro tests increasing
    change lintegral volume (fun seed =>
        extend (homSup D weight tests (fun point first second order =>
          increasing first second order point)) (random seed)) = _
    exact (lintegral_congr volume (fun seed => extend_homSup tests
        (fun point first second order => increasing first second order point) (random seed))).trans
      (lintegral_iSup volume (fun index seed => extend (tests index) (random seed))
        (fun index => along_measurable random (tests index))
        (fun index seed => extend_le_of_le (increasing index (index + 1) (Nat.le_succ index))
          (random seed)))

/-- Expectation along a randomization, a continuous map `(D ⇒ W) → W`. -/
@[expose] noncomputable def randomExpectation (random : Hom line (lift D)) :
    Hom (exponential D weight) weight :=
  ⟨QuasiBorel.Hom.comp (valueMap D)
      (Space.pair
        (QuasiBorel.Hom.constant (exponential D weight).space (randomizations D).space random)
        (QuasiBorel.Hom.identity (exponential D weight).space)), by
    show (homOrder D weight).Continuous weightOrder
      (fun test : Hom D weight => valueMap D (random, test))
    rw [show (fun test : Hom D weight => valueMap D (random, test)) =
        fun test => lintegral volume (fun seed => extend test (random seed)) from
      funext (fun test => valueMap_apply random test)]
    exact along_continuous random⟩

theorem randomExpectation_apply (random : Hom line (lift D)) (test : Hom D weight) :
    randomExpectation random test = lintegral volume (fun seed => extend test (random seed)) :=
  valueMap_apply random test

/-- Monotone convergence in the test, with no premise on the randomization. -/
theorem randomExpectation_homSup (random : Hom line (lift D)) (tests : Nat → Hom D weight)
    (increasing : ∀ point, weight.order.Chain (fun index => tests index point)) :
    randomExpectation random (homSup D weight tests increasing) =
      ENNReal.iSup (fun index => randomExpectation random (tests index)) :=
  (randomExpectation random).property.preserves tests
    (fun first second order point => increasing point first second order)

/-- Expectation is continuous in the randomization. -/
theorem randomExpectation_continuous :
    (randomizations D).order.Continuous (continuation D).order
      (fun random => (randomExpectation random :
        (continuation D).space.Carrier)) where
  monotone := by
    intro lower upper below test
    exact Eq.mpr (congr (congrArg ENNReal.le (valueMap_apply lower test))
        (valueMap_apply upper test))
      (lintegral_mono volume (fun seed => (extend_continuous test).monotone (below seed)))
  preserves := by
    intro randoms increasing
    apply Subtype.ext
    apply QuasiBorel.Hom.ext
    intro test
    refine (valueMap_apply ((randomizations D).order.sup randoms increasing) test).trans
      (Eq.trans ?_ (congrArg ENNReal.iSup
        (funext (fun index => (valueMap_apply (randoms index) test).symm))))
    exact (lintegral_congr volume (fun seed => (extend_continuous test).preserves
        (fun index => (randoms index).val seed)
        (fun first second order => increasing first second order seed))).trans
      (lintegral_iSup volume (fun index seed => extend test ((randoms index).val seed))
        (fun index => along_measurable (randoms index) test)
        (fun index seed => (extend_continuous test).monotone
          (increasing index (index + 1) (Nat.le_succ index) seed)))

/-- Randomizations as expectation functionals, a continuous map into `J D`. -/
@[expose] noncomputable def randomExpectationMap (D : Predomain.{0, v} realSource) :
    Hom (randomizations D) (continuation D) :=
  ⟨(Space.curry (valueMap D)).subtypeLift
      (fun functional => (homOrder D weight).Continuous weightOrder functional.toFun)
      (fun random => (randomExpectation random).property),
    randomExpectation_continuous⟩

theorem randomExpectationMap_apply (random : Hom line (lift D)) :
    (randomExpectationMap D random : Hom (exponential D weight) weight) =
      randomExpectation random :=
  Hom.ext (fun _ => rfl)

/-! ### Randomizing an accepted family -/

variable {laws : Carrier → Law D.space}

/-- The partial Lebesgue randomizer of a family's global kernel. -/
@[expose] noncomputable def randomizer (family : SFinite.Family D.space laws) :
    Kernel.PartialRandomizer family.kernel :=
  Kernel.PartialRandomizer.ofSFinite family.kernel StandardBorel.real family.sfinite

/-- Failure, or the family's generator at a returned seed. -/
@[expose] def through (family : SFinite.Family D.space laws) :
    Sum Unit Carrier → (lift D).space.Carrier :=
  Sum.elim (fun _ => Sum.inl ()) family.random

theorem through_measurable (family : SFinite.Family D.space laws) :
    MeasurableMap (Problib.Measure.Space.sum (Problib.Measure.Space.discrete Unit) borel)
      (lift D).space.toMeasurable (through family) :=
  MeasurableMap.sum_elim (MeasurableMap.constant _ _ (Sum.inl ()))
    (Space.random_measurable family.accepted)

/-- The family's generator, as a morphism from the line. -/
@[expose] def generatorMap (family : SFinite.Family D.space laws) :
    QuasiBorel.Hom (Space.ofMeasurable borel borel) (lift D).space where
  toFun := family.random
  map_random := fun measurable => (lift D).space.reparam measurable family.accepted

/-- The randomizer, as a morphism from parameter and seed into the sum of
failure and returned seeds. -/
@[expose] noncomputable def randomizerMap (family : SFinite.Family D.space laws) :
    QuasiBorel.Hom (Space.product (Space.sourceObject realSource) line.space)
      (Space.sum (Space.ofMeasurable borel (Problib.Measure.Space.discrete Unit))
        (Space.ofMeasurable borel borel)) where
  toFun := (randomizer family).function
  map_random := fun accepted => SumRandom.of_measurable (MeasurableMap.comp
    (randomizer family).measurable (Problib.Measure.Space.pair_measurable accepted.1 accepted.2))

/-- The randomization of a family, jointly in the parameter and the seed. -/
@[expose] noncomputable def randomizeMap (family : SFinite.Family D.space laws) :
    QuasiBorel.Hom (Space.product (Space.sourceObject realSource) line.space) (lift D).space :=
  QuasiBorel.Hom.comp
    (Space.copair
      (QuasiBorel.Hom.constant (Space.ofMeasurable borel (Problib.Measure.Space.discrete Unit))
        (lift D).space (Sum.inl ()))
      (generatorMap family))
    (randomizerMap family)

/-- The randomization of a family at a parameter. -/
@[expose] noncomputable def randomize (family : SFinite.Family D.space laws) (seed : Carrier) :
    Hom line (lift D) :=
  ⟨Space.curry (randomizeMap family) seed, CPO.continuous_from_discrete _ _⟩

theorem randomize_apply (family : SFinite.Family D.space laws) (parameter seed : Carrier) :
    randomize family parameter seed =
      through family ((randomizer family).function (parameter, seed)) :=
  rfl

theorem randomize_random (family : SFinite.Family D.space laws) :
    (randomizations D).space.Random (randomize family) :=
  (Space.curry (randomizeMap family)).map_random realSource.identity

theorem randomExpectation_randomize (family : SFinite.Family D.space laws) (parameter : Carrier) :
    randomExpectation (randomize family parameter) = expectation (laws parameter) := by
  apply Hom.ext
  intro (test : Hom D weight)
  let partialMap := randomizer family
  have returned : MeasurableMap borel
      (Problib.Measure.Space.sum (Problib.Measure.Space.discrete Unit) borel)
      (fun seed => partialMap.function (parameter, seed)) :=
    MeasurableMap.comp partialMap.measurable (Problib.Measure.Space.pair_measurable
      (MeasurableMap.constant borel borel parameter) (MeasurableMap.identity borel))
  have extended : ENNRealMeasurable (lift D).space.toMeasurable (extend test) :=
    SFinite.weight_measurable (extend test).val
  have measurable : ENNRealMeasurable
      (Problib.Measure.Space.sum (Problib.Measure.Space.discrete Unit) borel)
      (fun point => extend test (through family point)) :=
    ENNRealMeasurable.comp extended (through_measurable family)
  have failsOutside : ∀ point, ¬Set.range Sum.inr point →
      extend test (through family point) = ENNReal.zero := by
    intro point outside
    cases point with
    | inl _ => rfl
    | inr value => exact False.elim (outside ⟨value, rfl⟩)
  have zeroOutside : ∀ point : (lift D).space.Carrier, ¬Set.range Sum.inr point →
      extend test point = ENNReal.zero := by
    intro point outside
    cases point with
    | inl _ => rfl
    | inr value => exact False.elim (outside ⟨value, rfl⟩)
  rw [randomExpectation_apply, expectation_apply]
  calc lintegral volume (fun seed => extend test (randomize family parameter seed))
      = lintegral (volume.map (fun seed => partialMap.function (parameter, seed)) returned)
          (fun point => extend test (through family point)) :=
        (lintegral_map volume (fun seed => partialMap.function (parameter, seed)) returned
          measurable).symm
    _ = lintegral ((volume.map (fun seed => partialMap.function (parameter, seed)) returned).comap
          (MeasurableEmbedding.inr (Problib.Measure.Space.discrete Unit) borel))
          (fun seed => extend test (family.random seed)) :=
        (lintegral_comap_of_zero_outside
          (volume.map (fun seed => partialMap.function (parameter, seed)) returned)
          (MeasurableEmbedding.inr (Problib.Measure.Space.discrete Unit) borel)
          measurable failsOutside).symm
    _ = lintegral (family.kernel parameter) (fun seed => extend test (family.random seed)) :=
        congrArg (fun measure => lintegral measure (fun seed => extend test (family.random seed)))
          (partialMap.law parameter)
    _ = lintegral ((family.kernel parameter).map family.random
          (Space.random_measurable family.accepted)) (extend test) :=
        (lintegral_map (family.kernel parameter) family.random
          (Space.random_measurable family.accepted) extended).symm
    _ = lintegral (((family.kernel parameter).map family.random
          (Space.random_measurable family.accepted)).comap
          (Space.inrEmbedding (Space.terminal realSource) D.space)) (fun point => test point) :=
        (lintegral_comap_of_zero_outside
          ((family.kernel parameter).map family.random (Space.random_measurable family.accepted))
          (Space.inrEmbedding (Space.terminal realSource) D.space) extended zeroOutside).symm
    _ = lintegral (laws parameter).val test.val :=
        congrArg (fun measure => lintegral measure test.val) (family.law parameter)

/-- Every accepted random family of s-finite laws has one random
randomization whose expectation is the family's at every parameter. -/
theorem randomizable (accepted : SFinite.Random D.space laws) :
    ∃ random : Carrier → Hom line (lift D), (randomizations D).space.Random random ∧
      ∀ parameter, randomExpectation (random parameter) = expectation (laws parameter) := by
  rcases accepted with ⟨family⟩
  exact ⟨randomize family, randomize_random family, randomExpectation_randomize family⟩

/-! ### Witnesses -/

/-- The randomization that fails at every seed. -/
@[expose] noncomputable def failing (D : Predomain.{0, v} realSource) : Hom line (lift D) :=
  Hom.constant line (lift D) (Sum.inl ())

theorem failing_le (random : Hom line (lift D)) :
    (randomizations D).order.le (failing D) random :=
  fun _ => True.intro

theorem randomExpectation_failing (test : Hom D weight) :
    randomExpectation (failing D) test = ENNReal.zero := by
  rw [randomExpectation_apply]
  exact lintegral_zero volume

theorem lintegral_pure (point : D.space.Carrier) (test : Hom D weight) :
    lintegral (SFinite.pure D.space point).val test.val = test point :=
  (SFinite.integral_apply test.val (SFinite.pure D.space point)).symm.trans
    (SFinite.integral_pure test.val point)

/-- A point mass is randomized. -/
theorem randomizable_pure (point : D.space.Carrier) :
    ∃ random : Carrier → Hom line (lift D), (randomizations D).space.Random random ∧
      ∀ parameter (test : Hom D weight),
        randomExpectation (random parameter) test = test point := by
  rcases randomizable (laws := fun _ => SFinite.pure D.space point)
      ((object D.space).constant (SFinite.pure D.space point)) with
    ⟨random, accepted, equal⟩
  refine ⟨random, accepted, fun parameter test => ?_⟩
  rw [equal parameter, expectation_apply]
  exact lintegral_pure point test

/-- An infinite atom is randomized, and the constant test one has infinite
expectation along it. -/
theorem randomizable_infiniteAtom (point : D.space.Carrier) :
    ∃ random : Carrier → Hom line (lift D), (randomizations D).space.Random random ∧
      ∀ parameter, randomExpectation (random parameter) (Hom.constant D weight ENNReal.one) =
        ENNReal.top := by
  rcases randomizable
      (laws := fun _ => SFinite.scale D.space (ENNReal.top, SFinite.pure D.space point))
      ((object D.space).constant
        (SFinite.scale D.space (ENNReal.top, SFinite.pure D.space point))) with
    ⟨random, accepted, equal⟩
  refine ⟨random, accepted, fun parameter => ?_⟩
  rw [equal parameter, expectation_constant, SFinite.mass_scale, SFinite.mass_pure,
    ENNReal.mul_one, ENNReal.one_mul]

/-- The point masses at each parameter on the line share one randomizer. -/
theorem randomizable_line :
    ∃ random : Carrier → Hom line (lift line), (randomizations line).space.Random random ∧
      ∀ parameter (test : Hom line weight),
        randomExpectation (random parameter) test = test parameter := by
  rcases randomizable (D := line) (laws := fun parameter => SFinite.pure line.space parameter)
      ((SFinite.unit line.space).map_random (MeasurableMap.identity borel)) with
    ⟨random, accepted, equal⟩
  refine ⟨random, accepted, fun parameter test => ?_⟩
  rw [equal parameter, expectation_apply]
  exact lintegral_pure parameter test

/-- A pointwise family that is a point mass on `V` and zero off it has an
accepted family only when `V` is Borel. -/
theorem measurable_of_random (region : Set Carrier) [DecidablePred region]
    (accepted : SFinite.Random (Space.terminal realSource) (fun parameter =>
      if region parameter then SFinite.pure (Space.terminal realSource) ()
      else SFinite.zero (Space.terminal realSource))) :
    borel.Measurable region := by
  rcases accepted with ⟨family⟩
  have measured := family.toKernel.measurable
    (Problib.Measure.Space.univ (Space.terminal realSource).toMeasurable) ENNReal.zero
  have equal : Set.preimage (fun parameter => family.toKernel parameter Set.univ)
      (ennrealIoi ENNReal.zero) = region := by
    apply Set.ext
    intro parameter
    change ENNReal.lt ENNReal.zero (family.toKernel parameter Set.univ) ↔ region parameter
    rw [ENNReal.zero_lt_iff_ne_zero, SFinite.Family.toKernel_apply]
    by_cases inside : region parameter
    · simp only [ite_eq_left inside]
      change mass (Space.terminal realSource) (SFinite.pure (Space.terminal realSource) ()) ≠
        ENNReal.zero ↔ region parameter
      rw [SFinite.mass_pure]
      exact ⟨fun _ => inside, fun _ => ENNReal.one_ne_zero⟩
    · simp only [ite_eq_right inside]
      change mass (Space.terminal realSource) (SFinite.zero (Space.terminal realSource)) ≠
        ENNReal.zero ↔ region parameter
      rw [SFinite.mass_zero]
      exact ⟨fun nonzero => False.elim (nonzero rfl),
        fun isInside => False.elim (inside isInside)⟩
  rw [← equal]
  exact measured

end

end Problib.QuasiBorel.Domain.Predomain
