import Problib.Inference.SecondMoment
import Problib.Inference.SecondMoment.Product
import Problib.Inference.Necessity.Density

set_option autoImplicit false

/-! Finite witnesses for second moments. Each exhibit is a law of delivered
value/weight pairs. The proofs evaluate those laws and apply the public moment
and centered-integral theorems. -/

namespace Problib.Inference.SecondMomentWitnesses

open Problib.Real Problib.Measure Problib.Inference
open Problib.Real.Construction
open Problib.Measure.Real (Carrier)
open Problib.Inference.Necessity.Weighting
open Problib.Inference.Necessity.Density (two zeroOrTwo zeroOrTwo_properlyWeighted)

section

/-- Squared weights are measurable even when read without a value integrand. -/
theorem squareReading_measurable (space : Space Unit) :
    ENNRealMeasurable (Space.product space weightSpace)
      (fun draw : Unit × NNReal => ENNReal.mul (drawWeight draw) (drawWeight draw)) :=
  (drawWeight_measurable space).mul (drawWeight_measurable space)

/-- Total second-moment mass is the lower integral of the squared weight. -/
theorem moment_mass {α : Type} {space : Space α}
    (weighted : Measure (Space.product space weightSpace)) :
    (secondMoment weighted) Set.univ = lintegral weighted
      (fun draw => ENNReal.mul (drawWeight draw) (drawWeight draw)) := by
  have total := lintegral_secondMoment weighted (ENNRealMeasurable.constant space ENNReal.one)
  rw [lintegral_const, ENNReal.one_mul] at total
  rw [total]
  apply lintegral_congr
  intro draw
  exact ENNReal.mul_one _

/-- A fair weighted law evaluated on any nonnegative reading. -/
theorem moment_fair {α : Type} (space : Space α) (x y : α) (a b : NNReal) :
    secondMoment (fair (Space.product space weightSpace) (x, a) (y, b)) =
      Measure.smul halfMass (Measure.add
        (Measure.smul (ENNReal.finite (NNReal.mul a a)) (Measure.dirac space x))
        (Measure.smul (ENNReal.finite (NNReal.mul b b)) (Measure.dirac space y))) := by
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  rw [lintegral_secondMoment _ measurable,
    lintegral_fair _ _ _ ((drawWeight_measurable space).mul
      (drawWeight_measurable space) |>.mul (measurable.comp (draw_value_measurable space))),
    lintegral_smul_measure, lintegral_add_measure, lintegral_smul_measure,
    lintegral_smul_measure, lintegral_dirac _ _ measurable, lintegral_dirac _ _ measurable]
  simp only [drawWeight, ENNReal.finite_mul_finite]

theorem map_fair {α β : Type} {space : Space α} {result : Space β}
    (x y : α) (function : α → β) (measurable : MeasurableMap space result function) :
    (fair space x y).map function measurable = fair result (function x) (function y) := by
  rw [fair, Measure.map_smul, Measure.map_add, Measure.map_dirac, Measure.map_dirac]
  rfl

/-- A finite lower integral of an NNReal reading certifies its real integral. -/
theorem nnreal_integral {α : Type} {space : Space α} {measure : Measure space}
    {reading : α → NNReal} (measurable : MeasurableMap space weightSpace reading)
    (mass : NNReal) (integral : lintegral measure (fun x => ENNReal.finite (reading x)) =
      ENNReal.finite mass) : HasRealIntegral measure (fun x => (reading x).toReal) mass.toReal := by
  refine ⟨{ positive := reading
            negative := fun _ => NNReal.zero
            positive_measurable := finite_weight_measurable measurable
            negative_measurable := ENNRealMeasurable.constant _ _
            decomposition := fun _ => (Dedekind.sub_zero _).symm
            positiveMass := mass
            negativeMass := NNReal.zero
            positive_integral := integral
            negative_integral := lintegral_zero measure }, ?_⟩
  exact Dedekind.sub_zero _

/-- Mass certified as finite gives a real integral of the constant one. -/
theorem one_integral {α : Type} {space : Space α} {measure : Measure space}
    (mass : NNReal) (total : measure Set.univ = ENNReal.finite mass) :
    HasRealIntegral measure (fun _ => Dedekind.one) mass.toReal := by
  have cert := nnreal_integral (measure := measure) (MeasurableMap.constant space weightSpace NNReal.one) mass
    (by rw [lintegral_const]; change ENNReal.mul ENNReal.one (measure Set.univ) = _; rw [ENNReal.one_mul]; exact total)
  exact cert

/-- The deterministic unit-weight point draw. -/
noncomputable def unitLaw : Measure (Space.product point weightSpace) :=
  (Measure.dirac point ()).map (fun x => (x, NNReal.one)) (unit_weight_measurable point)

theorem unitLaw_pin : unitLaw =
    (Measure.dirac point ()).map (fun x => (x, NNReal.one)) (unit_weight_measurable point) := rfl

theorem unitLaw_properlyWeighted : ProperlyWeighted (Measure.dirac point ()) unitLaw := by
  have probability : Measure.IsProbability (Measure.dirac point ()) := ⟨Measure.dirac_apply_univ _ _⟩
  exact importance_weighted probability (MeasurableMap.constant point weightSpace NNReal.one)
    (by
      refine (Measure.eq_iff_lintegral _ _).mpr fun f hf => ?_
      rw [lintegral_withDensity _ (ENNRealMeasurable.constant _ _) hf]
      apply lintegral_congr
      intro x
      exact (ENNReal.one_mul _).symm)

theorem unitLaw_moment : secondMoment unitLaw = Measure.dirac point () :=
  secondMoment_unitWeight _

theorem split_moment : secondMoment (zeroOrTwo ()) =
    Measure.smul (ENNReal.finite two) (Measure.dirac point ()) := by
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  rw [lintegral_secondMoment _ measurable, Necessity.Density.zeroOrTwo, Kernel.const_apply,
    lintegral_fair _ _ _ ((drawWeight_measurable point).mul
      (drawWeight_measurable point) |>.mul (measurable.comp (draw_value_measurable point))),
    lintegral_smul_measure, lintegral_dirac _ _ measurable]
  show ENNReal.mul halfMass (ENNReal.add
      (ENNReal.mul (ENNReal.mul ENNReal.zero ENNReal.zero) (function ()))
      (ENNReal.mul (ENNReal.mul (ENNReal.ofRat 2 (by decide +kernel))
        (ENNReal.ofRat 2 (by decide +kernel))) (function ()))) = _
  rw [ENNReal.zero_mul, ENNReal.zero_mul, ENNReal.zero_add,
    ← ENNReal.ofRat_mul, ← ENNReal.mul_assoc,
    half_ofRat (2 * 2) 2 _ (by decide +kernel) (by decide +kernel)]
  rfl

/-- Two actual independent fair lanes, retaining both values and product weight. -/
noncomputable def independentLaw : Measure (Space.product (Space.product point point) weightSpace) :=
  (Measure.prod (zeroOrTwo ()) (zeroOrTwo ())
    (Measure.SFinite.ofFinite (zeroOrTwo_properlyWeighted ()).probability.to_finite)).map
      weightedProductSplit (weightedProductSplit_measurable point point)

theorem independentLaw_pin : independentLaw =
    (Measure.prod (zeroOrTwo ()) (zeroOrTwo ())
      (Measure.SFinite.ofFinite (zeroOrTwo_properlyWeighted ()).probability.to_finite)).map
        (fun draws => ((draws.1.1, draws.2.1), NNReal.mul draws.1.2 draws.2.2))
        (weightedProductSplit_measurable point point) := rfl

/-- The new product identity computes the actual independent law's moment mass. -/
theorem independent_mass : (secondMoment independentLaw) Set.univ =
    ENNReal.ofRat 4 (by decide +kernel) := by
  rw [independentLaw, secondMoment_weighted_product]
  have universal : Set.product (Set.univ : Set Unit) (Set.univ : Set Unit) = Set.univ := by
    apply Set.ext
    intro value
    exact ⟨fun _ => True.intro, fun _ => ⟨True.intro, True.intro⟩⟩
  rw [← universal, Measure.prod_apply_product _ _ _ point.univ point.univ,
    split_moment, Measure.smul_apply_measurable _ _ point.univ, Measure.dirac_apply_univ,
    ENNReal.mul_one]
  change ENNReal.mul (ENNReal.ofRat 2 (by decide +kernel))
    (ENNReal.ofRat 2 (by decide +kernel)) = _
  rw [← ENNReal.ofRat_mul]
  exact ofRat_congr (by decide +kernel) _ _

theorem unit_variance :
    HasRealIntegral unitLaw (fun draw =>
      Dedekind.mul (Dedekind.sub draw.2.toReal Dedekind.one)
        (Dedekind.sub draw.2.toReal Dedekind.one)) Dedekind.zero := by
  have raw : HasRealIntegral (secondMoment unitLaw)
      (fun _ => Dedekind.mul Dedekind.one Dedekind.one) Dedekind.one := by
    rw [unitLaw_moment]
    exact (HasRealIntegral.const (Measure.IsProbability.mk (Measure.dirac_apply_univ _ _))
      Dedekind.one).congr fun _ => (Dedekind.mul_one _).symm
  have centered := centered_of_secondMoment unitLaw_properlyWeighted
    (HasRealIntegral.const (Measure.IsProbability.mk (Measure.dirac_apply_univ _ _)) Dedekind.one) raw
  simpa only [Dedekind.one_mul, Dedekind.mul_one, Dedekind.sub_self] using centered

theorem split_variance :
    HasRealIntegral (zeroOrTwo ()) (fun draw =>
      Dedekind.mul (Dedekind.sub draw.2.toReal Dedekind.one)
        (Dedekind.sub draw.2.toReal Dedekind.one)) Dedekind.one := by
  have raw := one_integral two (measure := secondMoment (zeroOrTwo ())) (by
    rw [split_moment, Measure.smul_apply_measurable _ _ point.univ,
      Measure.dirac_apply_univ, ENNReal.mul_one])
  have square : HasRealIntegral (secondMoment (zeroOrTwo ()))
      (fun _ => Dedekind.mul Dedekind.one Dedekind.one) two.toReal :=
    raw.congr fun _ => (Dedekind.mul_one _).symm
  have centered := centered_of_secondMoment (zeroOrTwo_properlyWeighted ())
    (HasRealIntegral.const (Measure.IsProbability.mk (Measure.dirac_apply_univ _ _)) Dedekind.one) square
  simp only [Dedekind.one_mul, Dedekind.mul_one] at centered
  have value : Dedekind.sub two.toReal Dedekind.one = Dedekind.one := by
    rw [two, rationalWeight, NNReal.toReal_ofRat, ← Dedekind.ofRat_one, ← Dedekind.ofRat_sub]
    exact congrArg Dedekind.selection.ofRat (by decide +kernel)
  rw [value] at centered
  exact centered

/-- Scaling the same delivered weights by three changes means by three and
raw second moments by nine. -/
theorem scale_three :
    ProperlyWeighted (Measure.smul (ENNReal.ofRat 3 (by decide +kernel)) (Measure.dirac point ()))
      ((zeroOrTwo ()).map (fun draw => (draw.1, NNReal.mul
        (rationalWeight 3 (by decide +kernel)) draw.2))
        (scale_weight_measurable point (rationalWeight 3 (by decide +kernel)))) ∧
    secondMoment ((zeroOrTwo ()).map
      (fun draw => (draw.1, NNReal.mul (rationalWeight 3 (by decide +kernel)) draw.2))
      (scale_weight_measurable point (rationalWeight 3 (by decide +kernel)))) =
      Measure.smul (ENNReal.ofRat 18 (by decide +kernel)) (Measure.dirac point ()) := by
  constructor
  · have properlyWeighted := weighted_density (density := fun _ => rationalWeight 3 (by decide +kernel)) (MeasurableMap.constant point weightSpace
      (rationalWeight 3 (by decide +kernel))) (zeroOrTwo_properlyWeighted ())
    have same : (Measure.dirac point ()).withDensity (fun _ => ENNReal.ofRat 3 (by decide +kernel)) =
        Measure.smul (ENNReal.ofRat 3 (by decide +kernel)) (Measure.dirac point ()) := by
      refine (Measure.eq_iff_lintegral _ _).mpr fun f hf => ?_
      rw [lintegral_withDensity _ (ENNRealMeasurable.constant _ _) hf, lintegral_smul_measure]
      exact lintegral_smul _ _ hf
    change ProperlyWeighted ((Measure.dirac point ()).withDensity
      (fun _ => ENNReal.ofRat 3 (by decide +kernel))) _ at properlyWeighted
    rw [same] at properlyWeighted
    refine properlyWeighted_iff_lintegral.mpr
      ⟨(zeroOrTwo_properlyWeighted ()).probability.map _ _, fun function measurable => ?_⟩
    rw [lintegral_map _ _ _ (weighted_integrand_measurable measurable),
      ← properlyWeighted.lintegral measurable,
      lintegral_map _ _ _ (weighted_integrand_measurable measurable)]
    apply lintegral_congr
    intro draw
    show ENNReal.mul (ENNReal.finite (NNReal.mul (rationalWeight 3 (by decide +kernel)) draw.2))
      (function draw.1) =
      ENNReal.mul (ENNReal.finite (NNReal.mul draw.2 (rationalWeight 3 (by decide +kernel))))
        (function draw.1)
    rw [NNReal.mul_comm]
  · rw [secondMoment_scale, split_moment, Measure.smul_smul]
    show Measure.smul (ENNReal.mul
      (ENNReal.mul (ENNReal.ofRat 3 (by decide +kernel)) (ENNReal.ofRat 3 (by decide +kernel)))
      (ENNReal.ofRat 2 (by decide +kernel))) _ = _
    rw [← ENNReal.ofRat_mul, ← ENNReal.ofRat_mul]
    exact congrArg (fun factor => Measure.smul factor (Measure.dirac point ()))
      (ofRat_congr (by decide +kernel) _ _)

/-- A Boolean-indexed continuation. Measurability is joint, not a family of
unrelated measures. -/
noncomputable def boolStep (left right : Measure (Space.product point weightSpace)) :
    Kernel bools (Space.product point weightSpace) where
  toFun := fun b => if b then right else left
  measurable := fun {_} _ => ENNRealMeasurable.of_measurableMap
    (MeasurableMap.from_discrete ennrealBorel _)

/-- Zero incoming weight on false, and weight two on true. -/
noncomputable def outerLaw : Measure (Space.product bools weightSpace) :=
  fair (Space.product bools weightSpace) (false, NNReal.zero) (true, two)

theorem outerLaw_pin : outerLaw =
    fair (Space.product bools weightSpace) (false, NNReal.zero) (true, two) := rfl

/-- The false continuation is deterministic of weight one, while true has
weights zero/two. Their second moments are one and two. -/
noncomputable def dependentStep := boolStep unitLaw (zeroOrTwo ())

theorem dependentStep_pin : dependentStep = boolStep unitLaw (zeroOrTwo ()) := rfl

theorem dependentStep_markov (b : Bool) : Measure.IsProbability (dependentStep b) := by
  cases b
  · exact unitLaw_properlyWeighted.probability
  · exact (zeroOrTwo_properlyWeighted ()).probability

/-- The hand-enumerated result has one half at zero, then one quarter each at
zero and four. -/
noncomputable def enumerated : Measure (Space.product point weightSpace) :=
  Measure.add (Measure.smul halfMass (Measure.dirac (Space.product point weightSpace) ((), NNReal.zero)))
    (Measure.smul halfMass (fair (Space.product point weightSpace)
      ((), NNReal.zero) ((), rationalWeight 4 (by decide +kernel))))

theorem enumerated_pin : enumerated =
    Measure.add (Measure.smul halfMass (Measure.dirac (Space.product point weightSpace) ((), NNReal.zero)))
      (Measure.smul halfMass (fair (Space.product point weightSpace)
        ((), NNReal.zero) ((), rationalWeight 4 (by decide +kernel)))) := rfl

/-- An explicit joint law checks value-dependent composition with a zero
incoming weight. -/
theorem dependent_bind_enumerated :
    outerLaw.bind (reweight dependentStep (Kernel.IsSFinite.ofMarkov dependentStep_markov)) =
      enumerated := by
  rw [outerLaw, fair, Measure.smul_bind, Measure.add_bind, Measure.dirac_bind,
    Measure.dirac_bind, reweight_apply, reweight_apply]
  change Measure.smul halfMass (Measure.add
    (unitLaw.map _ _) ((zeroOrTwo ()).map _ _)) = enumerated
  rw [unitLaw, Measure.map_comp, Measure.map_dirac,
    Necessity.Density.zeroOrTwo, Kernel.const_apply, map_fair]
  simp only [NNReal.zero_mul, NNReal.mul_zero]
  have four : NNReal.mul two two = rationalWeight 4 (by decide +kernel) :=
    ((NNReal.ofRat_mul 2 2 (by decide +kernel) (by decide +kernel)).symm).trans
      (NNReal.ofRat_congr (by decide +kernel))
  rw [four, Measure.smul_add]
  rfl

/-- The theorem and the enumeration have the same second-moment measure. -/
theorem dependent_bind_moment :
    secondMoment enumerated =
      (secondMoment outerLaw).bind (secondMomentKernel dependentStep) := by
  rw [← dependent_bind_enumerated]
  exact secondMoment_weighted_bind (fair_probability _ _ _) dependentStep_markov
    (Kernel.IsSFinite.ofMarkov dependentStep_markov)

/-- The enumeration has squared-weight mass four, including its zero row. -/
theorem dependent_bind_mass : (secondMoment enumerated) Set.univ =
    ENNReal.ofRat 4 (by decide +kernel) := by
  rw [moment_mass, enumerated, lintegral_add_measure, lintegral_smul_measure,
    lintegral_dirac _ _ (squareReading_measurable point), lintegral_smul_measure,
    lintegral_fair _ _ _ (squareReading_measurable point)]
  show ENNReal.add (ENNReal.mul halfMass (ENNReal.mul ENNReal.zero ENNReal.zero))
    (ENNReal.mul halfMass (ENNReal.mul halfMass (ENNReal.add (ENNReal.mul ENNReal.zero ENNReal.zero)
      (ENNReal.mul (ENNReal.ofRat 4 (by decide +kernel)) (ENNReal.ofRat 4 (by decide +kernel)))))) = _
  rw [ENNReal.zero_mul, ENNReal.mul_zero, ENNReal.zero_add, ENNReal.zero_add,
    ← ENNReal.ofRat_mul, half_ofRat (4 * 4) 8 _ (by decide +kernel) (by decide +kernel),
    half_ofRat 8 4 _ (by decide +kernel) (by decide +kernel)]

/-- The zero-weight outer law is properly weighted for the zero target. -/
theorem zero_target_properlyWeighted : ProperlyWeighted (Measure.zero bools)
    ((Measure.dirac bools false).map (fun b => (b, NNReal.zero))
      (Space.pair_measurable (MeasurableMap.identity bools)
        (MeasurableMap.constant bools weightSpace NNReal.zero))) :=
  normalized_properlyWeighted (Measure.IsProbability.mk (Measure.dirac_apply_univ bools false))
    NNReal.zero (Measure.zero_apply _) (fun nonzero => False.elim (nonzero rfl))

/-- A zero target contributes no second moment even with nontrivial continuations. -/
theorem zero_target_bind :
    secondMoment (((Measure.dirac bools false).map (fun b => (b, NNReal.zero))
      (Space.pair_measurable (MeasurableMap.identity bools)
        (MeasurableMap.constant bools weightSpace NNReal.zero))).bind
      (reweight dependentStep (Kernel.IsSFinite.ofMarkov dependentStep_markov))) =
      Measure.zero point := by
  rw [secondMoment_weighted_bind
      ((Measure.IsProbability.mk (Measure.dirac_apply_univ bools false)).map _ _)
      dependentStep_markov (Kernel.IsSFinite.ofMarkov dependentStep_markov),
    secondMoment_constantWeight, NNReal.mul_zero]
  change (Measure.smul ENNReal.zero (Measure.dirac bools false)).bind _ = _
  rw [Measure.zero_smul, Measure.zero_bind]

/-- Positive exact block: the fair conditional carries mass two. -/
theorem positive_exact_block :
    secondMoment ((fair bools false true).map (fun b => (b, two))
      (Space.pair_measurable (MeasurableMap.identity bools)
        (MeasurableMap.constant bools weightSpace two))) =
      Measure.smul (ENNReal.finite two)
        (Measure.smul (ENNReal.finite two) (fair bools false true)) := by
  have prob := fair_probability bools false true
  have total : (Measure.smul (ENNReal.finite two) (fair bools false true)) Set.univ =
      ENNReal.finite two := by
    rw [Measure.smul_apply_measurable _ _ bools.univ, prob.univ_eq_one, ENNReal.mul_one]
  apply secondMoment_exactBlock two total
  intro nonzero
  exact (Measure.normalize_eq_of_smul_eq _ _ (fair bools false true) (by
    rw [total])).symm

/-- At zero mass the two distinct point fallbacks give the same zero moment. -/
theorem zero_exact_fallbacks (b : Bool) :
    secondMoment ((Measure.dirac bools b).map (fun x => (x, NNReal.zero))
      (Space.pair_measurable (MeasurableMap.identity bools)
        (MeasurableMap.constant bools weightSpace NNReal.zero))) = Measure.zero bools := by
  have total : (Measure.zero bools) Set.univ = ENNReal.finite NNReal.zero := Measure.zero_apply _
  have identity := secondMoment_exactBlock (sampler := Measure.dirac bools b)
    NNReal.zero total (fun nonzero => False.elim (nonzero rfl))
  change secondMoment ((Measure.dirac bools b).map (fun x => (x, NNReal.zero))
    (Space.pair_measurable (MeasurableMap.identity bools)
      (MeasurableMap.constant bools weightSpace NNReal.zero))) =
    Measure.smul ENNReal.zero (Measure.zero bools) at identity
  rw [Measure.zero_smul] at identity
  exact identity

end

end Problib.Inference.SecondMomentWitnesses
