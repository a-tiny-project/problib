module

public import Problib.Inference.Population.Conditional
public import Problib.Inference.Reciprocal
public import Problib.Inference.Selection
import Problib.Measure.AlmostEverywhere.Transport
import Problib.Measure.Integral.Density.Change
import Problib.Measure.Integral.Density.Zero
import Problib.Measure.Integral.Lebesgue.Extensionality
import Problib.Measure.Integral.Lebesgue.Transport
import Problib.Measure.Integral.Lebesgue.Zero
import Problib.Measure.Kernel.Measurable
set_option autoImplicit false

/-! # The density of a selected lane

A conditional law of a population disintegrates its extended target along the
marked lane's value, with the marked lane pinned there (`ConditionalLaw`). It
gives the law of the lane that selection draws a density with no closed form:
`x ↦ γ(x) · E_{C(x)}[1/Ẑ]`, for a target `γ` with density `γ(x)` against a
reference (`selected_density`). The positive part of the selected law is the
extended target reweighted by `1/Ẑ` (`selectedPositive_eq_extended`), and the
conditional law turns integration over the extended target into integration
over the target followed by the pinned conditional run.

Both factors of that density can be read off runs of one SMC.

- A conditional run pinned at `x` estimates the density at `x`: `γ(x)/Ẑ_c`
  read off `C(x)` is unbiased for it (`selected_density_unbiased`).
- A forward run's selected lane, weighted by `Ẑ/γ(x)`, is properly weighted for
  the reference restricted to where that density is positive
  (`selected_reciprocal_properlyWeighted`). The selected value with `Ẑ` is
  properly weighted for the target (`selected_properlyWeighted`), and dividing
  by `γ` restricts the reference to `{γ ≠ 0}`. That set differs from the
  density's support only on a null set (`selected_support`): where `γ` is
  positive, the marked lane has positive weight under the extended target, so
  `1/Ẑ` is positive almost surely under the conditional run. -/

namespace Problib.Inference

open Problib.Real Problib.Measure

variable {α : Type} {space : Space α}

public section

/-! ### The selected density -/

/-- The density of the selected lane at a point: the target's density there
times the expected inverse mean weight of the conditional run pinned there. -/
@[expose] noncomputable def selectedDensity {ι : Type} (lanes : Lanes ι)
    (conditional : Kernel space (markedSpace ι space)) (density : α → ENNReal)
    (point : α) : ENNReal :=
  ENNReal.mul (density point) (lintegral (conditional point) (inverseMeanWeight lanes))

theorem selectedDensity_measurable {ι : Type} (lanes : Lanes ι)
    (conditional : Kernel space (markedSpace ι space)) {density : α → ENNReal}
    (measurable : ENNRealMeasurable space density) :
    ENNRealMeasurable space (selectedDensity lanes conditional density) :=
  ENNRealMeasurable.mul measurable
    (Kernel.lintegral_measurable conditional (inverseMeanWeight_measurable lanes space))

/-- From a conditional law of the population, the positive part of the selected
law has density `x ↦ γ(x) · E_{C(x)}[1/Ẑ]` against the reference of `γ`. The
conditional law need not be Markov, and the density need not be finite. -/
theorem selected_density {ι : Type} {lanes : Lanes ι}
    {population : Measure (populationSpace ι space)} {target base : Measure space}
    {conditional : Kernel space (markedSpace ι space)}
    (law : ConditionalLaw lanes population target conditional) {density : α → ENNReal}
    (measurable : ENNRealMeasurable space density)
    (isDensity : Measure.IsDensity target base density) :
    Measure.IsDensity (selectedPositive lanes population) base
      (selectedDensity lanes conditional density) := by
  refine (Measure.eq_iff_lintegral _ _).mpr fun function functionMeasurable => ?_
  have inverseMeasurable := inverseMeanWeight_measurable lanes space
  have readMeasurable := functionMeasurable.comp (reference_measurable lanes space)
  have massMeasurable : ENNRealMeasurable space
      (fun point => lintegral (conditional point) (inverseMeanWeight lanes)) :=
    Kernel.lintegral_measurable conditional inverseMeasurable
  rw [selectedPositive_eq_extended, lintegral_map _ _ _ functionMeasurable,
    lintegral_withDensity _ inverseMeasurable readMeasurable, ← law.disintegrates,
    Measure.lintegral_bind _ _ (ENNRealMeasurable.mul inverseMeasurable readMeasurable),
    lintegral_withDensity _ (selectedDensity_measurable lanes conditional measurable)
      functionMeasurable,
    isDensity.eq_withDensity,
    lintegral_withDensity _ measurable (Kernel.lintegral_measurable conditional
      (ENNRealMeasurable.mul inverseMeasurable readMeasurable))]
  refine lintegral_congr _ fun point => ?_
  have held := lintegral_holdsAt (law.pinned point)
    (function := fun pair => ENNReal.mul (inverseMeanWeight lanes pair.2) (function pair.1))
    (ENNRealMeasurable.mul (inverseMeasurable.comp (Space.second_measurable _ _))
      (functionMeasurable.comp (Space.first_measurable _ _)))
  have commuted : (fun marked : (ι → α × NNReal) × ι => ENNReal.mul (inverseMeanWeight lanes marked)
      (function point)) =
      fun marked => ENNReal.mul (function point) (inverseMeanWeight lanes marked) :=
    funext fun marked => ENNReal.mul_comm _ _
  show ENNReal.mul (density point) (lintegral (conditional point) fun marked =>
      ENNReal.mul (inverseMeanWeight lanes marked) (function (reference marked))) =
    ENNReal.mul (selectedDensity lanes conditional density point) (function point)
  rw [held, commuted, lintegral_smul _ _ inverseMeasurable, selectedDensity,
    ENNReal.mul_assoc, ENNReal.mul_comm (function point)]

/-! ### An estimate from the conditional run -/

/-- The estimate `γ(x)/Ẑ_c` of a marked population drawn at `x`. -/
theorem selectedEstimate_measurable {ι : Type} (lanes : Lanes ι) (space : Space α)
    {density : α → NNReal} (measurable : MeasurableMap space weightSpace density) :
    MeasurableMap (Space.product space (markedSpace ι space)) weightSpace
      (fun pair => NNReal.mul (density pair.1)
        (NNReal.div NNReal.one (meanWeight lanes pair.2.1))) :=
  weight_mul_measurable (MeasurableMap.comp measurable (Space.first_measurable _ _))
    (weight_inverse_measurable (MeasurableMap.comp (meanWeight_measurable lanes space)
      (MeasurableMap.comp (Space.first_measurable _ _) (Space.second_measurable _ _))))

/-- A conditional run pinned at `x`, read through `γ(x)/Ẑ_c`, is an unbiased
estimate of the selected law's density at `x`. It is RAVI's reverse estimate
with the conditional law as the meta kernel. -/
theorem selected_density_unbiased {ι : Type} {lanes : Lanes ι}
    {population : Measure (populationSpace ι space)} {target base : Measure space}
    {conditional : Kernel space (markedSpace ι space)}
    (law : ConditionalLaw lanes population target conditional)
    (markov : ∀ point, Measure.IsProbability (conditional point))
    (finite : Kernel.IsSFinite conditional) {density : α → NNReal}
    (measurable : MeasurableMap space weightSpace density)
    (isDensity : Measure.IsDensity target base fun point => ENNReal.finite (density point)) :
    Measure.IsDensity (selectedPositive lanes population) base
        (selectedDensity lanes conditional fun point => ENNReal.finite (density point)) ∧
      UnbiasedEstimate (selectedDensity lanes conditional fun point => ENNReal.finite (density point))
        (readEstimate conditional finite
          (fun pair => NNReal.mul (density pair.1)
            (NNReal.div NNReal.one (meanWeight lanes pair.2.1)))
          (selectedEstimate_measurable lanes space measurable)) := by
  refine ⟨selected_density law (finite_weight_measurable measurable) isDensity,
    fun point => ?_, fun point => ?_⟩
  · rw [readEstimate_apply]
    exact (markov point).map _ _
  · rw [readEstimate_apply,
      lintegral_map _ _ _ (finite_weight_measurable (MeasurableMap.identity weightSpace))]
    have split : (fun marked : (ι → α × NNReal) × ι => ENNReal.finite
        (NNReal.mul (density point) (NNReal.div NNReal.one (meanWeight lanes marked.1)))) =
        fun marked => ENNReal.mul (ENNReal.finite (density point))
          (inverseMeanWeight lanes marked) :=
      funext fun marked => (ENNReal.finite_mul_finite _ _).symm
    show lintegral (conditional point) (fun marked => ENNReal.finite
        (NNReal.mul (density point) (NNReal.div NNReal.one (meanWeight lanes marked.1)))) = _
    rw [split, lintegral_smul _ _ (inverseMeanWeight_measurable lanes space)]
    rfl

/-! ### A reciprocal from the forward run -/

/-- Under the extended target the marked lane carries positive weight, so
reweighting it by `1/Ẑ · Ẑ` changes nothing. -/
theorem extended_withDensity_unit {ι : Type} (lanes : Lanes ι)
    (population : Measure (populationSpace ι space)) :
    (extended lanes population).withDensity (fun marked =>
        ENNReal.mul (inverseMeanWeight lanes marked) (ENNReal.finite (meanWeight lanes marked.1))) =
      extended lanes population := by
  have unitMeasurable : ENNRealMeasurable (markedSpace ι space) (fun marked =>
      ENNReal.mul (inverseMeanWeight lanes marked) (ENNReal.finite (meanWeight lanes marked.1))) :=
    ENNRealMeasurable.mul (inverseMeanWeight_measurable lanes space)
      (finite_weight_measurable (MeasurableMap.comp (meanWeight_measurable lanes space)
        (Space.first_measurable (populationSpace ι space) (Space.discrete ι))))
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  rw [lintegral_withDensity _ unitMeasurable measurable, extended,
    Measure.lintegral_bind _ _ (ENNRealMeasurable.mul unitMeasurable measurable),
    Measure.lintegral_bind _ _ measurable]
  refine lintegral_congr _ fun draws => ?_
  rw [lintegral_markedLane lanes draws (ENNRealMeasurable.mul unitMeasurable measurable),
    lintegral_markedLane lanes draws measurable]
  refine congrArg (ENNReal.mul _)
    (congrArg ENNReal.additiveLaws.listSum (List.map_congr_left fun lane _ => ?_))
  show ENNReal.mul (drawWeight (draws lane))
      (ENNReal.mul (ENNReal.mul (ENNReal.finite (NNReal.div NNReal.one (meanWeight lanes draws)))
        (ENNReal.finite (meanWeight lanes draws))) (function (draws, lane))) =
    ENNReal.mul (drawWeight (draws lane)) (function (draws, lane))
  by_cases zero : totalWeight lanes draws = NNReal.zero
  · rw [drawWeight, weight_eq_zero zero lane]
    exact (ENNReal.zero_mul _).trans (ENNReal.zero_mul _).symm
  · rw [ENNReal.finite_mul_finite, NNReal.div_mul_cancel _ (meanWeight_ne_zero lanes zero)]
    exact congrArg (ENNReal.mul _) (ENNReal.one_mul _)

/-- Where the target's density is positive, the selected density is positive
at almost every point of the reference. The points where the conditional run's
expected inverse mean weight vanishes are null for the selected law, so they
are null for the extended target reweighted by `1/Ẑ`, so for the extended
target itself, so for the target, and so for the reference where the target's
density is positive. -/
theorem selected_support {ι : Type} {lanes : Lanes ι}
    {population : Measure (populationSpace ι space)} {target base : Measure space}
    {conditional : Kernel space (markedSpace ι space)}
    (law : ConditionalLaw lanes population target conditional)
    (markov : ∀ point, Measure.IsProbability (conditional point)) {density : α → ENNReal}
    (measurable : ENNRealMeasurable space density)
    (isDensity : Measure.IsDensity target base density) :
    base.restrict (fun point => density point ≠ ENNReal.zero) =
      base.restrict (fun point =>
        selectedDensity lanes conditional density point ≠ ENNReal.zero) := by
  have inverseMeasurable := inverseMeanWeight_measurable lanes space
  have massMeasurable : ENNRealMeasurable space
      (fun point => lintegral (conditional point) (inverseMeanWeight lanes)) :=
    Kernel.lintegral_measurable conditional inverseMeasurable
  let lost : Set α := Set.inter (fun point => density point ≠ ENNReal.zero)
    (fun point => lintegral (conditional point) (inverseMeanWeight lanes) = ENNReal.zero)
  have lostMeasurable : space.Measurable lost :=
    space.inter (space.complement (measurable.eq_set (ENNRealMeasurable.constant space _)))
      (massMeasurable.eq_set (ENNRealMeasurable.constant space _))
  have positiveNull : selectedPositive lanes population lost = ENNReal.zero := by
    have empty : Set.inter lost
        (fun point => selectedDensity lanes conditional density point ≠ ENNReal.zero) =
        Set.empty :=
      Set.ext fun point => ⟨fun member => (member.2 (by
        rw [selectedDensity, member.1.2]
        exact ENNReal.mul_zero _)).elim, fun member => member.elim⟩
    rw [(selected_density law measurable isDensity).eq_withDensity]
    refine (Measure.withDensity_apply_eq_zero_iff
      (selectedDensity_measurable lanes conditional measurable) lostMeasurable).mpr ?_
    rw [empty]
    exact base.empty_apply
  have reweightedNull : ((extended lanes population).withDensity (inverseMeanWeight lanes))
      (Set.preimage reference lost) = ENNReal.zero := by
    rw [← Measure.map_apply _ _ (reference_measurable lanes space) lostMeasurable,
      ← selectedPositive_eq_extended]
    exact positiveNull
  have targetNull : target lost = ENNReal.zero := by
    rw [← conditional_reference law markov, Measure.map_apply _ _ _ lostMeasurable,
      ← extended_withDensity_unit lanes population,
      ← Measure.withDensity_withDensity _ inverseMeasurable
        (finite_weight_measurable (MeasurableMap.comp (meanWeight_measurable lanes space)
          (Space.first_measurable (populationSpace ι space) (Space.discrete ι))))]
    exact Measure.NullSet.withDensity reweightedNull _
  have referenceNull : base lost = ENNReal.zero := by
    rw [isDensity.eq_withDensity] at targetNull
    have charged := (Measure.withDensity_apply_eq_zero_iff measurable lostMeasurable).mp targetNull
    have same : Set.inter lost (fun point => density point ≠ ENNReal.zero) = lost :=
      Set.ext fun point => ⟨fun member => member.1, fun member => ⟨member, member.1⟩⟩
    rw [same] at charged
    exact charged
  refine Measure.restrict_congr_ae (Measure.NullSet.mono referenceNull ?_)
  intro point disagree
  by_cases vanishes : density point = ENNReal.zero
  · refine (disagree ?_).elim
    have selectedVanishes : selectedDensity lanes conditional density point = ENNReal.zero := by
      rw [selectedDensity, vanishes]
      exact ENNReal.zero_mul _
    exact propext ⟨fun nonzero => (nonzero vanishes).elim,
      fun nonzero => (nonzero selectedVanishes).elim⟩
  · by_cases mass : lintegral (conditional point) (inverseMeanWeight lanes) = ENNReal.zero
    · exact ⟨vanishes, mass⟩
    · refine (disagree ?_).elim
      have selectedPositive : selectedDensity lanes conditional density point ≠ ENNReal.zero :=
        fun zero => (ENNReal.mul_eq_zero_iff.mp zero).elim vanishes mass
      exact propext ⟨fun _ => selectedPositive, fun _ => vanishes⟩

/-- A forward run's selected lane, weighted by `Ẑ/γ(x)`, is properly weighted
for the reference restricted to where the selected density is positive. The
selected value with `Ẑ` is properly weighted for the target
(`selected_properlyWeighted`), dividing by `γ` restricts the reference to
`{γ ≠ 0}` (`properlyWeighted_weighted_reciprocal`), and that set is the selected
density's support up to a null set (`selected_support`). Positivity of the total
weight is not needed here. -/
theorem selected_reciprocal_properlyWeighted {ι : Type} {lanes : Lanes ι}
    {population : Measure (populationSpace ι space)} {target base : Measure space}
    {conditional : Kernel space (markedSpace ι space)}
    (law : ConditionalLaw lanes population target conditional)
    (markov : ∀ point, Measure.IsProbability (conditional point))
    (probability : Measure.IsProbability population)
    (fallback : Kernel (populationSpace ι space) (Space.discrete ι))
    (fallbackMarkov : ∀ draws, Measure.IsProbability (fallback draws))
    {density : α → NNReal} (measurable : MeasurableMap space weightSpace density)
    (isDensity : Measure.IsDensity target base fun point => ENNReal.finite (density point)) :
    ProperlyWeighted (base.restrict fun point =>
        selectedDensity lanes conditional (fun point => ENNReal.finite (density point)) point ≠
          ENNReal.zero)
      ((population.bind (selection lanes space fallback fallbackMarkov)).map
        (fun draw => (draw.1, NNReal.mul draw.2 (NNReal.div NNReal.one (density draw.1))))
        (density_weight_measurable (weight_inverse_measurable measurable))) := by
  have properlyWeighted := properlyWeighted_weighted_reciprocal measurable isDensity
    (selected_properlyWeighted (empirical_invariant_of_conditional law markov probability)
      fallback fallbackMarkov)
  have support : (fun point => ENNReal.finite (density point) ≠ ENNReal.zero) =
      fun point => density point ≠ NNReal.zero :=
    funext fun point => propext ⟨fun nonzero zero => nonzero (congrArg ENNReal.finite zero),
      fun nonzero zero => nonzero (ENNReal.finite_injective zero)⟩
  rw [← selected_support law markov (finite_weight_measurable measurable) isDensity, support]
  exact properlyWeighted

end

end Problib.Inference
