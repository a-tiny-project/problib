module

public import Problib.Measure.Kernel.Product
public import Problib.Measure.Normalization
public import Problib.Real.Series.Ratio
public import Problib.Measure.Additive.Counting
public import Problib.Measure.Kernel.Precomp
import Problib.Measure.Extended.Ratio
import Problib.Measure.Kernel.Measurable
import Problib.Measure.Integral.Density.Algebra
import Problib.Measure.Integral.Density.AlmostEverywhere
import Problib.Measure.Integral.Lebesgue.Zero
import Problib.Measure.Integral.Lebesgue.Transport

set_option autoImplicit false

/-! # Conditional kernels of joint densities

A joint density on `alpha × beta`, read against an s-finite reference measure on
`beta`, has an explicit conditional kernel. At each input, the fiber of the
density is divided by its mass when that mass is finite and nonzero, and every
other input receives a fallback Dirac measure. The kernel is defined at every
input and needs no standard Borel presentation.

A density that factors as `h(x)·g(S(x), θ)` with `h(x)` finite and nonzero has
the conditional of `g` at `S(x)` (`densityConditional_statistic`), the
Fisher–Neyman direction of sufficiency. A zero or infinite `h(x)` sends the
fiber to the fallback instead (`zero_scale_does_not_factor`,
`top_scale_does_not_factor`). -/

namespace Problib.Measure.Kernel

open Problib.Real

universe u v w

variable {alpha : Type u} {beta : Type v} {source : Space alpha} {target : Space beta}

/-- The fiber of a joint density at one input, read against the reference
measure. -/
@[expose] public noncomputable def densityFiber (reference : Measure target)
    (density : alpha → beta → ENNReal) (input : alpha) : Measure target :=
  reference.withDensity (density input)

/-- The total mass of the fiber of a joint density at one input. -/
@[expose] public noncomputable def densityMass (reference : Measure target)
    (density : alpha → beta → ENNReal) (input : alpha) : ENNReal :=
  lintegral reference (density input)

/-- The joint density divided by the mass of its fiber. -/
@[expose] public noncomputable def normalizedDensity (reference : Measure target)
    (density : alpha → beta → ENNReal) (input : alpha) (output : beta) : ENNReal :=
  ENNReal.densityRatio (density input output) (densityMass reference density input)

/-- A fiber's total mass is the integral of its density. -/
public theorem densityFiber_univ (reference : Measure target)
    (density : alpha → beta → ENNReal) (input : alpha) :
    densityFiber reference density input Set.univ =
      densityMass reference density input := by
  unfold densityFiber densityMass
  rw [reference.withDensity_apply (density input) target.univ, reference.restrict_univ]

/-- A fiber is normalizable exactly when its mass is finite and nonzero. -/
public theorem isNormalizable_densityFiber_iff (reference : Measure target)
    (density : alpha → beta → ENNReal) (input : alpha) :
    Measure.IsNormalizable (densityFiber reference density input) ↔
      ENNReal.Finite (densityMass reference density input) ∧
        densityMass reference density input ≠ ENNReal.zero := by
  rw [← densityFiber_univ]
  exact ⟨fun defined => ⟨defined.finite.univ_finite, defined.nonzero⟩,
    fun bounds => ⟨⟨bounds.1⟩, bounds.2⟩⟩

/-- The fiber mass is measurable in the input when the joint density is. -/
public theorem densityMass_measurable {reference : Measure target}
    (referenceFinite : Measure.SFinite reference) {density : alpha → beta → ENNReal}
    (densityMeasurable : ENNRealMeasurable (Space.product source target)
      (fun pair => density pair.1 pair.2)) :
    ENNRealMeasurable source (densityMass reference density) :=
  lintegral_measurable_joint (Kernel.const source reference)
    (IsSFinite.const source referenceFinite) densityMeasurable

/-- The normalized density is jointly measurable when the joint density is. -/
public theorem normalizedDensity_measurable {reference : Measure target}
    (referenceFinite : Measure.SFinite reference) {density : alpha → beta → ENNReal}
    (densityMeasurable : ENNRealMeasurable (Space.product source target)
      (fun pair => density pair.1 pair.2)) :
    ENNRealMeasurable (Space.product source target)
      (fun pair => normalizedDensity reference density pair.1 pair.2) :=
  ENNRealMeasurable.densityRatio densityMeasurable
    ((densityMass_measurable referenceFinite densityMeasurable).comp
      (Space.first_measurable source target))

/-- The inputs with a normalizable fiber form a measurable set. -/
public theorem normalizableFiber_measurable {reference : Measure target}
    (referenceFinite : Measure.SFinite reference) {density : alpha → beta → ENNReal}
    (densityMeasurable : ENNRealMeasurable (Space.product source target)
      (fun pair => density pair.1 pair.2)) :
    source.Measurable
      (fun input => Measure.IsNormalizable (densityFiber reference density input)) := by
  have massMeasurable := densityMass_measurable referenceFinite densityMeasurable
  have infinite := massMeasurable.eq_set (ENNRealMeasurable.constant source ENNReal.top)
  have null := massMeasurable.eq_set (ENNRealMeasurable.constant source ENNReal.zero)
  have region : (fun input => Measure.IsNormalizable (densityFiber reference density input)) =
      Set.inter
        (Set.complement (fun input => densityMass reference density input = ENNReal.top))
        (Set.complement (fun input => densityMass reference density input = ENNReal.zero)) := by
    funext input
    apply propext
    rw [isNormalizable_densityFiber_iff, ENNReal.finite_iff_ne_top]
    exact Iff.rfl
  rw [region]
  exact source.inter (source.complement infinite) (source.complement null)

/-- A finite nonzero mass times the density ratio against that mass recovers the
numerator. -/
private theorem mul_densityRatio_of_finite {mass : ENNReal} (finite : ENNReal.Finite mass)
    (nonzero : mass ≠ ENNReal.zero) (value : ENNReal) :
    ENNReal.mul mass (ENNReal.densityRatio value mass) = value := by
  rcases ENNReal.exists_finite_of_finite finite with ⟨weight, rfl⟩
  have weightNonzero : weight ≠ NNReal.zero :=
    fun equal => nonzero (congrArg ENNReal.finite equal)
  have cancel : ENNReal.mul (ENNReal.finite weight)
      (ENNReal.finite (NNReal.div NNReal.one weight)) = ENNReal.one :=
    congrArg ENNReal.finite (NNReal.mul_div_cancel NNReal.one weightNonzero)
  have split : ENNReal.mul (ENNReal.finite weight)
      (ENNReal.mul (ENNReal.finite (NNReal.div NNReal.one weight)) value) = value := by
    rw [← ENNReal.mul_assoc, cancel, ENNReal.one_mul]
  calc
    ENNReal.mul (ENNReal.finite weight) (ENNReal.densityRatio value (ENNReal.finite weight)) =
        ENNReal.mul (ENNReal.finite weight) (ENNReal.densityRatio
          (ENNReal.mul (ENNReal.finite weight)
            (ENNReal.mul (ENNReal.finite (NNReal.div NNReal.one weight)) value))
          (ENNReal.finite weight)) := by
      rw [split]
    _ = ENNReal.mul (ENNReal.finite weight)
          (ENNReal.mul (ENNReal.finite (NNReal.div NNReal.one weight)) value) := by
      rw [ENNReal.densityRatio_mul_of_finite finite nonzero]
    _ = value := split

/-- The conditional kernel of a joint density. A fiber of finite, nonzero mass
is normalized. Every other input receives the Dirac measure at `fallback`. -/
@[expose] public noncomputable def densityConditional (reference : Measure target)
    (referenceFinite : Measure.SFinite reference) (density : alpha → beta → ENNReal)
    (densityMeasurable : ENNRealMeasurable (Space.product source target)
      (fun pair => density pair.1 pair.2))
    (fallback : beta) : Kernel source target :=
  piecewise (fun input => Measure.IsNormalizable (densityFiber reference density input))
    (normalizableFiber_measurable referenceFinite densityMeasurable)
    ((Kernel.const source reference).withDensity (IsSFinite.const source referenceFinite)
      (normalizedDensity reference density)
      (normalizedDensity_measurable referenceFinite densityMeasurable))
    (Kernel.const source (Measure.dirac target fallback))

/-- On a normalizable fiber, the conditional kernel is the normalized fiber. -/
public theorem densityConditional_eq_normalize (reference : Measure target)
    (referenceFinite : Measure.SFinite reference) {density : alpha → beta → ENNReal}
    (densityMeasurable : ENNRealMeasurable (Space.product source target)
      (fun pair => density pair.1 pair.2))
    (fallback : beta) (input : alpha)
    (defined : Measure.IsNormalizable (densityFiber reference density input)) :
    densityConditional reference referenceFinite density densityMeasurable fallback input =
      Measure.normalize (densityFiber reference density input) defined := by
  unfold densityConditional
  rw [piecewise_apply_of_mem _ _ _ _ input defined, withDensity_apply, Kernel.const_apply]
  symm
  apply Measure.normalize_eq_of_smul_eq
  obtain ⟨finite, nonzero⟩ :=
    (isNormalizable_densityFiber_iff reference density input).mp defined
  have ratioMeasurable : ENNRealMeasurable target (normalizedDensity reference density input) :=
    jointly_measurable_slice (normalizedDensity_measurable referenceFinite densityMeasurable) input
  rw [densityFiber_univ,
    ← (reference.withDensity (normalizedDensity reference density input)).withDensity_const,
    Measure.withDensity_withDensity reference ratioMeasurable
      (ENNRealMeasurable.constant target _)]
  unfold densityFiber
  congr 1
  funext output
  rw [ENNReal.mul_comm]
  exact mul_densityRatio_of_finite finite nonzero (density input output)

/-- Off the normalizable fibers, the conditional kernel is the fallback Dirac
measure. -/
public theorem densityConditional_eq_dirac (reference : Measure target)
    (referenceFinite : Measure.SFinite reference) {density : alpha → beta → ENNReal}
    (densityMeasurable : ENNRealMeasurable (Space.product source target)
      (fun pair => density pair.1 pair.2))
    (fallback : beta) (input : alpha)
    (undefined : ¬Measure.IsNormalizable (densityFiber reference density input)) :
    densityConditional reference referenceFinite density densityMeasurable fallback input =
      Measure.dirac target fallback := by
  unfold densityConditional
  rw [piecewise_apply_of_not_mem _ _ _ _ input undefined, Kernel.const_apply]

/-- Every fiber of the conditional kernel is a probability measure. -/
public theorem densityConditional_isProbability (reference : Measure target)
    (referenceFinite : Measure.SFinite reference) {density : alpha → beta → ENNReal}
    (densityMeasurable : ENNRealMeasurable (Space.product source target)
      (fun pair => density pair.1 pair.2))
    (fallback : beta) (input : alpha) :
    Measure.IsProbability
      (densityConditional reference referenceFinite density densityMeasurable fallback input) := by
  classical
  by_cases defined : Measure.IsNormalizable (densityFiber reference density input)
  · rw [densityConditional_eq_normalize reference referenceFinite densityMeasurable fallback
      input defined]
    exact Measure.normalize_isProbability _ defined
  · rw [densityConditional_eq_dirac reference referenceFinite densityMeasurable fallback
      input defined]
    exact Measure.IsProbability.dirac target fallback

/-- The conditional kernel is uniformly finite with bound one. -/
public theorem densityConditional_isFinite (reference : Measure target)
    (referenceFinite : Measure.SFinite reference) {density : alpha → beta → ENNReal}
    (densityMeasurable : ENNRealMeasurable (Space.product source target)
      (fun pair => density pair.1 pair.2))
    (fallback : beta) :
    IsFinite (densityConditional reference referenceFinite density densityMeasurable fallback) := by
  refine ⟨⟨ENNReal.one, True.intro, ?_⟩⟩
  intro input
  rw [(densityConditional_isProbability reference referenceFinite densityMeasurable fallback
    input).univ_eq_one]
  exact ENNReal.le_refl _

/-- Two joint densities, possibly over different input spaces, have the same
conditional law at two inputs whose fibers agree. -/
public theorem densityConditional_eq_of_fiber (reference : Measure target)
    (referenceFinite : Measure.SFinite reference) {gamma : Type w} {other : Space gamma}
    {density : alpha → beta → ENNReal} {otherDensity : gamma → beta → ENNReal}
    (densityMeasurable : ENNRealMeasurable (Space.product source target)
      (fun pair => density pair.1 pair.2))
    (otherMeasurable : ENNRealMeasurable (Space.product other target)
      (fun pair => otherDensity pair.1 pair.2))
    (fallback : beta) {input : alpha} {otherInput : gamma}
    (same : density input = otherDensity otherInput) :
    densityConditional reference referenceFinite density densityMeasurable fallback input =
      densityConditional reference referenceFinite otherDensity otherMeasurable fallback
        otherInput := by
  classical
  have fiber : densityFiber reference density input =
      densityFiber reference otherDensity otherInput := by
    unfold densityFiber
    rw [same]
  by_cases defined : Measure.IsNormalizable (densityFiber reference density input)
  · rw [densityConditional_eq_normalize reference referenceFinite densityMeasurable fallback
        input defined,
      densityConditional_eq_normalize reference referenceFinite otherMeasurable fallback
        otherInput (fiber ▸ defined)]
    exact Measure.normalize_congr fiber _ _
  · rw [densityConditional_eq_dirac reference referenceFinite densityMeasurable fallback
        input defined,
      densityConditional_eq_dirac reference referenceFinite otherMeasurable fallback
        otherInput (fun otherDefined => defined (fiber ▸ otherDefined))]

/-- The conditional kernel reads an input only through its fiber of the density. -/
public theorem densityConditional_congr_fiber (reference : Measure target)
    (referenceFinite : Measure.SFinite reference) {density : alpha → beta → ENNReal}
    (densityMeasurable : ENNRealMeasurable (Space.product source target)
      (fun pair => density pair.1 pair.2))
    (fallback : beta) {first second : alpha} (same : density first = density second) :
    densityConditional reference referenceFinite density densityMeasurable fallback first =
      densityConditional reference referenceFinite density densityMeasurable fallback second :=
  densityConditional_eq_of_fiber reference referenceFinite densityMeasurable densityMeasurable
    fallback same

/-- A fiber of finite mass is its mass times the conditional kernel. A null
fiber is the zero measure, whatever the fallback. -/
public theorem densityFiber_eq_smul (reference : Measure target)
    (referenceFinite : Measure.SFinite reference) {density : alpha → beta → ENNReal}
    (densityMeasurable : ENNRealMeasurable (Space.product source target)
      (fun pair => density pair.1 pair.2))
    (fallback : beta) (input : alpha)
    (finite : ENNReal.Finite (densityMass reference density input)) :
    densityFiber reference density input =
      Measure.smul (densityMass reference density input)
        (densityConditional reference referenceFinite density densityMeasurable fallback
          input) := by
  classical
  by_cases null : densityMass reference density input = ENNReal.zero
  · rw [null, Measure.zero_smul]
    unfold densityFiber
    rw [Measure.withDensity_congr_ae
      (ae_zero_of_lintegral_eq_zero (jointly_measurable_slice densityMeasurable input) null),
      Measure.withDensity_zero]
  · have defined : Measure.IsNormalizable (densityFiber reference density input) :=
      (isNormalizable_densityFiber_iff reference density input).mpr ⟨finite, null⟩
    rw [densityConditional_eq_normalize reference referenceFinite densityMeasurable fallback
      input defined, ← densityFiber_univ]
    exact (Measure.smul_normalize _ defined).symm

/-- A density between `lower > 0` and `upper` against a probability reference
has a conditional kernel that keeps `lower / upper` of the reference at every
input. -/
public theorem densityConditional_lower (reference : Measure target)
    (referenceFinite : Measure.SFinite reference)
    (referenceProbability : Measure.IsProbability reference) {density : alpha → beta → ENNReal}
    (densityMeasurable : ENNRealMeasurable (Space.product source target)
      (fun pair => density pair.1 pair.2))
    (fallback : beta) {lower upper : NNReal} (lowerPositive : NNReal.lt NNReal.zero lower)
    (bounded : ∀ input output, ENNReal.le (ENNReal.finite lower) (density input output) ∧
      ENNReal.le (density input output) (ENNReal.finite upper))
    (input : alpha) {set : Set beta} (setMeasurable : target.Measurable set) :
    ENNReal.le (ENNReal.mul (ENNReal.finite (NNReal.div lower upper)) (reference set))
      (densityConditional reference referenceFinite density densityMeasurable fallback input
        set) := by
  obtain ⟨output⟩ := referenceProbability.nonempty
  have lowerUpper : NNReal.le lower upper :=
    ENNReal.le_trans (bounded input output).1 (bounded input output).2
  have upperNonzero : upper ≠ NNReal.zero :=
    (NNReal.zero_lt_iff_ne_zero upper).mp (NNReal.lt_of_lt_of_le lowerPositive lowerUpper)
  have upperPositive : ENNReal.lt ENNReal.zero (ENNReal.finite upper) :=
    ENNReal.zero_lt_iff_ne_zero.mpr (fun equal => upperNonzero (ENNReal.finite_injective equal))
  have fiberLower : ENNReal.le (ENNReal.mul (ENNReal.finite lower) (reference set))
      (densityFiber reference density input set) := by
    unfold densityFiber
    rw [Measure.withDensity_apply _ _ setMeasurable, ← Measure.restrict_apply_univ reference set,
      ← lintegral_const]
    exact lintegral_mono _ (fun output => (bounded input output).1)
  have massUpper : ENNReal.le (densityMass reference density input) (ENNReal.finite upper) := by
    have constant := lintegral_const reference (ENNReal.finite upper)
    rw [referenceProbability.univ_eq_one, ENNReal.mul_one] at constant
    unfold densityMass
    rw [← constant]
    exact lintegral_mono _ (fun output => (bounded input output).2)
  have scaled : densityFiber reference density input set =
      ENNReal.mul (densityMass reference density input)
        (densityConditional reference referenceFinite density densityMeasurable fallback input
          set) := by
    rw [← Measure.smul_apply_measurable _ _ setMeasurable,
      ← densityFiber_eq_smul reference referenceFinite densityMeasurable fallback input
        (ENNReal.finite_of_le massUpper True.intro)]
  have upperBound : ENNReal.le (densityFiber reference density input set)
      (ENNReal.mul (ENNReal.finite upper)
        (densityConditional reference referenceFinite density densityMeasurable fallback input
          set)) := by
    rw [scaled]
    exact ENNReal.mul_le_mul_right massUpper _
  apply (ENNReal.mul_le_mul_left_iff (factor := ENNReal.finite upper) True.intro
    upperPositive).mp
  rw [← ENNReal.mul_assoc, ENNReal.finite_mul_finite, NNReal.mul_div_cancel lower upperNonzero]
  exact ENNReal.le_trans fiberLower upperBound

/-- A density on the kernel of a semiproduct is a density on the product. -/
private theorem semiproduct_withDensity_right (base : Measure source)
    (kernel : Kernel source target) (kernelFinite : IsSFinite kernel)
    {density : alpha → beta → ENNReal}
    (densityMeasurable : ENNRealMeasurable (Space.product source target)
      (fun pair => density pair.1 pair.2)) :
    base.semiproduct (kernel.withDensity kernelFinite density densityMeasurable)
        (IsSFinite.withDensity kernelFinite density densityMeasurable) =
      (base.semiproduct kernel kernelFinite).withDensity
        (fun pair => density pair.1 pair.2) := by
  have step := Measure.semiproduct_withDensity base kernel kernelFinite
    (ENNRealMeasurable.constant source ENNReal.one) densityMeasurable
  rw [Measure.withDensity_one] at step
  rw [step]
  congr 1
  funext pair
  exact ENNReal.one_mul _

/-- The base measure weighted by fiber mass, followed by the conditional kernel,
is the joint density when fiber masses are finite almost everywhere. -/
public theorem semiproduct_densityConditional (base : Measure source)
    (reference : Measure target) (referenceFinite : Measure.SFinite reference)
    {density : alpha → beta → ENNReal}
    (densityMeasurable : ENNRealMeasurable (Space.product source target)
      (fun pair => density pair.1 pair.2))
    (fallback : beta)
    (finite : base.AE (fun input => ENNReal.Finite (densityMass reference density input))) :
    (base.withDensity (densityMass reference density)).semiproduct
        (densityConditional reference referenceFinite density densityMeasurable fallback)
        (densityConditional_isFinite reference referenceFinite densityMeasurable
          fallback).toSFinite =
      (Measure.prod base reference referenceFinite).withDensity
        (fun pair => density pair.1 pair.2) := by
  have massMeasurable := densityMass_measurable referenceFinite densityMeasurable
  have firstMassMeasurable : ENNRealMeasurable (Space.product source target)
      (fun pair => (fun input (_ : beta) => densityMass reference density input)
        pair.1 pair.2) :=
    massMeasurable.comp (Space.first_measurable source target)
  have conditionalFinite := (densityConditional_isFinite reference referenceFinite
    densityMeasurable fallback).toSFinite
  calc
    (base.withDensity (densityMass reference density)).semiproduct
        (densityConditional reference referenceFinite density densityMeasurable fallback)
        conditionalFinite =
      (base.semiproduct
        (densityConditional reference referenceFinite density densityMeasurable fallback)
        conditionalFinite).withDensity
        (fun pair => densityMass reference density pair.1) :=
      Measure.semiproduct_withDensity_left base massMeasurable _ conditionalFinite
    _ = base.semiproduct
        ((densityConditional reference referenceFinite density densityMeasurable
          fallback).withDensity conditionalFinite
          (fun input _ => densityMass reference density input) firstMassMeasurable)
        (IsSFinite.withDensity conditionalFinite _ firstMassMeasurable) :=
      (semiproduct_withDensity_right base _ conditionalFinite
        (density := fun input _ => densityMass reference density input)
        firstMassMeasurable).symm
    _ = base.semiproduct
        ((Kernel.const source reference).withDensity (IsSFinite.const source referenceFinite)
          density densityMeasurable)
        (IsSFinite.withDensity (IsSFinite.const source referenceFinite) density
          densityMeasurable) := by
      apply Measure.semiproduct_congr_ae
      apply finite.mono
      intro input inputFinite
      change (densityConditional reference referenceFinite density densityMeasurable
          fallback input).withDensity (fun _ => densityMass reference density input) =
        (Kernel.const source reference input).withDensity (density input)
      rw [Measure.withDensity_const, Kernel.const_apply]
      exact (densityFiber_eq_smul reference referenceFinite densityMeasurable fallback
        input inputFinite).symm
    _ = (Measure.prod base reference referenceFinite).withDensity
        (fun pair => density pair.1 pair.2) :=
      semiproduct_withDensity_right base _ _ densityMeasurable

/-- Scaling one fiber by a positive finite weight leaves the conditional kernel
unchanged at that input. -/
public theorem densityConditional_mul_left (reference : Measure target)
    (referenceFinite : Measure.SFinite reference) {density : alpha → beta → ENNReal}
    (densityMeasurable : ENNRealMeasurable (Space.product source target)
      (fun pair => density pair.1 pair.2))
    {weight : alpha → ENNReal}
    (weightedMeasurable : ENNRealMeasurable (Space.product source target)
      (fun pair => ENNReal.mul (weight pair.1) (density pair.1 pair.2)))
    (fallback : beta) (input : alpha)
    (weightFinite : ENNReal.Finite (weight input)) (weightNonzero : weight input ≠ ENNReal.zero) :
    densityConditional reference referenceFinite
        (fun input output => ENNReal.mul (weight input) (density input output))
        weightedMeasurable fallback input =
      densityConditional reference referenceFinite density densityMeasurable fallback input := by
  have scaled : densityFiber reference
        (fun input output => ENNReal.mul (weight input) (density input output)) input =
      Measure.smul (weight input) (densityFiber reference density input) := by
    unfold densityFiber
    rw [← (reference.withDensity (density input)).withDensity_const,
      Measure.withDensity_withDensity reference (jointly_measurable_slice densityMeasurable input)
        (ENNRealMeasurable.constant target _)]
    congr 1
    funext output
    exact ENNReal.mul_comm _ _
  have total : Measure.smul (weight input) (densityFiber reference density input) Set.univ =
      ENNReal.mul (weight input) (densityFiber reference density input Set.univ) :=
    Measure.smul_apply_measurable _ _ target.univ
  have equivalent : Measure.IsNormalizable (densityFiber reference
        (fun input output => ENNReal.mul (weight input) (density input output)) input) ↔
      Measure.IsNormalizable (densityFiber reference density input) := by
    rw [scaled]
    constructor
    · intro defined
      refine ⟨⟨?_⟩, ?_⟩
      · have bounded := defined.finite.univ_finite
        rw [total, ENNReal.finite_iff_ne_top] at bounded
        rw [ENNReal.finite_iff_ne_top]
        intro infinite
        rw [infinite, ENNReal.mul_top_of_ne_zero weightNonzero] at bounded
        exact bounded rfl
      · intro null
        apply defined.nonzero
        rw [total, null, ENNReal.mul_zero]
    · intro defined
      refine ⟨⟨?_⟩, ?_⟩
      · rw [total]
        exact ENNReal.mul_finite weightFinite defined.finite.univ_finite
      · rw [total]
        intro null
        rcases ENNReal.mul_eq_zero_iff.mp null with weightZero | fiberZero
        · exact weightNonzero weightZero
        · exact defined.nonzero fiberZero
  classical
  by_cases defined : Measure.IsNormalizable (densityFiber reference density input)
  · have weightedDefined := equivalent.mpr defined
    rw [densityConditional_eq_normalize reference referenceFinite weightedMeasurable fallback
        input weightedDefined,
      densityConditional_eq_normalize reference referenceFinite densityMeasurable fallback
        input defined]
    apply Measure.normalize_eq_of_smul_eq
    rw [scaled, total, ← Measure.smul_smul, Measure.smul_normalize]
  · rw [densityConditional_eq_dirac reference referenceFinite weightedMeasurable fallback
        input (fun weightedDefined => defined (equivalent.mp weightedDefined)),
      densityConditional_eq_dirac reference referenceFinite densityMeasurable fallback
        input defined]

/-! ### Sufficient statistics -/

/-- The Fisher–Neyman factorization, pointwise. Where the fiber of a density at
an input is a finite nonzero multiple of the fiber of a second density at a
statistic value, the two conditional kernels agree there. No map to the
statistic appears, so none needs to be measurable. -/
public theorem densityConditional_factor (reference : Measure target)
    (referenceFinite : Measure.SFinite reference) {gamma : Type w} {statistics : Space gamma}
    {density : alpha → beta → ENNReal} {factor : gamma → beta → ENNReal}
    (densityMeasurable : ENNRealMeasurable (Space.product source target)
      (fun pair => density pair.1 pair.2))
    (factorMeasurable : ENNRealMeasurable (Space.product statistics target)
      (fun pair => factor pair.1 pair.2))
    (fallback : beta) {input : alpha} {statistic : gamma} {scale : ENNReal}
    (scaleFinite : ENNReal.Finite scale) (scaleNonzero : scale ≠ ENNReal.zero)
    (factored : density input = fun output => ENNReal.mul scale (factor statistic output)) :
    densityConditional reference referenceFinite density densityMeasurable fallback input =
      densityConditional reference referenceFinite factor factorMeasurable fallback statistic := by
  have scaledMeasurable : ENNRealMeasurable (Space.product statistics target)
      (fun pair => ENNReal.mul ((fun _ : gamma => scale) pair.1) (factor pair.1 pair.2)) :=
    (ENNRealMeasurable.constant _ scale).mul factorMeasurable
  calc densityConditional reference referenceFinite density densityMeasurable fallback input
      = densityConditional reference referenceFinite
          (fun value output => ENNReal.mul ((fun _ : gamma => scale) value) (factor value output))
          scaledMeasurable fallback statistic :=
        densityConditional_eq_of_fiber reference referenceFinite densityMeasurable
          scaledMeasurable fallback factored
    _ = densityConditional reference referenceFinite factor factorMeasurable fallback statistic :=
        densityConditional_mul_left reference referenceFinite factorMeasurable scaledMeasurable
          fallback statistic scaleFinite scaleNonzero

/-- The Fisher–Neyman factorization through a statistic. If a density factors
as `h(x)·g(S(x), θ)` at every input, its conditional at an input with `h(x)`
finite and nonzero is the conditional of `g` at `S(x)`. -/
public theorem densityConditional_statistic (reference : Measure target)
    (referenceFinite : Measure.SFinite reference) {gamma : Type w} {statistics : Space gamma}
    {density : alpha → beta → ENNReal} {factor : gamma → beta → ENNReal}
    (densityMeasurable : ENNRealMeasurable (Space.product source target)
      (fun pair => density pair.1 pair.2))
    (factorMeasurable : ENNRealMeasurable (Space.product statistics target)
      (fun pair => factor pair.1 pair.2))
    (fallback : beta) {statistic : alpha → gamma} {scale : alpha → ENNReal}
    (factored : ∀ input output,
      density input output = ENNReal.mul (scale input) (factor (statistic input) output))
    (input : alpha) (scaleFinite : ENNReal.Finite (scale input))
    (scaleNonzero : scale input ≠ ENNReal.zero) :
    densityConditional reference referenceFinite density densityMeasurable fallback input =
      densityConditional reference referenceFinite factor factorMeasurable fallback
        (statistic input) :=
  densityConditional_factor reference referenceFinite densityMeasurable factorMeasurable fallback
    scaleFinite scaleNonzero (funext (factored input))

/-- Inputs with equal statistics and admissible scales have equal conditionals. -/
public theorem densityConditional_statistic_congr (reference : Measure target)
    (referenceFinite : Measure.SFinite reference) {gamma : Type w} {statistics : Space gamma}
    {density : alpha → beta → ENNReal} {factor : gamma → beta → ENNReal}
    (densityMeasurable : ENNRealMeasurable (Space.product source target)
      (fun pair => density pair.1 pair.2))
    (factorMeasurable : ENNRealMeasurable (Space.product statistics target)
      (fun pair => factor pair.1 pair.2))
    (fallback : beta) {statistic : alpha → gamma} {scale : alpha → ENNReal}
    (factored : ∀ input output,
      density input output = ENNReal.mul (scale input) (factor (statistic input) output))
    {first second : alpha} (same : statistic first = statistic second)
    (firstFinite : ENNReal.Finite (scale first)) (firstNonzero : scale first ≠ ENNReal.zero)
    (secondFinite : ENNReal.Finite (scale second)) (secondNonzero : scale second ≠ ENNReal.zero) :
    densityConditional reference referenceFinite density densityMeasurable fallback first =
      densityConditional reference referenceFinite density densityMeasurable fallback second := by
  rw [densityConditional_statistic reference referenceFinite densityMeasurable factorMeasurable
      fallback factored first firstFinite firstNonzero,
    densityConditional_statistic reference referenceFinite densityMeasurable factorMeasurable
      fallback factored second secondFinite secondNonzero, same]

/-- The Fisher–Neyman factorization as kernels. With a measurable statistic and
a scale that is finite and nonzero at every input, the conditional kernel of
the density is the conditional kernel of `g` precomposed with the statistic. -/
public theorem densityConditional_eq_precomp (reference : Measure target)
    (referenceFinite : Measure.SFinite reference) {gamma : Type w} {statistics : Space gamma}
    {density : alpha → beta → ENNReal} {factor : gamma → beta → ENNReal}
    (densityMeasurable : ENNRealMeasurable (Space.product source target)
      (fun pair => density pair.1 pair.2))
    (factorMeasurable : ENNRealMeasurable (Space.product statistics target)
      (fun pair => factor pair.1 pair.2))
    (fallback : beta) {statistic : alpha → gamma}
    (statisticMeasurable : MeasurableMap source statistics statistic) {scale : alpha → ENNReal}
    (factored : ∀ input output,
      density input output = ENNReal.mul (scale input) (factor (statistic input) output))
    (scaleFinite : ∀ input, ENNReal.Finite (scale input))
    (scaleNonzero : ∀ input, scale input ≠ ENNReal.zero) :
    densityConditional reference referenceFinite density densityMeasurable fallback =
      (densityConditional reference referenceFinite factor factorMeasurable fallback).precomp
        statistic statisticMeasurable :=
  Kernel.ext fun input => densityConditional_statistic reference referenceFinite
    densityMeasurable factorMeasurable fallback factored input (scaleFinite input)
    (scaleNonzero input)

/-- A zero scale leaves a null fiber, which is never normalizable, so the
conditional there is the fallback whatever the second density. -/
public theorem densityFiber_not_normalizable_of_zero_scale (reference : Measure target)
    {density : alpha → beta → ENNReal} {input : alpha} {factor : beta → ENNReal}
    (factored : density input = fun output => ENNReal.mul ENNReal.zero (factor output)) :
    ¬Measure.IsNormalizable (densityFiber reference density input) := by
  rw [isNormalizable_densityFiber_iff]
  intro bounds
  apply bounds.2
  unfold densityMass
  rw [factored]
  simp only [ENNReal.zero_mul]
  exact lintegral_zero reference

/-- An infinite scale on a factor of positive mass leaves a fiber of infinite
mass, which is never normalizable. -/
public theorem densityFiber_not_normalizable_of_top_scale (reference : Measure target)
    {density : alpha → beta → ENNReal} {input : alpha} {factor : beta → ENNReal}
    (factorMeasurable : ENNRealMeasurable target factor)
    (positive : lintegral reference factor ≠ ENNReal.zero)
    (factored : density input = fun output => ENNReal.mul ENNReal.top (factor output)) :
    ¬Measure.IsNormalizable (densityFiber reference density input) := by
  rw [isNormalizable_densityFiber_iff]
  intro bounds
  have infinite : densityMass reference density input = ENNReal.top := by
    unfold densityMass
    rw [factored, lintegral_smul reference ENNReal.top factorMeasurable,
      ENNReal.top_mul_of_ne_zero positive]
  have bounded := bounds.1
  rw [infinite] at bounded
  exact bounded

/-- The finite-mass premise of `semiproduct_densityConditional` is necessary.
The constant density against counting measure has an infinite fiber, and no
kernel rebuilds the joint measure from the fiber-mass marginal. -/
public theorem infinite_densityMass_does_not_disintegrate
    (kernel : Kernel (Space.discrete Unit) (Space.discrete Nat))
    (kernelFinite : IsSFinite kernel) :
    ((Measure.dirac (Space.discrete Unit) ()).withDensity
        (densityMass Measure.counting (fun (_ : Unit) (_ : Nat) => ENNReal.one))).semiproduct
        kernel kernelFinite ≠
      (Measure.prod (Measure.dirac (Space.discrete Unit) ()) Measure.counting
        Measure.countingSigmaFinite.toSFinite).withDensity (fun _ => ENNReal.one) := by
  intro equal
  have infinite : densityMass Measure.counting (fun (_ : Unit) (_ : Nat) => ENNReal.one) () =
      ENNReal.top := by
    unfold densityMass
    rw [lintegral_const, ENNReal.one_mul, Measure.counting_univ]
  have rectangle := congrArg (fun measure : Measure (Space.product (Space.discrete Unit)
      (Space.discrete Nat)) => measure (Set.product Set.univ (fun value : Nat => value = 0)))
    equal
  rw [Measure.semiproduct_apply_product _ _ _ (Space.discrete Unit).univ True.intro,
    Measure.restrict_univ,
    Problib.Measure.lintegral_withDensity _ (fun _ => True.intro) (fun _ => True.intro),
    lintegral_dirac _ _ (fun _ => True.intro), infinite, Measure.withDensity_one,
    Measure.prod_apply_product _ _ _ (Space.discrete Unit).univ True.intro,
    Measure.dirac_apply_univ, Measure.counting_singleton, ENNReal.one_mul] at rectangle
  classical
  by_cases null : kernel () (fun value : Nat => value = 0) = ENNReal.zero
  · rw [null, ENNReal.mul_zero] at rectangle
    exact ENNReal.one_ne_zero rectangle.symm
  · rw [ENNReal.top_mul_of_ne_zero null] at rectangle
    exact ENNReal.top_ne_finite NNReal.one rectangle

/-- A fiber scaled by a zero or infinite weight is not normalizable, so it takes
the fallback. -/
private theorem scaled_fiber_not_normalizable (factor : ENNReal)
    (degenerate : factor = ENNReal.zero ∨ factor = ENNReal.top) :
    ¬Measure.IsNormalizable (densityFiber (Measure.dirac (Space.discrete Nat) 1)
      (fun (_ : Unit) (_ : Nat) => ENNReal.mul factor ENNReal.one) ()) := by
  intro defined
  have total : densityFiber (Measure.dirac (Space.discrete Nat) 1)
      (fun (_ : Unit) (_ : Nat) => ENNReal.mul factor ENNReal.one) () Set.univ = factor := by
    rw [densityFiber_univ]
    show lintegral (Measure.dirac (Space.discrete Nat) 1)
      (fun _ => ENNReal.mul factor ENNReal.one) = factor
    rw [lintegral_const, Measure.dirac_apply_univ, ENNReal.mul_one, ENNReal.mul_one]
  rcases degenerate with zero | top
  · exact defined.nonzero (total.trans zero)
  · have bounded := defined.finite.univ_finite
    rw [total, top] at bounded
    exact bounded

private theorem unit_fiber :
    densityFiber (Measure.dirac (Space.discrete Nat) 1)
      (fun (_ : Unit) (_ : Nat) => ENNReal.one) () = Measure.dirac (Space.discrete Nat) 1 := by
  unfold densityFiber
  exact Measure.withDensity_one _

private theorem unit_fiber_normalizable :
    Measure.IsNormalizable (densityFiber (Measure.dirac (Space.discrete Nat) 1)
      (fun (_ : Unit) (_ : Nat) => ENNReal.one) ()) := by
  rw [unit_fiber]
  exact (Measure.IsProbability.dirac _ 1).to_normalizable

/-- The unit density against a Dirac reference conditions to that Dirac measure. -/
private theorem unit_densityConditional (fallback : Nat) :
    densityConditional (source := Space.discrete Unit) (Measure.dirac (Space.discrete Nat) 1)
        (Measure.SFinite.ofFinite (Measure.IsFinite.dirac _ 1))
        (fun _ _ => ENNReal.one) (ENNRealMeasurable.constant _ _) fallback () =
      Measure.dirac (Space.discrete Nat) 1 := by
  rw [densityConditional_eq_normalize _ _ _ _ () unit_fiber_normalizable]
  apply Measure.normalize_eq_of_smul_eq
  rw [unit_fiber, Measure.dirac_apply_univ, Measure.one_smul]

/-- The nonzero-weight premise of `densityConditional_mul_left` is necessary: a
zero weight sends a normalizable fiber to the fallback. -/
public theorem zero_weight_does_not_cancel :
    densityConditional (source := Space.discrete Unit) (Measure.dirac (Space.discrete Nat) 1)
        (Measure.SFinite.ofFinite (Measure.IsFinite.dirac _ 1))
        (fun _ _ => ENNReal.mul ENNReal.zero ENNReal.one) (ENNRealMeasurable.constant _ _) 0 () ≠
      densityConditional (source := Space.discrete Unit) (Measure.dirac (Space.discrete Nat) 1)
        (Measure.SFinite.ofFinite (Measure.IsFinite.dirac _ 1))
        (fun _ _ => ENNReal.one) (ENNRealMeasurable.constant _ _) 0 () := by
  rw [densityConditional_eq_dirac _ _ _ _ ()
      (scaled_fiber_not_normalizable ENNReal.zero (Or.inl rfl)),
    unit_densityConditional]
  intro equal
  have atOne := congrArg (fun measure : Measure (Space.discrete Nat) =>
    measure (fun value => value = 1)) equal
  rw [Measure.dirac_apply_of_not_mem (set := fun value : Nat => value = 1) _ _ True.intro
      (by decide),
    Measure.dirac_apply_of_mem (set := fun value : Nat => value = 1) _ _ True.intro rfl] at atOne
  exact ENNReal.one_ne_zero atOne.symm

/-- The finite-weight premise of `densityConditional_mul_left` is necessary: an
infinite weight sends a normalizable fiber to the fallback. -/
public theorem infinite_weight_does_not_cancel :
    densityConditional (source := Space.discrete Unit) (Measure.dirac (Space.discrete Nat) 1)
        (Measure.SFinite.ofFinite (Measure.IsFinite.dirac _ 1))
        (fun _ _ => ENNReal.mul ENNReal.top ENNReal.one) (ENNRealMeasurable.constant _ _) 0 () ≠
      densityConditional (source := Space.discrete Unit) (Measure.dirac (Space.discrete Nat) 1)
        (Measure.SFinite.ofFinite (Measure.IsFinite.dirac _ 1))
        (fun _ _ => ENNReal.one) (ENNRealMeasurable.constant _ _) 0 () := by
  rw [densityConditional_eq_dirac _ _ _ _ ()
      (scaled_fiber_not_normalizable ENNReal.top (Or.inr rfl)),
    unit_densityConditional]
  intro equal
  have atOne := congrArg (fun measure : Measure (Space.discrete Nat) =>
    measure (fun value => value = 1)) equal
  rw [Measure.dirac_apply_of_not_mem (set := fun value : Nat => value = 1) _ _ True.intro
      (by decide),
    Measure.dirac_apply_of_mem (set := fun value : Nat => value = 1) _ _ True.intro rfl] at atOne
  exact ENNReal.one_ne_zero atOne.symm

/-- The nonzero premise of `densityConditional_factor` is necessary. The
density `0·1` factors through the unit density with scale zero. The unit
density's fiber is normalizable, and the two conditionals differ. -/
public theorem zero_scale_does_not_factor :
    Measure.IsNormalizable (densityFiber (Measure.dirac (Space.discrete Nat) 1)
        (fun (_ : Unit) (_ : Nat) => ENNReal.one) ()) ∧
      densityConditional (source := Space.discrete Unit) (Measure.dirac (Space.discrete Nat) 1)
          (Measure.SFinite.ofFinite (Measure.IsFinite.dirac _ 1))
          (fun _ _ => ENNReal.mul ENNReal.zero ENNReal.one) (ENNRealMeasurable.constant _ _) 0
          () ≠
        densityConditional (source := Space.discrete Unit) (Measure.dirac (Space.discrete Nat) 1)
          (Measure.SFinite.ofFinite (Measure.IsFinite.dirac _ 1))
          (fun _ _ => ENNReal.one) (ENNRealMeasurable.constant _ _) 0 () :=
  ⟨unit_fiber_normalizable, zero_weight_does_not_cancel⟩

/-- The finite premise of `densityConditional_factor` is necessary. The density
`⊤·1` factors through the unit density with an infinite scale. The unit
density's fiber is normalizable, and the two conditionals differ. -/
public theorem top_scale_does_not_factor :
    Measure.IsNormalizable (densityFiber (Measure.dirac (Space.discrete Nat) 1)
        (fun (_ : Unit) (_ : Nat) => ENNReal.one) ()) ∧
      densityConditional (source := Space.discrete Unit) (Measure.dirac (Space.discrete Nat) 1)
          (Measure.SFinite.ofFinite (Measure.IsFinite.dirac _ 1))
          (fun _ _ => ENNReal.mul ENNReal.top ENNReal.one) (ENNRealMeasurable.constant _ _) 0
          () ≠
        densityConditional (source := Space.discrete Unit) (Measure.dirac (Space.discrete Nat) 1)
          (Measure.SFinite.ofFinite (Measure.IsFinite.dirac _ 1))
          (fun _ _ => ENNReal.one) (ENNRealMeasurable.constant _ _) 0 () :=
  ⟨unit_fiber_normalizable, infinite_weight_does_not_cancel⟩

end Problib.Measure.Kernel
