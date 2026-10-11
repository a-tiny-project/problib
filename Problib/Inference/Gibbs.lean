module

public import Problib.Inference.Involutive
public import Problib.Measure.Kernel.Site.Gibbs
public import Problib.Measure.Kernel.Site.Scan
import Problib.Measure.Kernel.Composition.Bind.Transport
import Problib.Measure.Integral.Density.Change

/-! Convergence of Gibbs scans on factor graphs.

A Gibbs update at a site draws the site from the joint density along the line
through the point. Against a base law, the update leaves the joint density
unchanged when refreshing the site from its reference leaves the base law
unchanged. The law that draws every site from its reference is such a base.

When the references are probability laws and the joint density lies between
`lower > 0` and `upper`, each Gibbs conditional keeps `lower / upper` of its
reference. A scan that visits every site is then minorized in one sweep, and
it converges in total variation from every law to the normalized joint density.
-/

set_option autoImplicit false

namespace Problib.Inference

open Problib.Real Problib.Measure
open Problib.Measure.Kernel (ConvergesFromEveryLaw)
open Problib.Measure.Kernel.Site

universe u v

variable {ι : Type u} {α : ι → Type v} {spaces : ∀ index, Space (α index)}

/-- The joint density against a probability law has finite nonzero mass when it
lies between `lower > 0` and `upper`. -/
public theorem withDensity_joint_normalizable (factors : List (Factor spaces))
    {base : Measure (Space.pi spaces)} (baseProbability : Measure.IsProbability base)
    {lower upper : NNReal} (lowerPositive : NNReal.lt NNReal.zero lower)
    (bounded : ∀ point, ENNReal.le (ENNReal.finite lower) (joint factors point) ∧
      ENNReal.le (joint factors point) (ENNReal.finite upper)) :
    Measure.IsNormalizable (base.withDensity (joint factors)) := by
  have constant (value : NNReal) :
      lintegral base (fun _ => ENNReal.finite value) = ENNReal.finite value := by
    rw [lintegral_const, baseProbability.univ_eq_one, ENNReal.mul_one]
  have mass : (base.withDensity (joint factors)) Set.univ = lintegral base (joint factors) := by
    rw [Measure.withDensity_apply _ _ (Space.pi spaces).univ, Measure.restrict_univ]
  have massUpper : ENNReal.le (lintegral base (joint factors)) (ENNReal.finite upper) := by
    rw [← constant upper]
    exact lintegral_mono _ (fun point => (bounded point).2)
  have massLower : ENNReal.le (ENNReal.finite lower) (lintegral base (joint factors)) := by
    rw [← constant lower]
    exact lintegral_mono _ (fun point => (bounded point).1)
  refine ⟨⟨?_⟩, ?_⟩
  · rw [mass]
    exact ENNReal.finite_of_le massUpper True.intro
  · rw [mass]
    intro zero
    rw [zero] at massLower
    exact (NNReal.zero_lt_iff_ne_zero lower).mp lowerPositive
      (ENNReal.finite_injective (ENNReal.le_zero_iff.mp massLower))

private theorem normalize_invariant {β : Type v} {space : Space β} {measure : Measure space}
    (defined : Measure.IsNormalizable measure) {kernel : Kernel space space}
    (invariant : measure.bind kernel = measure) :
    (Measure.normalize measure defined).bind kernel = Measure.normalize measure defined := by
  obtain ⟨mass, total⟩ := ENNReal.exists_finite_of_finite defined.finite.univ_finite
  rw [Measure.normalize_eq_of_total_eq measure defined total, Measure.smul_bind, invariant]

variable [DecidableEq ι]

/-- Replacing a site of the base law with an independent reference draw is
refreshing that site. -/
private theorem prod_map_replace (base : Measure (Space.pi spaces)) (site : ι)
    {measure : Measure (spaces site)} (finite : Measure.SFinite measure) :
    (Measure.prod base measure finite).map (fun pair => replace pair.1 site pair.2)
        (replace_measurable site) =
      base.bind (Step.const site measure finite).run := by
  unfold Measure.prod Measure.semiproduct
  rw [Measure.map_bind]
  rfl

/-- Refreshing the second coordinate of a pair from the conditional, and then
writing it into the site, is writing the site and then updating it. -/
private theorem gibbsKernel_map_replace (factors : List (Factor spaces))
    (reference : ∀ index, Measure (spaces index))
    (referenceFinite : ∀ index, Measure.SFinite (reference index))
    (fallback : ∀ index, α index) (site : ι) :
    (gibbsKernel (conditional factors reference referenceFinite fallback site)
        (gibbsStep factors reference referenceFinite fallback site).finite).map
        (fun pair => replace pair.1 site pair.2) (replace_measurable site) =
      (gibbsStep factors reference referenceFinite fallback site).run.precomp
        (fun pair => replace pair.1 site pair.2) (replace_measurable site) := by
  apply Kernel.ext
  intro pair
  unfold gibbsKernel
  rw [Kernel.map_apply, Kernel.precomp_apply, Kernel.deterministic_comp_apply,
    Kernel.attach_apply, Measure.map_comp, gibbsStep_run_apply,
    conditional_ignores factors reference referenceFinite fallback site pair.1 pair.2]
  congr 1
  funext value
  exact (replace_replace_same pair.1 site pair.2 value).symm

/-- A Gibbs update at a site leaves the joint density against `base` unchanged
when refreshing the site from its reference leaves `base` unchanged and the
joint density has finite mass along almost every line through the site. -/
public theorem gibbsStep_invariant (factors : List (Factor spaces))
    (reference : ∀ index, Measure (spaces index))
    (referenceFinite : ∀ index, Measure.SFinite (reference index))
    (fallback : ∀ index, α index) (site : ι) {base : Measure (Space.pi spaces)}
    (baseInvariant :
      base.bind (Step.const site (reference site) (referenceFinite site)).run = base)
    (finite : base.AE (fun point => ENNReal.Finite (Kernel.densityMass (reference site)
      (fun point value => joint factors (replace point site value)) point))) :
    KernelInvariant (base.withDensity (joint factors))
      (gibbsStep factors reference referenceFinite fallback site).run := by
  have pushed : ((Measure.prod base (reference site) (referenceFinite site)).withDensity
        (fun pair => joint factors (replace pair.1 site pair.2))).map
        (fun pair => replace pair.1 site pair.2) (replace_measurable site) =
      base.withDensity (joint factors) := by
    rw [Measure.map_withDensity _ _ (replace_measurable site) (joint_measurable factors),
      prod_map_replace base site (referenceFinite site), baseInvariant]
  have invariant : KernelInvariant
      ((Measure.prod base (reference site) (referenceFinite site)).withDensity
        (fun pair => joint factors (replace pair.1 site pair.2)))
      (gibbsKernel (conditional factors reference referenceFinite fallback site)
        (gibbsStep factors reference referenceFinite fallback site).finite) :=
    gibbs_densityConditional_invariant base (reference site) (referenceFinite site)
      (density := fun point value => joint factors (replace point site value))
      (ENNRealMeasurable.comp (joint_measurable factors) (replace_measurable site))
      (fallback site) finite
  unfold KernelInvariant at invariant ⊢
  rw [← pushed, Measure.bind_map,
    ← gibbsKernel_map_replace factors reference referenceFinite fallback site,
    ← Measure.map_bind, invariant]

/-- A Gibbs scan that visits every site converges in total variation from every
law to the normalized joint density against `base`, when the references and
`base` are probability laws, refreshing each scanned site leaves `base`
unchanged, and the joint density lies between `lower > 0` and `upper`. -/
public theorem gibbs_scan_converges (factors : List (Factor spaces))
    (reference : ∀ index, Measure (spaces index))
    (referenceFinite : ∀ index, Measure.SFinite (reference index))
    (referenceProbability : ∀ index, Measure.IsProbability (reference index))
    (fallback : ∀ index, α index) {order : List ι} (covers : ∀ index, index ∈ order)
    {base : Measure (Space.pi spaces)} (baseProbability : Measure.IsProbability base)
    (baseInvariant : ∀ site, site ∈ order →
      base.bind (Step.const site (reference site) (referenceFinite site)).run = base)
    {lower upper : NNReal} (lowerPositive : NNReal.lt NNReal.zero lower)
    (bounded : ∀ point, ENNReal.le (ENNReal.finite lower) (joint factors point) ∧
      ENNReal.le (joint factors point) (ENNReal.finite upper)) :
    ConvergesFromEveryLaw
      (sweep (order.map (gibbsStep factors reference referenceFinite fallback)))
      ⟨Measure.normalize (base.withDensity (joint factors))
          (withDensity_joint_normalizable factors baseProbability lowerPositive bounded),
        Measure.normalize_isProbability _ _⟩ := by
  obtain ⟨point⟩ := baseProbability.nonempty
  have lowerUpper : NNReal.le lower upper :=
    ENNReal.le_trans (bounded point).1 (bounded point).2
  have upperPositive : NNReal.lt NNReal.zero upper :=
    NNReal.lt_of_lt_of_le lowerPositive lowerUpper
  have atMostOne : NNReal.le (NNReal.div lower upper) NNReal.one := by
    apply NNReal.le_of_mul_le_mul_left upperPositive
    rw [NNReal.mul_div_cancel lower ((NNReal.zero_lt_iff_ne_zero upper).mp upperPositive),
      NNReal.mul_one]
    exact lowerUpper
  have lineFinite (site : ι) (point : ∀ index, α index) :
      ENNReal.Finite (Kernel.densityMass (reference site)
        (fun point value => joint factors (replace point site value)) point) := by
    have constant := lintegral_const (reference site) (ENNReal.finite upper)
    rw [(referenceProbability site).univ_eq_one, ENNReal.mul_one] at constant
    refine ENNReal.finite_of_le (right := ENNReal.finite upper) ?_ True.intro
    unfold Kernel.densityMass
    rw [← constant]
    exact lintegral_mono _ (fun value => (bounded (replace point site value)).2)
  apply sweep_convergesFromEveryLaw reference referenceFinite referenceProbability
    (weight := NNReal.div lower upper)
  · intro index
    exact List.mem_map.mpr
      ⟨gibbsStep factors reference referenceFinite fallback index,
        List.mem_map.mpr ⟨index, covers index, rfl⟩, rfl⟩
  · intro step member point
    obtain ⟨site, _, rfl⟩ := List.mem_map.mp member
    exact conditional_isProbability factors reference referenceFinite fallback site point
  · exact NNReal.div_positive lowerPositive upperPositive
  · exact atMostOne
  · intro step member point set setMeasurable
    obtain ⟨site, _, rfl⟩ := List.mem_map.mp member
    exact conditional_lower factors reference referenceFinite referenceProbability fallback
      site lowerPositive bounded point setMeasurable
  · apply normalize_invariant
    apply sweep_invariant
    intro step member
    obtain ⟨site, inOrder, rfl⟩ := List.mem_map.mp member
    exact gibbsStep_invariant factors reference referenceFinite fallback site
      (baseInvariant site inOrder) (Measure.ae_of_forall (lineFinite site))

/-- A Gibbs scan in an order that lists every site once converges in total
variation from every law to the normalized joint density against the law that
draws each site from its reference, when the joint density lies between
`lower > 0` and `upper`. -/
public theorem gibbs_scan_converges_product (factors : List (Factor spaces))
    (reference : ∀ index, Measure (spaces index))
    (referenceFinite : ∀ index, Measure.SFinite (reference index))
    (referenceProbability : ∀ index, Measure.IsProbability (reference index))
    (fallback : ∀ index, α index) {order : List ι} (sites : FiniteEnumeration order)
    {lower upper : NNReal}
    (lowerPositive : NNReal.lt NNReal.zero lower)
    (bounded : ∀ point, ENNReal.le (ENNReal.finite lower) (joint factors point) ∧
      ENNReal.le (joint factors point) (ENNReal.finite upper)) :
    ConvergesFromEveryLaw
      (sweep (order.map (gibbsStep factors reference referenceFinite fallback)))
      ⟨Measure.normalize
          ((refresh order reference referenceFinite fallback).withDensity (joint factors))
          (withDensity_joint_normalizable factors
            (refresh_isProbability order reference referenceFinite referenceProbability
              fallback)
            lowerPositive bounded),
        Measure.normalize_isProbability _ _⟩ :=
  gibbs_scan_converges factors reference referenceFinite referenceProbability fallback
    sites.complete
    (refresh_isProbability order reference referenceFinite referenceProbability fallback)
    (fun site _ => refresh_invariant sites reference referenceFinite referenceProbability
      fallback site)
    lowerPositive bounded

omit [DecidableEq ι] in
/-- A function that is finite and nonzero at each point of a list has a
positive lower bound on the list. -/
private theorem lower_of_list (values : (∀ index, α index) → ENNReal)
    (positive : ∀ point, ENNReal.Finite (values point) ∧ values point ≠ ENNReal.zero)
    (points : List (∀ index, α index)) :
    ∃ lower : NNReal, NNReal.lt NNReal.zero lower ∧
      ∀ point, point ∈ points → ENNReal.le (ENNReal.finite lower) (values point) := by
  induction points with
  | nil => exact ⟨NNReal.one, NNReal.one_positive, fun _ member => nomatch member⟩
  | cons head rest induction =>
      obtain ⟨lower, lowerPositive, below⟩ := induction
      obtain ⟨value, equal⟩ := ENNReal.exists_finite_of_finite (positive head).1
      have valuePositive : NNReal.lt NNReal.zero value :=
        (NNReal.zero_lt_iff_ne_zero value).mpr
          (fun zero => (positive head).2 (equal.trans (congrArg ENNReal.finite zero)))
      rcases NNReal.le_total lower value with atMost | atLeast
      · refine ⟨lower, lowerPositive, fun point member => ?_⟩
        rcases List.mem_cons.mp member with rfl | inRest
        · rw [equal]
          exact atMost
        · exact below point inRest
      · refine ⟨value, valuePositive, fun point member => ?_⟩
        rcases List.mem_cons.mp member with rfl | inRest
        · rw [equal]
          exact NNReal.le_refl value
        · exact ENNReal.le_trans
            (show ENNReal.le (ENNReal.finite value) (ENNReal.finite lower) from atLeast)
            (below point inRest)

omit [DecidableEq ι] in
/-- A function that is finite at each point of a list has a finite upper bound
on the list. -/
private theorem upper_of_list (values : (∀ index, α index) → ENNReal)
    (finite : ∀ point, ENNReal.Finite (values point)) (points : List (∀ index, α index)) :
    ∃ upper : NNReal,
      ∀ point, point ∈ points → ENNReal.le (values point) (ENNReal.finite upper) := by
  induction points with
  | nil => exact ⟨NNReal.zero, fun _ member => nomatch member⟩
  | cons head rest induction =>
      obtain ⟨upper, above⟩ := induction
      obtain ⟨value, equal⟩ := ENNReal.exists_finite_of_finite (finite head)
      rcases NNReal.le_total upper value with atMost | atLeast
      · refine ⟨value, fun point member => ?_⟩
        rcases List.mem_cons.mp member with rfl | inRest
        · rw [equal]
          exact NNReal.le_refl value
        · exact ENNReal.le_trans (above point inRest)
            (show ENNReal.le (ENNReal.finite upper) (ENNReal.finite value) from atMost)
      · refine ⟨upper, fun point member => ?_⟩
        rcases List.mem_cons.mp member with rfl | inRest
        · rw [equal]
          exact atLeast
        · exact above point inRest

/-- On a product whose points a finite list covers, a Gibbs scan in an order
that lists every site once converges in total variation from every law to the
normalized joint density against the law that draws each site from its
reference, when the joint density is finite and nonzero at every point. -/
public theorem gibbs_scan_converges_finite (factors : List (Factor spaces))
    (reference : ∀ index, Measure (spaces index))
    (referenceFinite : ∀ index, Measure.SFinite (reference index))
    (referenceProbability : ∀ index, Measure.IsProbability (reference index))
    (fallback : ∀ index, α index) {order : List ι} (sites : FiniteEnumeration order)
    {points : List (∀ index, α index)} (complete : ∀ point, point ∈ points)
    (positive : ∀ point, ENNReal.Finite (joint factors point) ∧
      joint factors point ≠ ENNReal.zero) :
    ∃ defined : Measure.IsNormalizable
        ((refresh order reference referenceFinite fallback).withDensity (joint factors)),
      ConvergesFromEveryLaw
        (sweep (order.map (gibbsStep factors reference referenceFinite fallback)))
        ⟨Measure.normalize _ defined, Measure.normalize_isProbability _ defined⟩ := by
  obtain ⟨lower, lowerPositive, below⟩ := lower_of_list (joint factors) positive points
  obtain ⟨upper, above⟩ := upper_of_list (joint factors) (fun point => (positive point).1) points
  exact ⟨_, gibbs_scan_converges_product factors reference referenceFinite referenceProbability
    fallback sites lowerPositive
    (fun point => ⟨below point (complete point), above point (complete point)⟩)⟩

end Problib.Inference
