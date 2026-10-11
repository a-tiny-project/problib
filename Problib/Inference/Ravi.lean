module

public import Problib.Inference.Reciprocal
public import Problib.Measure.Additive.AbsoluteContinuity
public import Problib.Measure.Kernel.Product.Density
public import Problib.Measure.Integral.Density.AlmostEverywhere
public import Problib.Measure.Integral.Lebesgue.Zero
public import Problib.Measure.Kernel.Composition.Bind.Transport
set_option autoImplicit false

/-! RAVI's answers from densities and a support condition.

A mixture draws an auxiliary `u` and then a value `x`. Its joint law `J` over
`(x, u)` has a density `j` against a product reference `ν ⊗ ν_U`, and its value
marginal `Q` has no closed-form density. A meta kernel `R`, whose law at `x`
has density `r(x, ·)` against `ν_U`, proposes an auxiliary for a value
(Lew, Cusumano-Towner and Mansinghka, UAI 2022).

* Forward: the joint draw weighted by `r / j` is properly weighted for `ν`
  restricted to where a density `q` of `Q` is positive
  (`ravi_forward_restricted`). It asks that the meta-inference joint `Q ⋉ R`
  be absolutely continuous with respect to `J`: for `ν`-almost every `x` with
  `q(x) > 0`, `R(x)` puts no mass where `j(x, ·)` vanishes. Then
  `ravi_forward_properlyWeighted`'s `answer` holds at the restricted reference.
* Reverse: the estimate `j / r`, read off a draw from `R(x)`, has mean
  `∫_{r > 0} j(x, u) ν_U(du)`, and that mean is a density of `Q`
  (`ravi_reverse_density`). It asks the converse continuity, `J ≪ Q ⋉ R`: for
  `ν`-almost every `x`, `j(x, ·)` vanishes where `r(x, ·)` does.

Both conditions are stated on measures, so neither depends on which version of
a density is read. `Necessity/Reciprocal.lean` shows the forward one cannot be
dropped. The joint density of a mixture whose auxiliary and component have
densities is the product of the two (`joint_withDensity_swap`), and the value
marginal of a product density integrates out the auxiliary
(`marginal_withDensity`). -/

namespace Problib.Inference

open Problib.Real Problib.Measure

universe u v

variable {α : Type u} {δ : Type v}

public section

variable {space : Space α} {extra : Space δ}

/-! ### Products and marginals of densities -/

/-- Swapping the coordinates of a weighted measure swaps the density's
arguments. -/
theorem withDensity_map_swap (measure : Measure (Space.product extra space))
    {density : δ × α → ENNReal}
    (densityMeasurable : ENNRealMeasurable (Space.product extra space) density) :
    (measure.withDensity density).map (fun pair => (pair.2, pair.1))
        (Space.swap_measurable extra space) =
      (measure.map (fun pair => (pair.2, pair.1)) (Space.swap_measurable extra space)).withDensity
        (fun pair => density (pair.2, pair.1)) := by
  have swappedMeasurable : ENNRealMeasurable (Space.product space extra)
      (fun pair => density (pair.2, pair.1)) :=
    densityMeasurable.comp (Space.swap_measurable space extra)
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  rw [lintegral_map _ _ _ measurable,
    lintegral_withDensity _ densityMeasurable
      (measurable.comp (Space.swap_measurable extra space)),
    lintegral_withDensity _ swappedMeasurable measurable,
    lintegral_map _ _ _ (ENNRealMeasurable.mul swappedMeasurable measurable)]

/-- A mixture whose auxiliary has density `m` against `ν_U` and whose component
at `u` has density `k(u, ·)` against `ν` has, read over `(x, u)`, the joint
density `m(u) k(u, x)` against `ν ⊗ ν_U`. -/
theorem joint_withDensity_swap {reference : Measure space} (referenceFinite : Measure.SFinite reference)
    {auxiliary : Measure extra} (auxiliaryFinite : Measure.SFinite auxiliary)
    {mixing : δ → ENNReal} (mixingMeasurable : ENNRealMeasurable extra mixing)
    (component : Kernel extra space) (componentFinite : Kernel.IsSFinite component)
    {componentDensity : δ × α → ENNReal}
    (componentMeasurable : ENNRealMeasurable (Space.product extra space) componentDensity)
    (represents : ∀ auxiliaryValue, component auxiliaryValue =
      reference.withDensity (fun value => componentDensity (auxiliaryValue, value))) :
    ((auxiliary.withDensity mixing).semiproduct component componentFinite).map
        (fun pair => (pair.2, pair.1)) (Space.swap_measurable extra space) =
      (Measure.prod reference auxiliary auxiliaryFinite).withDensity
        (fun pair => ENNReal.mul (mixing pair.2) (componentDensity (pair.2, pair.1))) := by
  rw [Measure.semiproduct_withDensity_prod _ mixingMeasurable reference referenceFinite _ _
      componentMeasurable represents,
    withDensity_map_swap _ (ENNRealMeasurable.mul componentMeasurable
      (mixingMeasurable.comp (Space.first_measurable extra space))),
    Measure.prod_swap auxiliaryFinite referenceFinite]
  congr 1
  funext pair
  exact ENNReal.mul_comm _ _

/-- The value marginal of a product density integrates the auxiliary out. -/
theorem marginal_withDensity (reference : Measure space) {auxiliary : Measure extra}
    (auxiliaryFinite : Measure.SFinite auxiliary) {density : α × δ → ENNReal}
    (densityMeasurable : ENNRealMeasurable (Space.product space extra) density) :
    ((Measure.prod reference auxiliary auxiliaryFinite).withDensity density).map Prod.fst
        (Space.first_measurable space extra) =
      reference.withDensity (fun value => lintegral auxiliary fun other => density (value, other)) := by
  have sectionMeasurable : ENNRealMeasurable space
      (fun value => lintegral auxiliary fun other => density (value, other)) :=
    Kernel.lintegral_measurable_joint (Kernel.const space auxiliary)
      (Kernel.IsSFinite.const space auxiliaryFinite) (function := fun value other => density (value, other))
      densityMeasurable
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  have firstMeasurable := measurable.comp (Space.first_measurable space extra)
  rw [lintegral_map _ _ _ measurable, lintegral_withDensity _ densityMeasurable firstMeasurable,
    lintegral_prod _ _ _ (ENNRealMeasurable.mul densityMeasurable firstMeasurable),
    lintegral_withDensity _ sectionMeasurable measurable]
  apply lintegral_congr
  intro value
  show lintegral auxiliary (fun other => ENNReal.mul (density (value, other)) (function value)) = _
  rw [show (fun other => ENNReal.mul (density (value, other)) (function value)) =
      fun other => ENNReal.mul (function value) (density (value, other)) from
      funext fun _ => ENNReal.mul_comm _ _,
    lintegral_smul _ _ (densityMeasurable.comp (Kernel.pair_left_measurable value)),
    ENNReal.mul_comm]

/-! ### Weights and null sets -/

/-- RAVI's forward weight `r / j`, read as zero where the joint density
vanishes. -/
@[expose] noncomputable def raviWeight (jointDensity metaDensity : α × δ → NNReal)
    (pair : α × δ) : NNReal :=
  NNReal.mul (metaDensity pair) (NNReal.div NNReal.one (jointDensity pair))

/-- RAVI's reverse estimate `j / r`, read as zero where the meta density
vanishes. -/
@[expose] noncomputable def raviEstimate (jointDensity metaDensity : α × δ → NNReal)
    (pair : α × δ) : NNReal :=
  NNReal.mul (jointDensity pair) (NNReal.div NNReal.one (metaDensity pair))

theorem raviWeight_measurable {jointDensity metaDensity : α × δ → NNReal}
    (jointMeasurable : MeasurableMap (Space.product space extra) weightSpace jointDensity)
    (metaMeasurable : MeasurableMap (Space.product space extra) weightSpace metaDensity) :
    MeasurableMap (Space.product space extra) weightSpace (raviWeight jointDensity metaDensity) :=
  weight_mul_measurable metaMeasurable (weight_inverse_measurable jointMeasurable)

theorem raviEstimate_measurable {jointDensity metaDensity : α × δ → NNReal}
    (jointMeasurable : MeasurableMap (Space.product space extra) weightSpace jointDensity)
    (metaMeasurable : MeasurableMap (Space.product space extra) weightSpace metaDensity) :
    MeasurableMap (Space.product space extra) weightSpace (raviEstimate jointDensity metaDensity) :=
  weight_mul_measurable jointMeasurable (weight_inverse_measurable metaMeasurable)

/-- A weight times another's reciprocal, times the other, is the weight where
the other is positive. -/
private theorem mul_reciprocal_cancel (value other : NNReal) (nonzero : other ≠ NNReal.zero) :
    NNReal.mul other (NNReal.mul value (NNReal.div NNReal.one other)) = value := by
  rw [← NNReal.mul_assoc, NNReal.mul_comm other value, NNReal.mul_assoc,
    NNReal.mul_div_cancel NNReal.one nonzero, NNReal.mul_one]

/-- A density that vanishes on a region weighs it zero. -/
private theorem withDensity_null_of_zero {γ : Type u} {carrier : Space γ} (measure : Measure carrier)
    {density : γ → ENNReal} {region : Set γ} (regionMeasurable : carrier.Measurable region)
    (zero : ∀ value, region value → density value = ENNReal.zero) :
    (measure.withDensity density) region = ENNReal.zero := by
  rw [measure.withDensity_apply density regionMeasurable]
  rw [lintegral_congr_ae (right := fun _ => ENNReal.zero)
    ((measure.ae_restrict_mem regionMeasurable).mono zero), lintegral_zero]

/-- A weighted measure that misses a region has a density that vanishes almost
everywhere on it. -/
private theorem ae_zero_of_withDensity_null {γ : Type u} {carrier : Space γ}
    {measure : Measure carrier} {density : γ → ENNReal}
    (densityMeasurable : ENNRealMeasurable carrier density) {region : Set γ}
    (regionMeasurable : carrier.Measurable region)
    (null : (measure.withDensity density) region = ENNReal.zero) :
    measure.AE (fun value => region value → density value = ENNReal.zero) := by
  rw [measure.withDensity_apply density regionMeasurable,
    ← lintegral_indicator measure region regionMeasurable] at null
  refine ((lintegral_eq_zero_iff
    (ENNRealMeasurable.indicator regionMeasurable densityMeasurable)).mp null).mono ?_
  intro value vanishing member
  rw [ennrealIndicator_of_mem member] at vanishing
  exact vanishing

/-- The region where a finite weight vanishes is measurable. -/
private theorem weight_zero_measurable {γ : Type u} {carrier : Space γ} {weight : γ → NNReal}
    (measurable : MeasurableMap carrier weightSpace weight) :
    carrier.Measurable (fun value => ENNReal.finite (weight value) = ENNReal.zero) :=
  ENNRealMeasurable.eq_set (finite_weight_measurable measurable)
    (ENNRealMeasurable.constant carrier ENNReal.zero)

/-- A meta-inference joint whose meta kernel has densities against `ν_U`, over
a value law with a density against `ν`, has the product density `r q` against
`ν ⊗ ν_U`. -/
private theorem meta_joint_density {reference : Measure space} {auxiliary : Measure extra}
    (auxiliaryFinite : Measure.SFinite auxiliary) {density : α → ENNReal}
    (densityMeasurable : ENNRealMeasurable space density)
    {metaKernel : Kernel space extra} (metaFinite : Kernel.IsSFinite metaKernel)
    {metaDensity : α × δ → NNReal}
    (metaMeasurable : MeasurableMap (Space.product space extra) weightSpace metaDensity)
    (metaEq : ∀ value, metaKernel value =
      auxiliary.withDensity (fun other => ENNReal.finite (metaDensity (value, other)))) :
    (reference.withDensity density).semiproduct metaKernel metaFinite =
      (Measure.prod reference auxiliary auxiliaryFinite).withDensity
        (fun pair => ENNReal.mul (ENNReal.finite (metaDensity pair)) (density pair.1)) :=
  Measure.semiproduct_withDensity_prod reference densityMeasurable auxiliary auxiliaryFinite
    metaKernel metaFinite (finite_weight_measurable metaMeasurable) metaEq

/-! ### RAVI's forward answer -/

/-- RAVI's forward answer at the reference restricted to a density's support.
A joint draw of a value and its auxiliary, with density `j` against
`ν ⊗ ν_U`, weighted by `r / j`, is properly weighted for `ν` restricted to where
a density `q` of the value's law is positive. The support condition is
`Q ⋉ R ≪ J`: for `ν`-almost every `x` with `q(x) > 0`, the meta kernel puts no
mass where `j(x, ·)` vanishes. Any version of `q` serves. -/
theorem ravi_forward_restricted {reference : Measure space} {auxiliary : Measure extra}
    (auxiliaryFinite : Measure.SFinite auxiliary)
    {joint : Measure (Space.product space extra)} (probability : Measure.IsProbability joint)
    {jointDensity : α × δ → NNReal}
    (jointMeasurable : MeasurableMap (Space.product space extra) weightSpace jointDensity)
    (jointEq : joint = (Measure.prod reference auxiliary auxiliaryFinite).withDensity
      (fun pair => ENNReal.finite (jointDensity pair)))
    {metaKernel : Kernel space extra}
    (metaMarkov : ∀ value, Measure.IsProbability (metaKernel value))
    (metaFinite : Kernel.IsSFinite metaKernel) {metaDensity : α × δ → NNReal}
    (metaMeasurable : MeasurableMap (Space.product space extra) weightSpace metaDensity)
    (metaEq : ∀ value, metaKernel value =
      auxiliary.withDensity (fun other => ENNReal.finite (metaDensity (value, other))))
    {density : α → ENNReal} (densityMeasurable : ENNRealMeasurable space density)
    (isDensity : Measure.IsDensity (joint.map Prod.fst (Space.first_measurable space extra))
      reference density)
    (support : Measure.AbsolutelyContinuous
      ((joint.map Prod.fst (Space.first_measurable space extra)).semiproduct metaKernel metaFinite)
      joint) :
    ProperlyWeighted (reference.restrict fun value => density value ≠ ENNReal.zero)
      (joint.map (fun pair => (pair.1, raviWeight jointDensity metaDensity pair))
        (Space.pair_measurable (Space.first_measurable space extra)
          (raviWeight_measurable jointMeasurable metaMeasurable))) := by
  let positive : Set α := fun value => density value ≠ ENNReal.zero
  have vanishingMeasurable : space.Measurable (fun value => density value = ENNReal.zero) :=
    ENNRealMeasurable.eq_set densityMeasurable (ENNRealMeasurable.constant space ENNReal.zero)
  have positiveMeasurable : space.Measurable positive := space.complement vanishingMeasurable
  have jointFinite := finite_weight_measurable jointMeasurable
  have metaFiniteMeasurable := finite_weight_measurable metaMeasurable
  -- Where `q` vanishes, so does `j`: `J({q = 0} × U) = Q({q = 0}) = 0`.
  have marginalZero : (Measure.prod reference auxiliary auxiliaryFinite).AE (fun pair =>
      density pair.1 = ENNReal.zero → ENNReal.finite (jointDensity pair) = ENNReal.zero) := by
    have regionMeasurable : (Space.product space extra).Measurable
        (fun pair => density pair.1 = ENNReal.zero) :=
      Space.first_measurable space extra vanishingMeasurable
    refine ae_zero_of_withDensity_null jointFinite regionMeasurable ?_
    rw [← jointEq]
    have mapped := Measure.map_apply joint Prod.fst (Space.first_measurable space extra)
      vanishingMeasurable
    rw [isDensity] at mapped
    show joint (Set.preimage Prod.fst (fun value => density value = ENNReal.zero)) = ENNReal.zero
    rw [← mapped]
    exact withDensity_null_of_zero reference vanishingMeasurable fun _ zero => zero
  -- Where `q` is positive and `j` vanishes, so does `r`: `Q ⋉ R ≪ J`.
  have jointZero : (Measure.prod reference auxiliary auxiliaryFinite).AE (fun pair => density pair.1 ≠ ENNReal.zero →
      ENNReal.finite (jointDensity pair) = ENNReal.zero →
        ENNReal.finite (metaDensity pair) = ENNReal.zero) := by
    have regionMeasurable := weight_zero_measurable jointMeasurable
    have jointNull : joint (fun pair => ENNReal.finite (jointDensity pair) = ENNReal.zero) =
        ENNReal.zero := by
      rw [jointEq]
      exact withDensity_null_of_zero _ regionMeasurable fun _ zero => zero
    have metaNull := support regionMeasurable jointNull
    rw [isDensity, meta_joint_density auxiliaryFinite densityMeasurable metaFinite metaMeasurable
      metaEq] at metaNull
    refine (ae_zero_of_withDensity_null
      (ENNRealMeasurable.mul metaFiniteMeasurable
        (densityMeasurable.comp (Space.first_measurable space extra)))
      regionMeasurable metaNull).mono ?_
    intro pair vanishing positiveHere zero
    rcases ENNReal.mul_eq_zero_iff.mp (vanishing zero) with metaZero | densityZero
    · exact metaZero
    · exact absurd densityZero positiveHere
  have restricted : reference.restrict positive =
      reference.withDensity (ennrealIndicator positive fun _ => ENNReal.one) := by
    rw [reference.withDensity_indicator _ positiveMeasurable, Measure.withDensity_one]
  have answer : (reference.restrict positive).semiproduct metaKernel metaFinite =
      joint.withDensity (fun pair => ENNReal.finite (raviWeight jointDensity metaDensity pair)) := by
    rw [restricted, meta_joint_density auxiliaryFinite
      (ENNRealMeasurable.indicator positiveMeasurable (ENNRealMeasurable.constant space _))
      metaFinite metaMeasurable metaEq, jointEq,
      Measure.withDensity_withDensity _ jointFinite
        (finite_weight_measurable (raviWeight_measurable jointMeasurable metaMeasurable))]
    apply Measure.withDensity_congr_ae
    refine (marginalZero.and jointZero).mono ?_
    intro pair ⟨marginal, joined⟩
    show ENNReal.mul (ENNReal.finite (metaDensity pair))
        (ennrealIndicator positive (fun _ => ENNReal.one) pair.1) =
      ENNReal.mul (ENNReal.finite (jointDensity pair))
        (ENNReal.finite (raviWeight jointDensity metaDensity pair))
    by_cases densityZero : density pair.1 = ENNReal.zero
    · rw [ennrealIndicator_of_not_mem (region := positive)
          (fun positiveHere => positiveHere densityZero),
        ENNReal.mul_zero, marginal densityZero, ENNReal.zero_mul]
    · rw [ennrealIndicator_of_mem (region := positive) densityZero, ENNReal.mul_one]
      by_cases jointVanishes : ENNReal.finite (jointDensity pair) = ENNReal.zero
      · rw [joined densityZero jointVanishes, jointVanishes, ENNReal.zero_mul]
      · have nonzero : jointDensity pair ≠ NNReal.zero :=
          fun equal => jointVanishes (congrArg ENNReal.finite equal)
        rw [ENNReal.finite_mul_finite, raviWeight, mul_reciprocal_cancel _ _ nonzero]
  exact ravi_forward_properlyWeighted probability metaMarkov metaFinite
    (raviWeight_measurable jointMeasurable metaMeasurable) answer

/-! ### RAVI's reverse answer -/

/-- An estimate read off a Markov meta kernel is unbiased for its mean under
the kernel. -/
theorem readEstimate_unbiased {metaKernel : Kernel space extra}
    (metaMarkov : ∀ value, Measure.IsProbability (metaKernel value))
    (metaFinite : Kernel.IsSFinite metaKernel) {estimate : α × δ → NNReal}
    (estimateMeasurable : MeasurableMap (Space.product space extra) weightSpace estimate) :
    UnbiasedEstimate (fun value => lintegral (metaKernel value) fun other =>
        ENNReal.finite (estimate (value, other)))
      (readEstimate metaKernel metaFinite estimate estimateMeasurable) where
  probability value := by
    rw [readEstimate_apply]
    exact (metaMarkov value).map _ _
  mean_eq value := by
    rw [readEstimate_apply,
      lintegral_map _ _ _ (finite_weight_measurable (MeasurableMap.identity weightSpace))]

/-- RAVI's reverse answer. The estimate `j / r`, read off a draw from the
meta kernel at `x`, has a mean that is a density of the value's law `Q`. The
support condition is `J ≪ Q ⋉ R`: for `ν`-almost every `x`, `j(x, ·)` vanishes
`ν_U`-almost everywhere where `r(x, ·)` does. -/
theorem ravi_reverse_density {reference : Measure space} {auxiliary : Measure extra}
    (auxiliaryFinite : Measure.SFinite auxiliary)
    {joint : Measure (Space.product space extra)} {jointDensity : α × δ → NNReal}
    (jointMeasurable : MeasurableMap (Space.product space extra) weightSpace jointDensity)
    (jointEq : joint = (Measure.prod reference auxiliary auxiliaryFinite).withDensity
      (fun pair => ENNReal.finite (jointDensity pair)))
    {metaKernel : Kernel space extra} (metaFinite : Kernel.IsSFinite metaKernel)
    {metaDensity : α × δ → NNReal}
    (metaMeasurable : MeasurableMap (Space.product space extra) weightSpace metaDensity)
    (metaEq : ∀ value, metaKernel value =
      auxiliary.withDensity (fun other => ENNReal.finite (metaDensity (value, other))))
    (support : Measure.AbsolutelyContinuous joint
      ((joint.map Prod.fst (Space.first_measurable space extra)).semiproduct metaKernel
        metaFinite)) :
    Measure.IsDensity (joint.map Prod.fst (Space.first_measurable space extra)) reference
      (fun value => lintegral (metaKernel value) fun other =>
        ENNReal.finite (raviEstimate jointDensity metaDensity (value, other))) := by
  have jointFinite := finite_weight_measurable jointMeasurable
  have metaFiniteMeasurable := finite_weight_measurable metaMeasurable
  have estimateFinite :=
    finite_weight_measurable (raviEstimate_measurable jointMeasurable metaMeasurable)
  have productMeasurable : ENNRealMeasurable (Space.product space extra) (fun pair =>
      ENNReal.mul (ENNReal.finite (metaDensity pair))
        (ENNReal.finite (raviEstimate jointDensity metaDensity pair))) :=
    ENNRealMeasurable.mul metaFiniteMeasurable estimateFinite
  -- Where `r` vanishes, so does `j`: the meta joint misses `{r = 0}`, and `J ≪ Q ⋉ R`.
  have metaZero : (Measure.prod reference auxiliary auxiliaryFinite).AE (fun pair =>
      ENNReal.finite (metaDensity pair) = ENNReal.zero →
        ENNReal.finite (jointDensity pair) = ENNReal.zero) := by
    have regionMeasurable := weight_zero_measurable metaMeasurable
    refine ae_zero_of_withDensity_null jointFinite regionMeasurable ?_
    rw [← jointEq]
    refine support regionMeasurable ?_
    have sectionZero : ∀ value, lintegral (metaKernel value) (fun other =>
        ennrealIndicator (fun pair => ENNReal.finite (metaDensity pair) = ENNReal.zero)
          (fun _ => ENNReal.one) (value, other)) = ENNReal.zero := by
      intro value
      have sectionMeasurable := (ENNRealMeasurable.indicator regionMeasurable
        (ENNRealMeasurable.constant (Space.product space extra) ENNReal.one)).comp
          (Kernel.pair_left_measurable value)
      rw [metaEq value, lintegral_withDensity _
        (metaFiniteMeasurable.comp (Kernel.pair_left_measurable value)) sectionMeasurable]
      refine (lintegral_congr _ (right := fun _ => ENNReal.zero) fun other => ?_).trans
        (lintegral_zero _)
      show ENNReal.mul (ENNReal.finite (metaDensity (value, other)))
        (ennrealIndicator (fun pair => ENNReal.finite (metaDensity pair) = ENNReal.zero)
          (fun _ => ENNReal.one) (value, other)) = ENNReal.zero
      by_cases member : ENNReal.finite (metaDensity (value, other)) = ENNReal.zero
      · rw [member, ENNReal.zero_mul]
      · rw [ennrealIndicator_of_not_mem
          (region := fun pair => ENNReal.finite (metaDensity pair) = ENNReal.zero) member,
          ENNReal.mul_zero]
    rw [apply_eq_lintegral_indicator _ regionMeasurable,
      lintegral_semiproduct _ _ _ (ENNRealMeasurable.indicator regionMeasurable
        (ENNRealMeasurable.constant _ _))]
    exact (lintegral_congr _ sectionZero).trans (lintegral_zero _)
  have mean : (fun value => lintegral (metaKernel value) fun other =>
      ENNReal.finite (raviEstimate jointDensity metaDensity (value, other))) =
      fun value => lintegral auxiliary fun other =>
        ENNReal.mul (ENNReal.finite (metaDensity (value, other)))
          (ENNReal.finite (raviEstimate jointDensity metaDensity (value, other))) := by
    funext value
    rw [metaEq value, lintegral_withDensity _
      (metaFiniteMeasurable.comp (Kernel.pair_left_measurable value))
      (estimateFinite.comp (Kernel.pair_left_measurable value))]
  rw [Measure.IsDensity, mean, ← marginal_withDensity reference auxiliaryFinite productMeasurable,
    jointEq]
  congr 1
  apply Measure.withDensity_congr_ae
  refine metaZero.mono ?_
  intro pair vanishing
  show ENNReal.finite (jointDensity pair) = ENNReal.mul (ENNReal.finite (metaDensity pair))
    (ENNReal.finite (raviEstimate jointDensity metaDensity pair))
  by_cases metaVanishes : ENNReal.finite (metaDensity pair) = ENNReal.zero
  · rw [vanishing metaVanishes, metaVanishes, ENNReal.zero_mul]
  · have nonzero : metaDensity pair ≠ NNReal.zero :=
      fun equal => metaVanishes (congrArg ENNReal.finite equal)
    rw [ENNReal.finite_mul_finite, raviEstimate, mul_reciprocal_cancel _ _ nonzero]

/-! ### Mixtures

A mixture `Q = let u ← M in K[u]` reads RAVI's joint as its own semiproduct,
swapped to put the value first. Its density is `m(u) k(u, x)` when the mixing
law and the component have densities `m` and `k(u, ·)`. -/

/-- A mixture's joint density over `(x, u)`: `m(u) k(u, x)`. -/
@[expose] noncomputable def mixtureJoint (mixingDensity : δ → NNReal)
    (componentDensity : δ × α → NNReal) (pair : α × δ) : NNReal :=
  NNReal.mul (mixingDensity pair.2) (componentDensity (pair.2, pair.1))

/-- A mixture's value density, `q(x) = ∫ m(u) k(u, x) ν_U(du)`. -/
@[expose] noncomputable def mixtureDensity (auxiliary : Measure extra)
    (mixingDensity : δ → NNReal) (componentDensity : δ × α → NNReal) (value : α) : ENNReal :=
  lintegral auxiliary fun other =>
    ENNReal.finite (mixtureJoint mixingDensity componentDensity (value, other))

theorem mixtureJoint_measurable {mixingDensity : δ → NNReal}
    {componentDensity : δ × α → NNReal}
    (mixingMeasurable : MeasurableMap extra weightSpace mixingDensity)
    (componentMeasurable : MeasurableMap (Space.product extra space) weightSpace
      componentDensity) :
    MeasurableMap (Space.product space extra) weightSpace
      (mixtureJoint mixingDensity componentDensity) :=
  weight_mul_measurable (MeasurableMap.comp mixingMeasurable (Space.second_measurable space extra))
    (MeasurableMap.comp componentMeasurable (Space.swap_measurable space extra))

/-- The value marginal of a mixture's swapped joint is the mixture. -/
theorem semiproduct_swap_marginal (mixing : Measure extra) (component : Kernel extra space)
    (componentFinite : Kernel.IsSFinite component) :
    ((mixing.semiproduct component componentFinite).map (fun pair => (pair.2, pair.1))
        (Space.swap_measurable extra space)).map Prod.fst (Space.first_measurable space extra) =
      mixing.bind component := by
  rw [Measure.map_comp, Measure.semiproduct, Measure.map_bind]
  refine congrArg (Measure.bind mixing) (Kernel.ext fun other => ?_)
  rw [Kernel.map_apply, Kernel.attach_apply, Measure.map_comp]
  exact Measure.map_id _

/-- A mixture's swapped joint has density `m(u) k(u, x)` against `ν ⊗ ν_U`. -/
theorem mixture_joint_eq {reference : Measure space} (referenceFinite : Measure.SFinite reference)
    {auxiliary : Measure extra} (auxiliaryFinite : Measure.SFinite auxiliary)
    {mixing : Measure extra} {mixingDensity : δ → NNReal}
    (mixingMeasurable : MeasurableMap extra weightSpace mixingDensity)
    (mixingEq : mixing = auxiliary.withDensity fun other => ENNReal.finite (mixingDensity other))
    {component : Kernel extra space} (componentFinite : Kernel.IsSFinite component)
    {componentDensity : δ × α → NNReal}
    (componentMeasurable : MeasurableMap (Space.product extra space) weightSpace
      componentDensity)
    (componentEq : ∀ other, component other =
      reference.withDensity fun value => ENNReal.finite (componentDensity (other, value))) :
    (mixing.semiproduct component componentFinite).map (fun pair => (pair.2, pair.1))
        (Space.swap_measurable extra space) =
      (Measure.prod reference auxiliary auxiliaryFinite).withDensity
        (fun pair => ENNReal.finite (mixtureJoint mixingDensity componentDensity pair)) := by
  subst mixingEq
  rw [joint_withDensity_swap referenceFinite auxiliaryFinite
    (finite_weight_measurable mixingMeasurable) component componentFinite
    (finite_weight_measurable componentMeasurable) componentEq]
  congr 1

/-- RAVI's forward answer for a mixture `Q = M.bind K`, from densities `m` of
`M` against `ν_U`, `k(u, ·)` of `K(u)` against `ν` and `r(x, ·)` of the meta
kernel `R(x)` against `ν_U`. The draw `(u, x)` from `M ⋉ K`, weighted by
`r(x, u) / (m(u) k(u, x))`, is properly weighted for `ν` restricted to where
`Q`'s density `q(x) = ∫ m(u) k(u, x) ν_U(du)` is positive, and `q` is a density
of `Q`. The support obligation `Q ⋉ R ≪ J`, with `J` the swapped joint, replaces
the pointwise condition "for `ν`-almost every `x` with `q(x) > 0`, `R(x)` puts
no mass where `m(u) k(u, x) = 0`". Their equivalence is not proven here. -/
theorem ravi_forward_mixture {reference : Measure space}
    (referenceFinite : Measure.SFinite reference)
    {auxiliary : Measure extra} (auxiliaryFinite : Measure.SFinite auxiliary)
    {mixing : Measure extra} {mixingDensity : δ → NNReal}
    (mixingMeasurable : MeasurableMap extra weightSpace mixingDensity)
    (mixingEq : mixing = auxiliary.withDensity fun other => ENNReal.finite (mixingDensity other))
    {component : Kernel extra space} (componentFinite : Kernel.IsSFinite component)
    {componentDensity : δ × α → NNReal}
    (componentMeasurable : MeasurableMap (Space.product extra space) weightSpace
      componentDensity)
    (componentEq : ∀ other, component other =
      reference.withDensity fun value => ENNReal.finite (componentDensity (other, value)))
    (probability : Measure.IsProbability (mixing.bind component))
    {metaKernel : Kernel space extra}
    (metaMarkov : ∀ value, Measure.IsProbability (metaKernel value))
    (metaFinite : Kernel.IsSFinite metaKernel) {metaDensity : α × δ → NNReal}
    (metaMeasurable : MeasurableMap (Space.product space extra) weightSpace metaDensity)
    (metaEq : ∀ value, metaKernel value =
      auxiliary.withDensity (fun other => ENNReal.finite (metaDensity (value, other))))
    (support : Measure.AbsolutelyContinuous
      ((mixing.bind component).semiproduct metaKernel metaFinite)
      ((mixing.semiproduct component componentFinite).map (fun pair => (pair.2, pair.1))
        (Space.swap_measurable extra space))) :
    Measure.IsDensity (mixing.bind component) reference
        (mixtureDensity auxiliary mixingDensity componentDensity) ∧
      ProperlyWeighted (reference.restrict fun value =>
          mixtureDensity auxiliary mixingDensity componentDensity value ≠ ENNReal.zero)
        ((mixing.semiproduct component componentFinite).map (fun pair =>
            (pair.2, raviWeight (mixtureJoint mixingDensity componentDensity) metaDensity
              (pair.2, pair.1)))
          (MeasurableMap.comp (Space.pair_measurable (Space.first_measurable space extra)
              (raviWeight_measurable (mixtureJoint_measurable mixingMeasurable
                componentMeasurable) metaMeasurable))
            (Space.swap_measurable extra space))) := by
  have jointMeasurable : MeasurableMap (Space.product space extra) weightSpace
      (mixtureJoint mixingDensity componentDensity) :=
    mixtureJoint_measurable mixingMeasurable componentMeasurable
  have marginal := semiproduct_swap_marginal mixing component componentFinite
  have jointEq := mixture_joint_eq referenceFinite auxiliaryFinite mixingMeasurable mixingEq
    componentFinite componentMeasurable componentEq
  have isDensity : Measure.IsDensity (mixing.bind component) reference
      (mixtureDensity auxiliary mixingDensity componentDensity) := by
    rw [Measure.IsDensity, ← marginal, jointEq,
      marginal_withDensity reference auxiliaryFinite (finite_weight_measurable jointMeasurable)]
    rfl
  have densityMeasurable : ENNRealMeasurable space
      (mixtureDensity auxiliary mixingDensity componentDensity) :=
    Kernel.lintegral_measurable_joint (Kernel.const space auxiliary)
      (Kernel.IsSFinite.const space auxiliaryFinite)
      (function := fun value other =>
        ENNReal.finite (mixtureJoint mixingDensity componentDensity (value, other)))
      (finite_weight_measurable jointMeasurable)
  have jointProbability : Measure.IsProbability ((mixing.semiproduct component
      componentFinite).map (fun pair => (pair.2, pair.1)) (Space.swap_measurable extra space)) := by
    refine ⟨?_⟩
    have total := Measure.map_apply ((mixing.semiproduct component componentFinite).map
      (fun pair => (pair.2, pair.1)) (Space.swap_measurable extra space)) Prod.fst
      (Space.first_measurable space extra) space.univ
    rw [Set.preimage_univ, marginal] at total
    rw [← total]
    exact probability.univ_eq_one
  refine ⟨isDensity, ?_⟩
  rw [← marginal] at isDensity support
  have properlyWeighted := ravi_forward_restricted auxiliaryFinite jointProbability jointMeasurable
    jointEq metaMarkov metaFinite metaMeasurable metaEq densityMeasurable isDensity support
  rw [Measure.map_comp] at properlyWeighted
  exact properlyWeighted

/-- RAVI's reverse answer for a mixture `Q = M.bind K`, from the same three
densities. The estimate `m(u) k(u, x) / r(x, u)`, read off a draw `u` from
`R(x)`, has a mean that is a density of `Q`. The support obligation
`J ≪ Q ⋉ R` replaces the pointwise condition "at `ν`-almost every `x`, the
fiber `u ↦ m(u) k(u, x)` is absolutely continuous with respect to `R(x)`".
Their equivalence is not proven here. -/
theorem ravi_reverse_mixture {reference : Measure space}
    (referenceFinite : Measure.SFinite reference)
    {auxiliary : Measure extra} (auxiliaryFinite : Measure.SFinite auxiliary)
    {mixing : Measure extra} {mixingDensity : δ → NNReal}
    (mixingMeasurable : MeasurableMap extra weightSpace mixingDensity)
    (mixingEq : mixing = auxiliary.withDensity fun other => ENNReal.finite (mixingDensity other))
    {component : Kernel extra space} (componentFinite : Kernel.IsSFinite component)
    {componentDensity : δ × α → NNReal}
    (componentMeasurable : MeasurableMap (Space.product extra space) weightSpace
      componentDensity)
    (componentEq : ∀ other, component other =
      reference.withDensity fun value => ENNReal.finite (componentDensity (other, value)))
    {metaKernel : Kernel space extra} (metaFinite : Kernel.IsSFinite metaKernel)
    {metaDensity : α × δ → NNReal}
    (metaMeasurable : MeasurableMap (Space.product space extra) weightSpace metaDensity)
    (metaEq : ∀ value, metaKernel value =
      auxiliary.withDensity (fun other => ENNReal.finite (metaDensity (value, other))))
    (support : Measure.AbsolutelyContinuous
      ((mixing.semiproduct component componentFinite).map (fun pair => (pair.2, pair.1))
        (Space.swap_measurable extra space))
      ((mixing.bind component).semiproduct metaKernel metaFinite)) :
    Measure.IsDensity (mixing.bind component) reference
      (fun value => lintegral (metaKernel value) fun other => ENNReal.finite
        (raviEstimate (mixtureJoint mixingDensity componentDensity) metaDensity
          (value, other))) := by
  have jointMeasurable : MeasurableMap (Space.product space extra) weightSpace
      (mixtureJoint mixingDensity componentDensity) :=
    mixtureJoint_measurable mixingMeasurable componentMeasurable
  have marginal := semiproduct_swap_marginal mixing component componentFinite
  have jointEq := mixture_joint_eq referenceFinite auxiliaryFinite mixingMeasurable mixingEq
    componentFinite componentMeasurable componentEq
  rw [← marginal] at support ⊢
  exact ravi_reverse_density auxiliaryFinite jointMeasurable jointEq metaFinite metaMeasurable
    metaEq support

end

end Problib.Inference
