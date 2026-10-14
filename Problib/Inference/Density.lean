module

public import Problib.Inference.Weighting
public import Problib.Measure.Kernel.Presentation.Fiber
public import Problib.Measure.Kernel.Density.Rules
public import Problib.Measure.Integral.Lebesgue.Discrete

set_option autoImplicit false

/-! Unbiased estimators of densities.

A density estimator is an `UnbiasedEstimate`: a probability kernel of finite
nonnegative estimates whose mean at every input is the density. The rules here
build estimators for the constructors of the density table, and every mean
equation holds pointwise in the whole input.

An estimated bind draws a properly weighted value and then an estimate
conditional on that value and its weight, and returns the product
(`unbiased_density_bind`). Conditioning on the value alone is not enough, and
`Problib.Inference.Necessity.Density` shows why. Exact factors scale an
estimate (`unbiased_density_score`, `unbiased_density_normalize`). A randomized
index estimates a countable sum (`unbiased_randomized_sum`), which gives the
superposition, loop and recursion rules together with their exact densities.
Independent factors multiply (`unbiased_density_product`), and a draw from a
probability fiber estimates a fiber density (`unbiased_density_fiber`). No rule
takes a ratio or a reciprocal of an estimate. -/

namespace Problib.Inference

open Problib.Real Problib.Measure

universe u v w
variable {α : Type u} {τ : Type v} {β : Type w}
  {source : Space α} {middle : Space τ} {target : Space β}

public section

/-- The extended value of a weight, as a measurable integrand. -/
theorem weight_value_measurable :
    ENNRealMeasurable weightSpace (fun weight : NNReal => ENNReal.finite weight) :=
  finite_weight_measurable (MeasurableMap.identity weightSpace)

/-- Scaling every estimate by an exact weight scales the mean. -/
theorem lintegral_scaled_weight (measure : Measure weightSpace) (factor : NNReal) :
    lintegral measure (fun weight => ENNReal.finite (NNReal.mul factor weight)) =
      ENNReal.mul (ENNReal.finite factor)
        (lintegral measure (fun weight => ENNReal.finite weight)) := by
  rw [← lintegral_smul measure (ENNReal.finite factor) weight_value_measurable]
  apply lintegral_congr
  intro weight
  exact (ENNReal.finite_mul_finite factor weight).symm

/-! ### The estimated bind -/

/-- The input of a conditional density estimator: the density's input and
point, then the previous weighted draw with its weight. -/
abbrev bindEstimateInput (source : Space α) (middle : Space τ)
    (target : Space β) : Space ((α × β) × (τ × NNReal)) :=
  Space.product (Space.product source target)
    (Space.product middle weightSpace)

/-- The previous weight times the conditional estimate. -/
theorem product_weight_measurable (source : Space α) (middle : Space τ)
    (target : Space β) :
    MeasurableMap
      (Space.product (bindEstimateInput source middle target) weightSpace)
      weightSpace (fun draw => NNReal.mul draw.1.2.2 draw.2) :=
  weight_mul_measurable
    (MeasurableMap.comp (Space.second_measurable middle weightSpace)
      (MeasurableMap.comp
        (Space.second_measurable (Space.product source target)
          (Space.product middle weightSpace))
        (Space.first_measurable (bindEstimateInput source middle target)
          weightSpace)))
    (Space.second_measurable (bindEstimateInput source middle target)
      weightSpace)

/-- Draw `(a, W)` at the input `γ`, then `e` given `((γ, y), (a, W))`, and
return `W·e`. The estimate's input keeps the weight. -/
@[expose] noncomputable def weightTimes
    (weighted : Kernel source (Space.product middle weightSpace))
    (weightedFinite : Kernel.IsSFinite weighted)
    (estimate : Kernel (bindEstimateInput source middle target) weightSpace)
    (estimateFinite : Kernel.IsSFinite estimate) :
    Kernel (Space.product source target) weightSpace :=
  ((weighted.precomp Prod.fst (Space.first_measurable source target)).attach
      (weightedFinite.precomp Prod.fst
        (Space.first_measurable source target))).comp
    ((estimate.attach estimateFinite).map
      (fun draw => NNReal.mul draw.1.2.2 draw.2)
      (product_weight_measurable source middle target))

/-- The mean of `W·e` is the weighted draw's integral of `W` times the
conditional mean. -/
theorem lintegral_weightTimes
    (weighted : Kernel source (Space.product middle weightSpace))
    (weightedFinite : Kernel.IsSFinite weighted)
    (estimate : Kernel (bindEstimateInput source middle target) weightSpace)
    (estimateFinite : Kernel.IsSFinite estimate) (pair : α × β) :
    lintegral (weightTimes weighted weightedFinite estimate estimateFinite pair)
        (fun weight => ENNReal.finite weight) =
      lintegral (weighted pair.1) (fun draw =>
        ENNReal.mul (drawWeight draw)
          (lintegral (estimate (pair, draw))
            (fun weight => ENNReal.finite weight))) := by
  rw [weightTimes, Kernel.lintegral_comp _ _ _ weight_value_measurable,
    Kernel.attach_apply, Kernel.precomp_apply,
    lintegral_map _ _ _ (Kernel.lintegral_measurable _ weight_value_measurable)]
  apply lintegral_congr
  intro draw
  rw [Kernel.map_apply, Kernel.attach_apply, Measure.map_comp,
    lintegral_map _ _ _ weight_value_measurable]
  exact lintegral_scaled_weight (estimate (pair, draw)) draw.2

theorem weightTimes_probability
    {weighted : Kernel source (Space.product middle weightSpace)}
    (weightedMarkov : ∀ input, Measure.IsProbability (weighted input))
    {estimate : Kernel (bindEstimateInput source middle target) weightSpace}
    (estimateMarkov : ∀ input, Measure.IsProbability (estimate input))
    (pair : α × β) :
    Measure.IsProbability (weightTimes weighted
      (Kernel.IsSFinite.ofMarkov weightedMarkov) estimate
      (Kernel.IsSFinite.ofMarkov estimateMarkov) pair) := by
  rw [weightTimes, Kernel.comp_apply]
  refine Measure.IsProbability.bind ?_ _ fun draw => ?_
  · rw [Kernel.attach_apply, Kernel.precomp_apply]
    exact (weightedMarkov pair.1).map _ _
  · rw [Kernel.map_apply, Kernel.attach_apply]
    exact ((estimateMarkov draw).map _ _).map _ _

/-- The estimated bind rule. The estimate is unbiased for `b` given the whole
weighted draw `(a, W)`, and proper weighting then integrates the draw out:
`E[W·e] = E[W·b(a, y)] = ∫ b(a, y) A(da)`. -/
theorem unbiased_density_bind
    {A : Kernel source middle}
    {weighted : Kernel source (Space.product middle weightSpace)}
    (properlyWeighted : ∀ input, ProperlyWeighted (A input) (weighted input))
    {b : α × τ → β → ENNReal}
    {estimate : Kernel (bindEstimateInput source middle target) weightSpace}
    (unbiased : UnbiasedEstimate (fun q => b (q.1.1, q.2.1) q.1.2) estimate) :
    UnbiasedEstimate
      (fun pair : α × β => lintegral (A pair.1)
        (fun value => b (pair.1, value) pair.2))
      (weightTimes weighted
        (Kernel.IsSFinite.ofMarkov fun input => (properlyWeighted input).probability)
        estimate (Kernel.IsSFinite.ofMarkov unbiased.probability)) := by
  refine ⟨weightTimes_probability (fun input => (properlyWeighted input).probability)
    unbiased.probability, fun pair => ?_⟩
  have sliceMap : MeasurableMap middle (bindEstimateInput source middle target)
      (fun value => (pair, (value, NNReal.zero))) :=
    Space.pair_measurable (MeasurableMap.constant middle _ pair)
      (Space.pair_measurable (MeasurableMap.identity middle)
        (MeasurableMap.constant middle weightSpace NNReal.zero))
  have slice : ENNRealMeasurable middle
      (fun value => b (pair.1, value) pair.2) :=
    unbiased.mean_measurable.comp sliceMap
  rw [lintegral_weightTimes, ← (properlyWeighted pair.1).lintegral slice]
  apply lintegral_congr
  intro draw
  rw [unbiased.mean_eq (pair, draw)]

/-! ### Exact factors -/

/-- An exact factor of the input times the estimate. -/
theorem scaled_weight_measurable {space : Space α} {factor : α → NNReal}
    (factorMeasurable : MeasurableMap space weightSpace factor) :
    MeasurableMap (Space.product space weightSpace) weightSpace
      (fun draw => NNReal.mul (factor draw.1) draw.2) :=
  weight_mul_measurable
    (MeasurableMap.comp factorMeasurable
      (Space.first_measurable space weightSpace))
    (Space.second_measurable space weightSpace)

/-- Scale every sampled estimate by an exact finite factor of the input. -/
@[expose] noncomputable def scaleEstimate {space : Space α}
    (estimate : Kernel space weightSpace)
    (estimateFinite : Kernel.IsSFinite estimate)
    (factor : α → NNReal)
    (factorMeasurable : MeasurableMap space weightSpace factor) :
    Kernel space weightSpace :=
  (estimate.attach estimateFinite).map
    (fun draw => NNReal.mul (factor draw.1) draw.2)
    (scaled_weight_measurable factorMeasurable)

/-- An exact score scales an unbiased density estimate. The factor order is
`density_score`'s. -/
theorem unbiased_density_score {space : Space α}
    {p : α → ENNReal} {estimate : Kernel space weightSpace}
    (unbiased : UnbiasedEstimate p estimate)
    (factor : α → NNReal)
    (factorMeasurable : MeasurableMap space weightSpace factor) :
    UnbiasedEstimate
      (fun input => ENNReal.mul (p input) (ENNReal.finite (factor input)))
      (scaleEstimate estimate
        (Kernel.IsSFinite.ofMarkov unbiased.probability)
        factor factorMeasurable) := by
  refine ⟨fun input => ?_, fun input => ?_⟩
  · rw [scaleEstimate, Kernel.map_apply _ _ (scaled_weight_measurable factorMeasurable),
      Kernel.attach_apply]
    exact ((unbiased.probability input).map _ _).map _ _
  · rw [scaleEstimate, Kernel.map_apply _ _ (scaled_weight_measurable factorMeasurable),
      Kernel.attach_apply, Measure.map_comp,
      lintegral_map _ _ _ weight_value_measurable]
    dsimp only
    rw [lintegral_scaled_weight, unbiased.mean_eq input, ENNReal.mul_comm]

/-- Normalizing divides by the exact evidence mass `Z`, which is scoring by its
reciprocal. The mean is `density_normalize`'s density. The rule admits no
estimated denominator. -/
theorem unbiased_density_normalize {space : Space α}
    {p : α → ENNReal} {estimate : Kernel space weightSpace}
    (unbiased : UnbiasedEstimate p estimate) (Z : NNReal) :
    UnbiasedEstimate
      (fun input => ENNReal.mul (p input)
        (ENNReal.finite (NNReal.div NNReal.one Z)))
      (scaleEstimate estimate
        (Kernel.IsSFinite.ofMarkov unbiased.probability)
        (fun _ => NNReal.div NNReal.one Z)
        (MeasurableMap.constant space weightSpace _)) :=
  unbiased_density_score unbiased _ _

/-! ### Randomized sums -/

/-- Scaling a term's estimate by the reciprocal of its index's probability. -/
theorem reciprocal_weight_measurable (space : Space α) (q : Nat → NNReal) :
    MeasurableMap
      (Space.product (Space.product space (Space.discrete Nat)) weightSpace)
      weightSpace
      (fun draw => NNReal.mul (NNReal.div NNReal.one (q draw.1.2)) draw.2) :=
  weight_mul_measurable
    (MeasurableMap.comp
      (MeasurableMap.from_discrete weightSpace (fun index => NNReal.div NNReal.one (q index)))
      (MeasurableMap.comp (Space.second_measurable space (Space.discrete Nat))
        (Space.first_measurable (Space.product space (Space.discrete Nat))
          weightSpace)))
    (Space.second_measurable (Space.product space (Space.discrete Nat))
      weightSpace)

/-- Draw an index `n`, then one estimate of term `n`, and divide it by the
exact probability `q n` of drawing `n`. -/
@[expose] noncomputable def randomizedSumEstimate {space : Space α}
    (index : Measure (Space.discrete Nat)) (indexFinite : Measure.SFinite index)
    (q : Nat → NNReal)
    (term : Kernel (Space.product space (Space.discrete Nat)) weightSpace)
    (termFinite : Kernel.IsSFinite term) : Kernel space weightSpace :=
  ((Kernel.const space index).attach
      (Kernel.IsSFinite.const space indexFinite)).comp
    ((term.attach termFinite).map
      (fun draw => NNReal.mul (NNReal.div NNReal.one (q draw.1.2)) draw.2)
      (reciprocal_weight_measurable space q))

/-- A randomized index estimates a countable sum without bias. The index's
singleton masses are the exact `q`, and a term that can be nonzero has a
nonzero chance of being drawn. -/
theorem unbiased_randomized_sum {space : Space α}
    (d : Nat → α → ENNReal)
    {index : Measure (Space.discrete Nat)}
    (indexProbability : Measure.IsProbability index)
    {q : Nat → NNReal}
    (indexMass : ∀ n, index (Set.singleton n) = ENNReal.finite (q n))
    (support : ∀ n input, d n input ≠ ENNReal.zero → q n ≠ NNReal.zero)
    {term : Kernel (Space.product space (Space.discrete Nat)) weightSpace}
    (termUnbiased : UnbiasedEstimate (fun draw => d draw.2 draw.1) term) :
    UnbiasedEstimate (fun input => ENNReal.tsum (fun n => d n input))
      (randomizedSumEstimate index
        (Measure.SFinite.ofFinite indexProbability.to_finite) q term
        (Kernel.IsSFinite.ofMarkov termUnbiased.probability)) := by
  refine ⟨fun input => ?_, fun input => ?_⟩
  · rw [randomizedSumEstimate, Kernel.comp_apply]
    refine Measure.IsProbability.bind ?_ _ fun draw => ?_
    · rw [Kernel.attach_apply, Kernel.const_apply]
      exact indexProbability.map _ _
    · rw [Kernel.map_apply, Kernel.attach_apply]
      exact ((termUnbiased.probability draw).map _ _).map _ _
  · rw [randomizedSumEstimate, Kernel.lintegral_comp _ _ _ weight_value_measurable,
      Kernel.attach_apply, Kernel.const_apply,
      lintegral_map _ _ _ (Kernel.lintegral_measurable _ weight_value_measurable),
      lintegral_discrete]
    apply ENNReal.tsum_congr
    intro n
    rw [Kernel.map_apply, Kernel.attach_apply, Measure.map_comp,
      lintegral_map _ _ _ weight_value_measurable]
    dsimp only
    rw [lintegral_scaled_weight, termUnbiased.mean_eq (input, n), indexMass n]
    show ENNReal.mul (ENNReal.mul (ENNReal.finite (NNReal.div NNReal.one (q n)))
      (d n input)) (ENNReal.finite (q n)) = d n input
    by_cases vanishes : d n input = ENNReal.zero
    · rw [vanishes, ENNReal.mul_zero, ENNReal.zero_mul]
    · rw [ENNReal.mul_comm, ← ENNReal.mul_assoc, ENNReal.finite_mul_finite,
        NNReal.mul_div_cancel _ (support n input vanishes)]
      exact ENNReal.one_mul _

/-- The pointwise slice of a term's mean at one index and input. -/
theorem term_slice_measurable {α' : Type u} {space : Space α'}
    (point : Space β) {d : Nat → α' → β → ENNReal}
    {term : Kernel (Space.product (Space.product space point) (Space.discrete Nat))
      weightSpace}
    (termUnbiased : UnbiasedEstimate (fun draw => d draw.2 draw.1.1 draw.1.2) term)
    (n : Nat) (input : α') : ENNRealMeasurable point (d n input) :=
  termUnbiased.mean_measurable.comp
    (Space.pair_measurable
      (Space.pair_measurable (MeasurableMap.constant point space input)
        (MeasurableMap.identity point))
      (MeasurableMap.constant point (Space.discrete Nat) n))

/-- Countable superposition: an estimate of a randomly drawn arm's density is
unbiased for the density of the superposed kernel. -/
theorem unbiased_density_superpose
    {μ : Nat → Kernel source target} {ν : Kernel source target}
    {p : Nat → α → β → ENNReal}
    (reconstruct : ∀ n input, Measure.IsDensity (μ n input) (ν input) (p n input))
    {index : Measure (Space.discrete Nat)}
    (indexProbability : Measure.IsProbability index)
    {q : Nat → NNReal}
    (indexMass : ∀ n, index (Set.singleton n) = ENNReal.finite (q n))
    (support : ∀ n input y, p n input y ≠ ENNReal.zero → q n ≠ NNReal.zero)
    {term : Kernel (Space.product (Space.product source target) (Space.discrete Nat))
      weightSpace}
    (termUnbiased : UnbiasedEstimate (fun draw => p draw.2 draw.1.1 draw.1.2) term) :
    (∀ input, Measure.IsDensity (Measure.sum fun n => μ n input) (ν input)
        (fun y => ENNReal.tsum (fun n => p n input y))) ∧
      UnbiasedEstimate (fun pair => ENNReal.tsum (fun n => p n pair.1 pair.2))
        (randomizedSumEstimate index
          (Measure.SFinite.ofFinite indexProbability.to_finite) q term
          (Kernel.IsSFinite.ofMarkov termUnbiased.probability)) :=
  ⟨fun input => Kernel.density_superpose (ν input) (fun n => μ n input)
      (fun n => p n input) (fun n => term_slice_measurable target termUnbiased n input)
      (fun n => reconstruct n input),
    unbiased_randomized_sum (fun n (pair : α × β) => p n pair.1 pair.2)
      indexProbability indexMass (fun n (pair : α × β) => support n pair.1 pair.2)
      termUnbiased⟩

/-- A loop's exit paths, indexed by their number of retries, estimate the
loop's exact density `densityLoop` without bias. -/
theorem unbiased_densityLoop
    {Q : Kernel source source} {R : Kernel source target}
    {QFinite : Kernel.IsSFinite Q}
    {ν : Measure target} {νFinite : Measure.SFinite ν}
    {exitReconstruct : Kernel.RadonNikodymDerivative R (Kernel.const source ν)}
    {index : Measure (Space.discrete Nat)}
    (indexProbability : Measure.IsProbability index)
    {q : Nat → NNReal}
    (indexMass : ∀ n, index (Set.singleton n) = ENNReal.finite (q n))
    (support : ∀ n input y, lintegral ((Kernel.iterate Q n) input)
        (fun z => exitReconstruct.density z y) ≠ ENNReal.zero → q n ≠ NNReal.zero)
    {path : Kernel (Space.product (Space.product source target) (Space.discrete Nat))
      weightSpace}
    (pathUnbiased : UnbiasedEstimate (fun draw =>
      lintegral ((Kernel.iterate Q draw.2) draw.1.1)
        (fun z => exitReconstruct.density z draw.1.2)) path) :
    UnbiasedEstimate
      (fun pair => (Kernel.densityLoop Q R QFinite ν νFinite exitReconstruct).density
        pair.1 pair.2)
      (randomizedSumEstimate index
        (Measure.SFinite.ofFinite indexProbability.to_finite) q path
        (Kernel.IsSFinite.ofMarkov pathUnbiased.probability)) := by
  rw [Kernel.densityLoop_density]
  exact unbiased_randomized_sum
    (fun n (pair : α × β) => lintegral ((Kernel.iterate Q n) pair.1)
      (fun z => exitReconstruct.density z pair.2))
    indexProbability indexMass (fun n (pair : α × β) => support n pair.1 pair.2)
    pathUnbiased

/-- A recursion measured through its increments: an estimate of a randomly
drawn increment's density is unbiased for the recursion's density. The Church
recursion case waits on G8. -/
theorem unbiased_density_recur_of_increments
    {μ ν : Kernel source target} {increment : Nat → Kernel source target}
    {incrementDensity : Nat → α → β → ENNReal}
    (sumEq : ∀ input, μ input = Measure.sum fun n => increment n input)
    (reconstruct : ∀ n input,
      Measure.IsDensity (increment n input) (ν input) (incrementDensity n input))
    {index : Measure (Space.discrete Nat)}
    (indexProbability : Measure.IsProbability index)
    {q : Nat → NNReal}
    (indexMass : ∀ n, index (Set.singleton n) = ENNReal.finite (q n))
    (support : ∀ n input y,
      incrementDensity n input y ≠ ENNReal.zero → q n ≠ NNReal.zero)
    {term : Kernel (Space.product (Space.product source target) (Space.discrete Nat))
      weightSpace}
    (termUnbiased : UnbiasedEstimate
      (fun draw => incrementDensity draw.2 draw.1.1 draw.1.2) term) :
    (∀ input, Measure.IsDensity (μ input) (ν input)
        (fun y => ENNReal.tsum (fun n => incrementDensity n input y))) ∧
      UnbiasedEstimate
        (fun pair => ENNReal.tsum (fun n => incrementDensity n pair.1 pair.2))
        (randomizedSumEstimate index
          (Measure.SFinite.ofFinite indexProbability.to_finite) q term
          (Kernel.IsSFinite.ofMarkov termUnbiased.probability)) :=
  ⟨fun input => Kernel.density_recur_of_increments (μ input) (ν input)
      (fun n => increment n input) (fun n => incrementDensity n input) (sumEq input)
      (fun n => term_slice_measurable target termUnbiased n input)
      (fun n => reconstruct n input),
    unbiased_randomized_sum (fun n (pair : α × β) => incrementDensity n pair.1 pair.2)
      indexProbability indexMass (fun n (pair : α × β) => support n pair.1 pair.2)
      termUnbiased⟩

/-! ### Products and fibers -/

/-- The left estimate times the right estimate. -/
theorem pair_weight_measurable (space : Space α) :
    MeasurableMap
      (Space.product (Space.product space weightSpace) weightSpace) weightSpace
      (fun draw => NNReal.mul draw.1.2 draw.2) :=
  weight_mul_measurable
    (MeasurableMap.comp (Space.second_measurable space weightSpace)
      (Space.first_measurable (Space.product space weightSpace) weightSpace))
    (Space.second_measurable (Space.product space weightSpace) weightSpace)

/-- Draw the left estimate, then the right estimate at the same input, and
return their product. The right draw does not read the left one, so the two are
conditionally independent given the input. -/
@[expose] noncomputable def independentProductEstimate {space : Space α}
    (left right : Kernel space weightSpace)
    (leftFinite : Kernel.IsSFinite left)
    (rightFinite : Kernel.IsSFinite right) : Kernel space weightSpace :=
  ((left.attach leftFinite).comp
      ((right.precomp Prod.fst (Space.first_measurable space weightSpace)).attach
        (rightFinite.precomp Prod.fst
          (Space.first_measurable space weightSpace)))).map
    (fun draw => NNReal.mul draw.1.2 draw.2) (pair_weight_measurable space)

/-- Conditionally independent factors have the product of their means. -/
theorem unbiased_density_product {space : Space α}
    {leftMean rightMean : α → ENNReal}
    {left right : Kernel space weightSpace}
    (leftUnbiased : UnbiasedEstimate leftMean left)
    (rightUnbiased : UnbiasedEstimate rightMean right) :
    UnbiasedEstimate
      (fun input => ENNReal.mul (leftMean input) (rightMean input))
      (independentProductEstimate left right
        (Kernel.IsSFinite.ofMarkov leftUnbiased.probability)
        (Kernel.IsSFinite.ofMarkov rightUnbiased.probability)) := by
  refine ⟨fun input => ?_, fun input => ?_⟩
  · rw [independentProductEstimate, Kernel.map_apply, Kernel.comp_apply]
    refine (Measure.IsProbability.bind ?_ _ fun draw => ?_).map _ _
    · rw [Kernel.attach_apply]
      exact (leftUnbiased.probability input).map _ _
    · rw [Kernel.attach_apply, Kernel.precomp_apply]
      exact (rightUnbiased.probability draw.1).map _ _
  · rw [independentProductEstimate, Kernel.map_apply,
      lintegral_map _ _ _ weight_value_measurable,
      Kernel.lintegral_comp _ _ _
        (finite_weight_measurable (pair_weight_measurable space)),
      Kernel.attach_apply,
      lintegral_map _ _ _ (Kernel.lintegral_measurable _
        (finite_weight_measurable (pair_weight_measurable space)))]
    have inner : ∀ weight : NNReal,
        lintegral (((right.precomp Prod.fst
            (Space.first_measurable space weightSpace)).attach
            (Kernel.IsSFinite.precomp
              (Kernel.IsSFinite.ofMarkov rightUnbiased.probability) Prod.fst
              (Space.first_measurable space weightSpace))) (input, weight))
          (fun draw => ENNReal.finite (NNReal.mul draw.1.2 draw.2)) =
        ENNReal.mul (rightMean input) (ENNReal.finite weight) := by
      intro weight
      rw [Kernel.attach_apply, Kernel.precomp_apply,
        lintegral_map _ _ _ (finite_weight_measurable (pair_weight_measurable space))]
      rw [lintegral_scaled_weight, rightUnbiased.mean_eq input, ENNReal.mul_comm]
    rw [lintegral_congr _ (fun weight => inner weight),
      lintegral_smul _ _ weight_value_measurable, leftUnbiased.mean_eq input,
      ENNReal.mul_comm]

/-- A fiber draw's reference change `h` times its trace density `p`. -/
theorem fiber_weight_measurable
    {p : α → τ → NNReal} {h : α → β → NNReal}
    (pMeasurable : MeasurableMap (Space.product source middle)
      weightSpace (fun pair => p pair.1 pair.2))
    (hMeasurable : MeasurableMap (Space.product source target)
      weightSpace (fun pair => h pair.1 pair.2)) :
    MeasurableMap (Space.product (Space.product source target) middle)
      weightSpace (fun draw => NNReal.mul (h draw.1.1 draw.1.2) (p draw.1.1 draw.2)) :=
  weight_mul_measurable
    (MeasurableMap.comp hMeasurable
      (Space.first_measurable (Space.product source target) middle))
    (MeasurableMap.comp pMeasurable
      (Space.pair_measurable
        (MeasurableMap.comp (Space.first_measurable source target)
          (Space.first_measurable (Space.product source target) middle))
        (Space.second_measurable (Space.product source target) middle)))

/-- Draw a trace from the fiber over `(γ, y)` and return the exact reference
change times the trace density there. -/
@[expose] noncomputable def fiberEstimate
    {reference : Kernel source middle}
    {ret : α × τ → β}
    {retMeasurable : MeasurableMap (Space.product source middle) target ret}
    (fiber : Kernel.FiberReference reference retMeasurable)
    (p : α → τ → NNReal) (h : α → β → NNReal)
    (pMeasurable : MeasurableMap (Space.product source middle)
      weightSpace (fun pair => p pair.1 pair.2))
    (hMeasurable : MeasurableMap (Space.product source target)
      weightSpace (fun pair => h pair.1 pair.2)) :
    Kernel (Space.product source target) weightSpace :=
  (fiber.conditional.attach fiber.conditionalSFinite).map
    (fun draw => NNReal.mul (h draw.1.1 draw.1.2) (p draw.1.1 draw.2))
    (fiber_weight_measurable pMeasurable hMeasurable)

/-- Sampling the fiber estimates the fiber density without bias. The fibers
must be probabilities, which `density_map_of_fiber` does not need. The factor
order is `density_reference_change`'s. -/
theorem unbiased_density_fiber
    {reference : Kernel source middle}
    {ret : α × τ → β}
    {retMeasurable : MeasurableMap (Space.product source middle) target ret}
    (fiber : Kernel.FiberReference reference retMeasurable)
    (fiberMarkov : fiber.IsMarkov)
    (p : α → τ → NNReal) (h : α → β → NNReal)
    (pMeasurable : MeasurableMap (Space.product source middle)
      weightSpace (fun pair => p pair.1 pair.2))
    (hMeasurable : MeasurableMap (Space.product source target)
      weightSpace (fun pair => h pair.1 pair.2)) :
    UnbiasedEstimate
      (fun pair => ENNReal.mul (ENNReal.finite (h pair.1 pair.2))
        (Kernel.fiberDensity fiber
          (fun input point => ENNReal.finite (p input point)) pair.1 pair.2))
      (fiberEstimate fiber p h pMeasurable hMeasurable) := by
  refine ⟨fun pair => ?_, fun pair => ?_⟩
  · rw [fiberEstimate,
      Kernel.map_apply _ _ (fiber_weight_measurable pMeasurable hMeasurable),
      Kernel.attach_apply]
    exact ((fiberMarkov pair).map _ _).map _ _
  · rw [fiberEstimate,
      Kernel.map_apply _ _ (fiber_weight_measurable pMeasurable hMeasurable),
      Kernel.attach_apply, Measure.map_comp,
      lintegral_map _ _ _ weight_value_measurable]
    simp only [Kernel.fiberDensity]
    have lifted : ENNRealMeasurable middle
        (fun point => ENNReal.finite (p pair.1 point)) :=
      finite_weight_measurable
        (MeasurableMap.comp pMeasurable
          (Space.pair_measurable (MeasurableMap.constant middle source pair.1)
            (MeasurableMap.identity middle)))
    rw [← lintegral_smul _ _ lifted]
    apply lintegral_congr
    intro point
    exact (ENNReal.finite_mul_finite _ _).symm

end

end Problib.Inference
