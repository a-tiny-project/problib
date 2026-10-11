module

public import Problib.Analysis.Exponential
public import Problib.Measure.Real.Simplex
public import Problib.Algebra.Product
public import Problib.Measure.Kernel.Density.Conditional
public import Problib.Measure.Kernel.Density.Normalized
import Problib.Measure.Integral.Density.Algebra

/-! Exponential families and their conjugate priors.

An exponential family with `k` statistics has densities
`h(x) exp(⟨η(θ), T(x)⟩ - A(θ))` (`likelihood`). The base `h` is finite, the
statistic `T` sends an observation to `Fin k → ℝ`, and the natural parameter `η`
and the log-partition `A` are functions of the parameter. All four are
measurable.

Evidence is a pair `(χ, ν)`: a sum of statistics and the number of observations
behind it. The conjugate weight of evidence is `exp(⟨η(θ), χ⟩ - νA(θ))`
(`weight`), and a conjugate prior weights a reference measure on the parameters
by it, so its hyperparameters are pseudo-observations. Evidence adds
componentwise, and the weight turns that addition into multiplication
(`weight_add`). One observation `x` is the evidence `(T(x), 1)`
(`observation`), and its likelihood is `h(x)` times that evidence's weight
(`likelihood_eq`). A batch likelihood is the product of the bases times the
weight of the summed evidence (`listProduct_likelihood_eq`).

Given observations `x₁ … x_N` with nonzero bases, the posterior of the prior at
`(χ, ν)` is the conjugate kernel at `(χ + ΣT(xⱼ), ν + N)` (`posterior`). The
data enter only through their summed evidence, the list sum at the evidence laws
(`Evidence.laws`), so concatenation adds and order does not matter. The update
is therefore an action of the additive monoid of evidence (`update_nil`,
`update_append`), and every order, grouping or parallel reduction of the batch
gives the same posterior (`posterior_perm`, `posterior_append`). The marginal
density of the batch is its base product times the mass of the updated weight
(`densityMass_joint`).

The conjugate kernel is the law of a normalized family over evidence
(`conjugateFamily`, `conjugate_eq_law`), whose normalizer `Z(e)` is the mass of
the weight at `e`. Under the prior at `e` with `Z(e)` finite and nonzero, the
marginal likelihood `m` of a batch satisfies `Z(e)·m = ∏h(xⱼ)·Z(e + Σ)`
(`normalizer_mul_marginal`), so `m` is the normalizer ratio
`∏h(xⱼ)·Z(e + Σ)/Z(e)`. The one-step predictive density of `x` at evidence `e`
is `h(x)·Z(e + (T(x), 1))/Z(e)` (`normalizer_mul_predictive`). Where
`Z(e + Σ)` is infinite the marginal is infinite, and the ratio is no density
(`marginal_eq_top`).

The conjugate kernel (`conjugate`) normalizes the weighted reference at each
evidence and falls back to a Dirac measure where the weighted reference has
zero or infinite mass. The flat evidence `(0, 0)` has weight one, so against a
reference of infinite mass a flat prior with no observations has no
normalization (`flat_not_normalizable`, `conjugate_flat`).

An instance names its conjugate law by showing that the weighted reference is a
finite nonzero multiple of a probability law (`conjugate_eq_of_smul`). The
Gaussian with known variance, the Poisson with its Gamma prior and the
categorical with its Dirichlet prior are the instances in `ExponentialFamily/`.
-/

set_option autoImplicit false

open scoped Problib.Real.AC

namespace Problib.Analysis

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction Problib.Real.Construction.Dedekind

noncomputable section

universe u v w

/-- An exponential family with `statistics` statistics: densities
`h(x) exp(⟨η(θ), T(x)⟩ - A(θ))` of observations `x` at parameters `θ`, with
measurable components. -/
public structure ExponentialFamily {Observation : Type u} {Parameter : Type v}
    (observations : Space Observation) (parameters : Space Parameter) (statistics : Nat) where
  /-- The base density `h`, finite by type. -/
  base : Observation → NNReal
  /-- The sufficient statistic `T`. -/
  statistic : Observation → Fin statistics → Carrier
  /-- The natural parameter `η`. -/
  natural : Parameter → Fin statistics → Carrier
  /-- The log-partition `A`. -/
  logPartition : Parameter → Carrier
  base_measurable : ENNRealMeasurable observations (fun value => ENNReal.finite (base value))
  statistic_measurable : ∀ index,
    MeasurableMap observations borel (fun value => statistic value index)
  natural_measurable : ∀ index,
    MeasurableMap parameters borel (fun parameter => natural parameter index)
  logPartition_measurable : MeasurableMap parameters borel logPartition

namespace ExponentialFamily

variable {Observation : Type u} {Parameter : Type v} {observations : Space Observation}
  {parameters : Space Parameter} {statistics : Nat}

/-! ### Evidence -/

/-- Evidence: a sum of statistics and the number of observations behind it. A
conjugate prior's hyperparameters are evidence read as pseudo-observations, so
both components are real. -/
public abbrev Evidence (statistics : Nat) : Type := (Fin statistics → Carrier) × Carrier

/-- The measurable space of evidence. -/
public abbrev Evidence.space (statistics : Nat) : Space (Evidence statistics) :=
  Space.product (Space.pi (fun _ : Fin statistics => borel)) borel

/-- Evidence adds componentwise. -/
@[expose] public def Evidence.add (first second : Evidence statistics) : Evidence statistics :=
  (fun index => Dedekind.add (first.1 index) (second.1 index), Dedekind.add first.2 second.2)

/-- The empty evidence: no statistics and no count. -/
@[expose] public def Evidence.zero : Evidence statistics :=
  (fun _ => Dedekind.zero, Dedekind.zero)

public theorem Evidence.add_assoc (first second third : Evidence statistics) :
    Evidence.add (Evidence.add first second) third =
      Evidence.add first (Evidence.add second third) :=
  Prod.ext (funext fun _ => Dedekind.add_assoc _ _ _) (Dedekind.add_assoc _ _ _)

public theorem Evidence.add_comm (first second : Evidence statistics) :
    Evidence.add first second = Evidence.add second first :=
  Prod.ext (funext fun _ => Dedekind.add_comm _ _) (Dedekind.add_comm _ _)

public theorem Evidence.add_left_comm (first second third : Evidence statistics) :
    Evidence.add first (Evidence.add second third) =
      Evidence.add second (Evidence.add first third) :=
  Prod.ext (funext fun _ => Dedekind.add_left_comm _ _ _) (Dedekind.add_left_comm _ _ _)

public theorem Evidence.add_zero (evidence : Evidence statistics) :
    Evidence.add evidence Evidence.zero = evidence :=
  Prod.ext (funext fun _ => Dedekind.add_zero _) (Dedekind.add_zero _)

public theorem Evidence.zero_add (evidence : Evidence statistics) :
    Evidence.add Evidence.zero evidence = evidence :=
  (Evidence.add_comm _ _).trans (Evidence.add_zero evidence)

/-- Evidence is a commutative monoid under componentwise addition, and summed
evidence is the list sum at these laws. -/
@[expose, reducible] public def Evidence.laws :
    Problib.Algebra.AdditiveCommutativeMonoidLaws (Evidence statistics) where
  zero := Evidence.zero
  add := Evidence.add
  add_comm := Evidence.add_comm
  add_assoc := Evidence.add_assoc
  add_zero := Evidence.add_zero

/-- Adding two measurable evidence maps is measurable. -/
public theorem Evidence.add_measurable {Input : Type w} {source : Space Input}
    {first second : Input → Evidence statistics}
    (firstMeasurable : MeasurableMap source (Evidence.space statistics) first)
    (secondMeasurable : MeasurableMap source (Evidence.space statistics) second) :
    MeasurableMap source (Evidence.space statistics)
      (fun input => Evidence.add (first input) (second input)) := by
  have totals (evidence : Input → Evidence statistics)
      (measurable : MeasurableMap source (Evidence.space statistics) evidence)
      (index : Fin statistics) :
      MeasurableMap source borel (fun input => (evidence input).1 index) :=
    MeasurableMap.comp (Space.coordinate_measurable (fun _ : Fin statistics => borel) index)
      (MeasurableMap.comp (Space.first_measurable _ _) measurable)
  show MeasurableMap source (Space.product (Space.pi (fun _ : Fin statistics => borel)) borel)
    (fun input => (fun index => Dedekind.add ((first input).1 index) ((second input).1 index),
      Dedekind.add (first input).2 (second input).2))
  exact Space.pair_measurable
    (Space.pi_measurable (fun index =>
      measurable_add (totals first firstMeasurable index) (totals second secondMeasurable index)))
    (measurable_add (MeasurableMap.comp (Space.second_measurable _ _) firstMeasurable)
      (MeasurableMap.comp (Space.second_measurable _ _) secondMeasurable))

/-! ### The pairing -/

/-- The pairing `⟨a, b⟩ = Σᵢ aᵢbᵢ` of two real vectors. -/
@[expose] public def pairing (statistics : Nat) (first second : Fin statistics → Carrier) :
    Carrier :=
  Dedekind.additiveLaws.finSum statistics (fun index => mul (first index) (second index))

/-- The pairing is additive in its second argument. -/
public theorem pairing_add_right (statistics : Nat)
    (natural first second : Fin statistics → Carrier) :
    pairing statistics natural (fun index => add (first index) (second index)) =
      add (pairing statistics natural first) (pairing statistics natural second) :=
  (Dedekind.additiveLaws.finSum_congr statistics fun _ => mul_add _ _ _).trans
    (Dedekind.additiveLaws.finSum_add statistics _ _)

public theorem pairing_zero_right (statistics : Nat) (natural : Fin statistics → Carrier) :
    pairing statistics natural (fun _ => zero) = zero :=
  (Dedekind.additiveLaws.finSum_congr statistics fun _ => mul_zero _).trans
    (Dedekind.additiveLaws.finSum_const_zero statistics)

/-- With one statistic the pairing is a product. -/
public theorem pairing_one (natural total : Fin 1 → Carrier) :
    pairing 1 natural total = mul (natural 0) (total 0) :=
  add_zero _

variable (family : ExponentialFamily observations parameters statistics)

/-! ### Observations as evidence -/

/-- The evidence of one observation: its statistic, counted once. -/
@[expose] public def observation (value : Observation) : Evidence statistics :=
  (family.statistic value, one)

public theorem observation_measurable :
    MeasurableMap observations (Evidence.space statistics)
      (fun value => family.observation value) :=
  Space.pair_measurable (Space.pi_measurable family.statistic_measurable)
    (MeasurableMap.constant observations borel one)

/-- The count of summed evidence is nonnegative. -/
public theorem listSum_observation_count_nonnegative : (data : List Observation) →
    le zero (Evidence.laws.listSum (data.map family.observation)).2
  | [] => le_refl zero
  | _ :: rest => add_nonnegative one_nonnegative (listSum_observation_count_nonnegative rest)

/-- The count of summed evidence is the number of observations. -/
public theorem listSum_observation_count : (data : List Observation) →
    (Evidence.laws.listSum (data.map family.observation)).2 = selection.ofRat (data.length : Rat)
  | [] => by
      show zero = selection.ofRat ((0 : Nat) : Rat)
      rw [show ((0 : Nat) : Rat) = 0 from rfl, ofRat_zero]
  | _ :: rest => by
      show add one (Evidence.laws.listSum (rest.map family.observation)).2 =
        selection.ofRat ((rest.length + 1 : Nat) : Rat)
      rw [listSum_observation_count rest, Rat.natCast_add, show ((1 : Nat) : Rat) = 1 from rfl,
        ofRat_add,
        ofRat_one, add_comm]

/-- Nonnegative statistics have nonnegative sums. -/
public theorem listSum_observation_statistic_nonnegative
    (nonnegative : ∀ value index, le zero (family.statistic value index)) :
    (data : List Observation) → (index : Fin statistics) →
      le zero ((Evidence.laws.listSum (data.map family.observation)).1 index)
  | [], _ => le_refl zero
  | value :: rest, index =>
      add_nonnegative (nonnegative value index)
        (listSum_observation_statistic_nonnegative nonnegative rest index)

/-- The posterior evidence: the prior's evidence plus the data's. -/
@[expose] public def update (prior : Evidence statistics) (data : List Observation) :
    Evidence statistics :=
  Evidence.add prior (Evidence.laws.listSum (data.map family.observation))

/-- Updating on no data leaves the evidence unchanged. -/
public theorem update_nil (prior : Evidence statistics) : family.update prior [] = prior :=
  Evidence.add_zero prior

/-- Updating on concatenated data is updating on each part in turn. -/
public theorem update_append (prior : Evidence statistics) (first second : List Observation) :
    family.update prior (first ++ second) = family.update (family.update prior first) second := by
  unfold update
  rw [List.map_append, Evidence.laws.listSum_append, Evidence.add_assoc]

/-- Updating ignores the order of the data. -/
public theorem update_perm (prior : Evidence statistics) {first second : List Observation}
    (perm : first.Perm second) : family.update prior first = family.update prior second := by
  unfold update
  rw [Evidence.laws.listSum_perm (perm.map family.observation)]

/-! ### The conjugate weight -/

/-- The conjugate weight `exp(⟨η(θ), χ⟩ - νA(θ))` of evidence `(χ, ν)`. -/
@[expose] public def weight (evidence : Evidence statistics) (parameter : Parameter) : ENNReal :=
  ENNReal.ofReal (exp (sub (pairing statistics (family.natural parameter) evidence.1)
    (mul evidence.2 (family.logPartition parameter))))

/-- The weight turns addition of evidence into multiplication. -/
public theorem weight_add (first second : Evidence statistics) (parameter : Parameter) :
    family.weight (Evidence.add first second) parameter =
      ENNReal.mul (family.weight first parameter) (family.weight second parameter) := by
  unfold weight
  rw [← ofReal_mul (exp_positive _).1 (exp_positive _).1, ← exp_add]
  congr 2
  show sub (pairing statistics (family.natural parameter)
      (fun index => add (first.1 index) (second.1 index)))
      (mul (add first.2 second.2) (family.logPartition parameter)) = _
  rw [pairing_add_right, add_mul]
  simp only [sub_eq_add_neg, neg_add]
  ac_rfl

/-- The flat evidence has weight one. -/
public theorem weight_zero (parameter : Parameter) :
    family.weight Evidence.zero parameter = ENNReal.one := by
  unfold weight
  show ENNReal.ofReal (exp (sub (pairing statistics (family.natural parameter) (fun _ => zero))
    (mul zero (family.logPartition parameter)))) = ENNReal.one
  rw [pairing_zero_right, zero_mul, sub_zero, exp_zero, ENNReal.ofReal_one]

public theorem weight_ne_zero (evidence : Evidence statistics) (parameter : Parameter) :
    family.weight evidence parameter ≠ ENNReal.zero :=
  fun vanishing => (exp_positive _).2 (ENNReal.ofReal_eq_zero_iff.mp vanishing)

/-- The weight is jointly measurable in the evidence and the parameter. -/
public theorem weight_measurable :
    ENNRealMeasurable (Space.product (Evidence.space statistics) parameters)
      (fun pair => family.weight pair.1 pair.2) := by
  have natural (index : Fin statistics) :
      MeasurableMap (Space.product (Evidence.space statistics) parameters) borel
        (fun pair => family.natural pair.2 index) :=
    MeasurableMap.comp (family.natural_measurable index) (Space.second_measurable _ _)
  have totals (index : Fin statistics) :
      MeasurableMap (Space.product (Evidence.space statistics) parameters) borel
        (fun pair => pair.1.1 index) :=
    MeasurableMap.comp (Space.coordinate_measurable (fun _ : Fin statistics => borel) index)
      (MeasurableMap.comp (Space.first_measurable _ _) (Space.first_measurable _ _))
  have pairingMeasurable :
      MeasurableMap (Space.product (Evidence.space statistics) parameters) borel
        (fun pair => pairing statistics (family.natural pair.2) pair.1.1) :=
    MeasurableMap.comp (finSum_measurable statistics)
      (Space.pi_measurable (fun index => measurable_mul (natural index) (totals index)))
  have count : MeasurableMap (Space.product (Evidence.space statistics) parameters) borel
      (fun pair => pair.1.2) :=
    MeasurableMap.comp (Space.second_measurable _ _) (Space.first_measurable _ _)
  exact ofReal_measurable.comp (MeasurableMap.comp exp_measurable
    (measurable_sub pairingMeasurable (measurable_mul count
      (MeasurableMap.comp family.logPartition_measurable (Space.second_measurable _ _)))))

/-! ### Likelihoods -/

/-- The family's density `h(x) exp(⟨η(θ), T(x)⟩ - A(θ))`. -/
@[expose] public def likelihood (parameter : Parameter) (value : Observation) : ENNReal :=
  ENNReal.mul (ENNReal.finite (family.base value))
    (ENNReal.ofReal (exp (sub (pairing statistics (family.natural parameter)
      (family.statistic value)) (family.logPartition parameter))))

/-- The likelihood is the base times the weight of the observation's evidence. -/
public theorem likelihood_eq (parameter : Parameter) (value : Observation) :
    family.likelihood parameter value =
      ENNReal.mul (ENNReal.finite (family.base value))
        (family.weight (family.observation value) parameter) := by
  unfold likelihood weight observation
  show _ = ENNReal.mul _ (ENNReal.ofReal (exp (sub (pairing statistics (family.natural parameter)
    (family.statistic value)) (mul one (family.logPartition parameter)))))
  rw [one_mul]

/-- Nonzero bases have a nonzero product. -/
public theorem listProduct_base_ne_zero : {data : List Observation} →
    (∀ value, value ∈ data → family.base value ≠ NNReal.zero) →
      NNReal.multiplicativeLaws.listProduct (data.map family.base) ≠ NNReal.zero
  | [], _ => NNReal.one_ne_zero
  | value :: rest, positive => by
      intro vanishing
      rcases NNReal.mul_eq_zero_iff.mp vanishing with head | tail
      · exact positive value (List.Mem.head rest) head
      · exact listProduct_base_ne_zero
          (fun other member => positive other (List.Mem.tail value member))
          tail

/-- A batch likelihood is the base product times the weight of the batch's
summed evidence. -/
public theorem listProduct_likelihood_eq (parameter : Parameter) : (data : List Observation) →
    ENNReal.multiplicativeLaws.listProduct (data.map (family.likelihood parameter)) =
      ENNReal.mul (ENNReal.finite (NNReal.multiplicativeLaws.listProduct (data.map family.base)))
        (family.weight (Evidence.laws.listSum (data.map family.observation)) parameter)
  | [] => by
      show ENNReal.one = ENNReal.mul ENNReal.one (family.weight Evidence.zero parameter)
      rw [weight_zero, ENNReal.one_mul]
  | value :: rest => by
      show ENNReal.mul (family.likelihood parameter value)
            (ENNReal.multiplicativeLaws.listProduct (rest.map (family.likelihood parameter))) =
        ENNReal.mul
          (ENNReal.finite (NNReal.mul (family.base value) (NNReal.multiplicativeLaws.listProduct
            (rest.map family.base))))
          (family.weight (Evidence.add (family.observation value)
              (Evidence.laws.listSum (rest.map family.observation)))
            parameter)
      rw [listProduct_likelihood_eq parameter rest, likelihood_eq, weight_add,
        ← ENNReal.finite_mul_finite]
      ac_rfl

/-! ### Measurability in the data -/

private theorem tail_measurable (count : Nat) :
    MeasurableMap (Space.pi (fun _ : Fin (count + 1) => observations))
      (Space.pi (fun _ : Fin count => observations)) (fun data index => data index.succ) :=
  Space.pi_measurable (fun index =>
    Space.coordinate_measurable (fun _ : Fin (count + 1) => observations) index.succ)

/-- The summed evidence of `count` observations is measurable in the observations. -/
public theorem listSum_observation_measurable : (count : Nat) →
    MeasurableMap (Space.pi (fun _ : Fin count => observations)) (Evidence.space statistics)
      (fun data => Evidence.laws.listSum ((List.ofFn data).map family.observation))
  | 0 => by
      have constant : (fun data : Fin 0 → Observation =>
          Evidence.laws.listSum ((List.ofFn data).map family.observation)) =
          fun _ => Evidence.zero :=
        funext fun data =>
          congrArg (fun data => Evidence.laws.listSum (data.map family.observation))
            (List.ofFn_zero (f := data))
      rw [constant]
      exact MeasurableMap.constant _ _ _
  | count + 1 => by
      have split : (fun data : Fin (count + 1) → Observation =>
          Evidence.laws.listSum ((List.ofFn data).map family.observation)) = fun data =>
            Evidence.add (family.observation (data 0))
              (Evidence.laws.listSum ((List.ofFn fun index : Fin count => data index.succ).map
                family.observation)) :=
        funext fun data =>
          congrArg (fun data => Evidence.laws.listSum (data.map family.observation))
            (List.ofFn_succ (f := data))
      rw [split]
      exact Evidence.add_measurable
        (MeasurableMap.comp (observation_measurable family)
          (Space.coordinate_measurable (fun _ : Fin (count + 1) => observations) 0))
        (MeasurableMap.comp (listSum_observation_measurable count) (tail_measurable count))

/-- The updated evidence is measurable in the observations. -/
public theorem update_measurable (prior : Evidence statistics) (count : Nat) :
    MeasurableMap (Space.pi (fun _ : Fin count => observations)) (Evidence.space statistics)
      (fun data => family.update prior (List.ofFn data)) :=
  Evidence.add_measurable (MeasurableMap.constant _ _ prior)
    (listSum_observation_measurable family count)

/-- The base product of `count` observations is measurable in the observations. -/
public theorem listProduct_base_measurable : (count : Nat) →
    ENNRealMeasurable (Space.pi (fun _ : Fin count => observations))
      (fun data => ENNReal.finite
        (NNReal.multiplicativeLaws.listProduct ((List.ofFn data).map family.base)))
  | 0 => by
      have constant : (fun data : Fin 0 → Observation =>
          ENNReal.finite (NNReal.multiplicativeLaws.listProduct
            ((List.ofFn data).map family.base))) =
          fun _ => ENNReal.one :=
        funext (fun data => congrArg
          (fun data : List Observation =>
            ENNReal.finite (NNReal.multiplicativeLaws.listProduct (data.map family.base)))
          (List.ofFn_zero (f := data)))
      rw [constant]
      exact ENNRealMeasurable.constant _ _
  | count + 1 => by
      have split : (fun data : Fin (count + 1) → Observation =>
          ENNReal.finite (NNReal.multiplicativeLaws.listProduct
            ((List.ofFn data).map family.base))) =
          fun data =>
            ENNReal.mul (ENNReal.finite (family.base (data 0)))
              (ENNReal.finite (NNReal.multiplicativeLaws.listProduct
                ((List.ofFn (fun index : Fin count => data index.succ)).map family.base))) :=
        funext (fun data => (congrArg
          (fun data : List Observation =>
            ENNReal.finite (NNReal.multiplicativeLaws.listProduct (data.map family.base)))
          (List.ofFn_succ (f := data))).trans (ENNReal.finite_mul_finite _ _).symm)
      rw [split]
      exact (family.base_measurable.comp
          (Space.coordinate_measurable (fun _ : Fin (count + 1) => observations) 0)).mul
        ((listProduct_base_measurable count).comp (tail_measurable count))

/-! ### Posteriors -/

/-- The joint density of `count` observations and the parameter, against the
reference on the parameters: the prior weight at `prior` times the batch
likelihood. -/
@[expose] public def joint (prior : Evidence statistics) (count : Nat)
    (data : Fin count → Observation) (parameter : Parameter) : ENNReal :=
  ENNReal.mul (family.weight prior parameter)
    (ENNReal.multiplicativeLaws.listProduct ((List.ofFn data).map (family.likelihood parameter)))

/-- The joint density is the base product times the weight of the updated evidence. -/
public theorem joint_eq (prior : Evidence statistics) (count : Nat)
    (data : Fin count → Observation) (parameter : Parameter) :
    family.joint prior count data parameter =
      ENNReal.mul (ENNReal.finite (NNReal.multiplicativeLaws.listProduct
        ((List.ofFn data).map family.base)))
        (family.weight (family.update prior (List.ofFn data)) parameter) := by
  unfold joint update
  rw [listProduct_likelihood_eq, weight_add]
  ac_rfl

private theorem factored_measurable (prior : Evidence statistics) (count : Nat) :
    ENNRealMeasurable (Space.product (Space.pi (fun _ : Fin count => observations)) parameters)
      (fun pair => ENNReal.mul
        (ENNReal.finite (NNReal.multiplicativeLaws.listProduct
          ((List.ofFn pair.1).map family.base)))
        (family.weight (family.update prior (List.ofFn pair.1)) pair.2)) :=
  ((listProduct_base_measurable family count).comp (Space.first_measurable _ _)).mul
    ((weight_measurable family).comp (Space.pair_measurable
      (MeasurableMap.comp (update_measurable family prior count) (Space.first_measurable _ _))
      (Space.second_measurable _ _)))

public theorem joint_measurable (prior : Evidence statistics) (count : Nat) :
    ENNRealMeasurable (Space.product (Space.pi (fun _ : Fin count => observations)) parameters)
      (fun pair => family.joint prior count pair.1 pair.2) := by
  have factored : (fun pair : (Fin count → Observation) × Parameter =>
      family.joint prior count pair.1 pair.2) = fun pair =>
        ENNReal.mul
          (ENNReal.finite (NNReal.multiplicativeLaws.listProduct
            ((List.ofFn pair.1).map family.base)))
          (family.weight (family.update prior (List.ofFn pair.1)) pair.2) :=
    funext (fun pair => joint_eq family prior count pair.1 pair.2)
  rw [factored]
  exact factored_measurable family prior count

/-- The conjugate kernel: at each evidence, the reference weighted by the
evidence's weight and normalized, or the fallback Dirac measure where the
weighted reference has zero or infinite mass. -/
@[expose] public def conjugate (reference : Measure parameters)
    (referenceFinite : Measure.SFinite reference) (fallback : Parameter) :
    Kernel (Evidence.space statistics) parameters :=
  Kernel.densityConditional reference referenceFinite family.weight (weight_measurable family)
    fallback

public theorem conjugate_eq_normalize (reference : Measure parameters)
    (referenceFinite : Measure.SFinite reference) (fallback : Parameter)
    (evidence : Evidence statistics)
    (defined : Measure.IsNormalizable (reference.withDensity (family.weight evidence))) :
    family.conjugate reference referenceFinite fallback evidence =
      Measure.normalize (reference.withDensity (family.weight evidence)) defined :=
  Kernel.densityConditional_eq_normalize reference referenceFinite (weight_measurable family)
    fallback evidence defined

public theorem conjugate_eq_dirac (reference : Measure parameters)
    (referenceFinite : Measure.SFinite reference) (fallback : Parameter)
    (evidence : Evidence statistics)
    (undefined : ¬Measure.IsNormalizable (reference.withDensity (family.weight evidence))) :
    family.conjugate reference referenceFinite fallback evidence =
      Measure.dirac parameters fallback :=
  Kernel.densityConditional_eq_dirac reference referenceFinite (weight_measurable family)
    fallback evidence undefined

/-- Where the weighted reference is a finite nonzero multiple of a probability
law, the conjugate kernel is that law. Each instance names its conjugate law
this way. -/
public theorem conjugate_eq_of_smul (reference : Measure parameters)
    (referenceFinite : Measure.SFinite reference) (fallback : Parameter)
    (evidence : Evidence statistics) {law : Measure parameters}
    (probability : Measure.IsProbability law) {factor : ENNReal}
    (finite : ENNReal.Finite factor) (nonzero : factor ≠ ENNReal.zero)
    (scaled : reference.withDensity (family.weight evidence) = Measure.smul factor law) :
    family.conjugate reference referenceFinite fallback evidence = law := by
  have lawDefined := probability.to_normalizable
  have defined : Measure.IsNormalizable (reference.withDensity (family.weight evidence)) :=
    scaled ▸ lawDefined.smul finite nonzero
  rw [conjugate_eq_normalize family reference referenceFinite fallback evidence defined,
    Measure.normalize_congr scaled defined (lawDefined.smul finite nonzero),
    Measure.normalize_smul law lawDefined, Measure.normalize_eq_self probability]

/-- Conjugate updating. Under the prior at `prior`, the conditional law of the
parameter given observations with nonzero bases is the conjugate kernel at the
prior's evidence plus the data's summed evidence. -/
public theorem posterior (reference : Measure parameters)
    (referenceFinite : Measure.SFinite reference) (prior : Evidence statistics)
    (fallback : Parameter) {count : Nat} (data : Fin count → Observation)
    (positive : ∀ index, family.base (data index) ≠ NNReal.zero) :
    Kernel.densityConditional reference referenceFinite (family.joint prior count)
        (joint_measurable family prior count) fallback data =
      family.conjugate reference referenceFinite fallback
        (family.update prior (List.ofFn data)) := by
  have baseNonzero :
      ENNReal.finite (NNReal.multiplicativeLaws.listProduct
        ((List.ofFn data).map family.base)) ≠ ENNReal.zero :=
    fun vanishing => listProduct_base_ne_zero family (fun value member => by
      obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
      exact positive index) (ENNReal.finite_injective vanishing)
  exact Kernel.densityConditional_factor reference referenceFinite
    (joint_measurable family prior count) (weight_measurable family) fallback
    (show ENNReal.Finite (ENNReal.finite (NNReal.multiplicativeLaws.listProduct
      ((List.ofFn data).map family.base)))
      from True.intro)
    baseNonzero (funext (joint_eq family prior count data))

/-- The marginal density of a batch is its base product times the mass of the
updated weight. -/
public theorem densityMass_joint (reference : Measure parameters) (prior : Evidence statistics)
    {count : Nat} (data : Fin count → Observation) :
    Kernel.densityMass reference (family.joint prior count) data =
      ENNReal.mul (ENNReal.finite (NNReal.multiplicativeLaws.listProduct
        ((List.ofFn data).map family.base)))
        (lintegral reference (family.weight (family.update prior (List.ofFn data)))) := by
  unfold Kernel.densityMass
  rw [funext (joint_eq family prior count data)]
  exact lintegral_smul reference _
    (Kernel.jointly_measurable_slice (weight_measurable family) _)

/-! ### Closed-form evidence -/

/-- The likelihood of one observation is measurable in the parameter. -/
public theorem likelihood_measurable (value : Observation) :
    ENNRealMeasurable parameters (fun parameter => family.likelihood parameter value) := by
  have factored : (fun parameter => family.likelihood parameter value) = fun parameter =>
      ENNReal.mul (ENNReal.finite (family.base value))
        (family.weight (family.observation value) parameter) :=
    funext fun parameter => likelihood_eq family parameter value
  rw [factored]
  exact (ENNRealMeasurable.constant _ _).mul
    (Kernel.jointly_measurable_slice (weight_measurable family) _)

/-- The batch likelihood is measurable in the parameter. -/
public theorem listProduct_likelihood_measurable (data : List Observation) :
    ENNRealMeasurable parameters
      (fun parameter => ENNReal.multiplicativeLaws.listProduct
        (data.map (family.likelihood parameter))) := by
  have factored :
      (fun parameter => ENNReal.multiplicativeLaws.listProduct
        (data.map (family.likelihood parameter))) = fun parameter =>
      ENNReal.mul (ENNReal.finite (NNReal.multiplicativeLaws.listProduct (data.map family.base)))
        (family.weight (Evidence.laws.listSum (data.map family.observation)) parameter) :=
    funext fun parameter => listProduct_likelihood_eq family parameter data
  rw [factored]
  exact (ENNRealMeasurable.constant _ _).mul
    (Kernel.jointly_measurable_slice (weight_measurable family) _)

/-- The conjugate kernel as a normalized family over evidence, with a constant
fallback. -/
@[expose] public def conjugateFamily (reference : Measure parameters)
    (referenceFinite : Measure.SFinite reference) (fallback : Parameter) :
    Kernel.NormalizedFamily (Evidence.space statistics) parameters where
  reference := reference
  referenceFinite := referenceFinite
  weight := family.weight
  weight_measurable := weight_measurable family
  fallback _ := fallback
  fallback_measurable := MeasurableMap.constant _ parameters fallback

/-- The normalizer `Z(e)` is the mass of the conjugate weight at `e`. -/
public theorem conjugateFamily_normalizer (reference : Measure parameters)
    (referenceFinite : Measure.SFinite reference) (fallback : Parameter)
    (evidence : Evidence statistics) :
    (family.conjugateFamily reference referenceFinite fallback).normalizer evidence =
      lintegral reference (family.weight evidence) :=
  rfl

/-- The conjugate kernel is the law of the normalized family at every evidence. -/
public theorem conjugate_eq_law (reference : Measure parameters)
    (referenceFinite : Measure.SFinite reference) (fallback : Parameter)
    (evidence : Evidence statistics) :
    family.conjugate reference referenceFinite fallback evidence =
      (family.conjugateFamily reference referenceFinite fallback).law evidence := by
  classical
  by_cases defined : Measure.IsNormalizable (reference.withDensity (family.weight evidence))
  · exact ((family.conjugateFamily reference referenceFinite fallback).law_eq_densityConditional
      defined fallback).symm
  · rw [conjugate_eq_dirac family reference referenceFinite fallback evidence defined,
      (family.conjugateFamily reference referenceFinite fallback).law_eq_dirac defined]
    rfl

/-- The normalizer ratio. Under the conjugate prior at `e` with `Z(e)` finite
and nonzero, the marginal likelihood `m` of a batch satisfies
`Z(e)·m = ∏h(xⱼ)·Z(e + Σ)`. -/
public theorem normalizer_mul_marginal (reference : Measure parameters)
    (referenceFinite : Measure.SFinite reference) (fallback : Parameter)
    {prior : Evidence statistics}
    (defined : Measure.IsNormalizable (reference.withDensity (family.weight prior)))
    (data : List Observation) :
    ENNReal.mul ((family.conjugateFamily reference referenceFinite fallback).normalizer prior)
        (lintegral (family.conjugate reference referenceFinite fallback prior)
          (fun parameter =>
            ENNReal.multiplicativeLaws.listProduct (data.map (family.likelihood parameter)))) =
      ENNReal.mul (ENNReal.finite (NNReal.multiplicativeLaws.listProduct (data.map family.base)))
        ((family.conjugateFamily reference referenceFinite fallback).normalizer
          (family.update prior data)) := by
  rw [conjugate_eq_law]
  apply Kernel.NormalizedFamily.normalizer_mul_lintegral_law _
    (family.listProduct_likelihood_measurable data) defined
  intro parameter
  show ENNReal.mul (family.weight prior parameter)
      (ENNReal.multiplicativeLaws.listProduct (data.map (family.likelihood parameter))) =
    ENNReal.mul _
      (family.weight (Evidence.add prior (Evidence.laws.listSum (data.map family.observation)))
        parameter)
  rw [listProduct_likelihood_eq, weight_add]
  ac_rfl

/-- The one-step predictive. At evidence `e` with `Z(e)` finite and nonzero,
the predictive density `p` of one observation `x` satisfies
`Z(e)·p = h(x)·Z(e + (T(x), 1))`. After data, `e` is the updated evidence
(`posterior`). -/
public theorem normalizer_mul_predictive (reference : Measure parameters)
    (referenceFinite : Measure.SFinite reference) (fallback : Parameter)
    {evidence : Evidence statistics}
    (defined : Measure.IsNormalizable (reference.withDensity (family.weight evidence)))
    (value : Observation) :
    ENNReal.mul ((family.conjugateFamily reference referenceFinite fallback).normalizer evidence)
        (lintegral (family.conjugate reference referenceFinite fallback evidence)
          (fun parameter => family.likelihood parameter value)) =
      ENNReal.mul (ENNReal.finite (family.base value))
        ((family.conjugateFamily reference referenceFinite fallback).normalizer
          (Evidence.add evidence (family.observation value))) := by
  rw [conjugate_eq_law]
  apply Kernel.NormalizedFamily.normalizer_mul_lintegral_law _
    (family.likelihood_measurable value) defined
  intro parameter
  show ENNReal.mul (family.weight evidence parameter) (family.likelihood parameter value) =
    ENNReal.mul _ (family.weight (Evidence.add evidence (family.observation value)) parameter)
  rw [likelihood_eq, weight_add]
  ac_rfl

/-- Where the updated normalizer is infinite, the marginal likelihood of a
batch with nonzero base product is infinite. -/
public theorem marginal_eq_top (reference : Measure parameters)
    (referenceFinite : Measure.SFinite reference) (fallback : Parameter)
    {prior : Evidence statistics}
    (defined : Measure.IsNormalizable (reference.withDensity (family.weight prior)))
    {data : List Observation}
    (baseNonzero : NNReal.multiplicativeLaws.listProduct (data.map family.base) ≠ NNReal.zero)
    (infinite : (family.conjugateFamily reference referenceFinite fallback).normalizer
      (family.update prior data) = ENNReal.top) :
    lintegral (family.conjugate reference referenceFinite fallback prior)
        (fun parameter => ENNReal.multiplicativeLaws.listProduct
          (data.map (family.likelihood parameter))) =
          ENNReal.top := by
  rw [conjugate_eq_law]
  apply Kernel.NormalizedFamily.lintegral_law_eq_top _
    (family.listProduct_likelihood_measurable data) defined _
    (fun vanishing => baseNonzero (ENNReal.finite_injective vanishing)) infinite
  intro parameter
  show ENNReal.mul (family.weight prior parameter)
      (ENNReal.multiplicativeLaws.listProduct (data.map (family.likelihood parameter))) =
    ENNReal.mul _
      (family.weight (Evidence.add prior (Evidence.laws.listSum (data.map family.observation)))
        parameter)
  rw [listProduct_likelihood_eq, weight_add]
  ac_rfl

/-- Posteriors agree wherever the updated evidence agrees, across priors and
batch sizes. -/
public theorem posterior_congr (reference : Measure parameters)
    (referenceFinite : Measure.SFinite reference) {prior otherPrior : Evidence statistics}
    (fallback : Parameter) {count otherCount : Nat} {data : Fin count → Observation}
    {otherData : Fin otherCount → Observation}
    (positive : ∀ index, family.base (data index) ≠ NNReal.zero)
    (otherPositive : ∀ index, family.base (otherData index) ≠ NNReal.zero)
    (same : family.update prior (List.ofFn data) =
      family.update otherPrior (List.ofFn otherData)) :
    Kernel.densityConditional reference referenceFinite (family.joint prior count)
        (joint_measurable family prior count) fallback data =
      Kernel.densityConditional reference referenceFinite (family.joint otherPrior otherCount)
        (joint_measurable family otherPrior otherCount) fallback otherData := by
  rw [posterior family reference referenceFinite prior fallback data positive,
    posterior family reference referenceFinite otherPrior fallback otherData otherPositive, same]

/-- Reordering the observations leaves the posterior unchanged. -/
public theorem posterior_perm (reference : Measure parameters)
    (referenceFinite : Measure.SFinite reference) (prior : Evidence statistics)
    (fallback : Parameter) {count otherCount : Nat} {data : Fin count → Observation}
    {otherData : Fin otherCount → Observation}
    (positive : ∀ index, family.base (data index) ≠ NNReal.zero)
    (otherPositive : ∀ index, family.base (otherData index) ≠ NNReal.zero)
    (perm : (List.ofFn data).Perm (List.ofFn otherData)) :
    Kernel.densityConditional reference referenceFinite (family.joint prior count)
        (joint_measurable family prior count) fallback data =
      Kernel.densityConditional reference referenceFinite (family.joint prior otherCount)
        (joint_measurable family prior otherCount) fallback otherData :=
  posterior_congr family reference referenceFinite fallback positive otherPositive
    (update_perm family prior perm)

/-- Conditioning in two stages is conditioning on the whole batch: the
posterior evidence after the first stage is the prior of the second. -/
public theorem posterior_append (reference : Measure parameters)
    (referenceFinite : Measure.SFinite reference) (prior : Evidence statistics)
    (fallback : Parameter) {count firstCount secondCount : Nat} {data : Fin count → Observation}
    {first : Fin firstCount → Observation} {second : Fin secondCount → Observation}
    (positive : ∀ index, family.base (data index) ≠ NNReal.zero)
    (secondPositive : ∀ index, family.base (second index) ≠ NNReal.zero)
    (split : List.ofFn data = List.ofFn first ++ List.ofFn second) :
    Kernel.densityConditional reference referenceFinite (family.joint prior count)
        (joint_measurable family prior count) fallback data =
      Kernel.densityConditional reference referenceFinite
        (family.joint (family.update prior (List.ofFn first)) secondCount)
        (joint_measurable family (family.update prior (List.ofFn first)) secondCount)
        fallback second :=
  posterior_congr family reference referenceFinite fallback positive secondPositive
    (by rw [split, update_append])

/-! ### The flat prior -/

/-- A flat prior with no observations has no normalization against a reference of
infinite mass, because its joint fiber is the reference itself. -/
public theorem flat_not_normalizable (reference : Measure parameters)
    (infinite : reference Set.univ = ENNReal.top) (data : Fin 0 → Observation) :
    ¬Measure.IsNormalizable
      (Kernel.densityFiber reference (family.joint Evidence.zero 0) data) := by
  have unit : family.joint Evidence.zero 0 data = fun _ => ENNReal.one := by
    funext parameter
    rw [joint_eq, List.ofFn_zero, update_nil, weight_zero]
    exact ENNReal.mul_one _
  apply Measure.infinite_not_normalizable
  unfold Kernel.densityFiber
  rw [unit, Measure.withDensity_one]
  exact infinite

/-- Against a reference of infinite mass, the conjugate kernel at the flat
evidence is the fallback. -/
public theorem conjugate_flat (reference : Measure parameters)
    (referenceFinite : Measure.SFinite reference) (fallback : Parameter)
    (infinite : reference Set.univ = ENNReal.top) :
    family.conjugate reference referenceFinite fallback Evidence.zero =
      Measure.dirac parameters fallback := by
  apply conjugate_eq_dirac
  have unit : family.weight Evidence.zero = fun _ => ENNReal.one := funext (weight_zero family)
  rw [unit, Measure.withDensity_one]
  exact Measure.infinite_not_normalizable infinite

end ExponentialFamily

end

end Problib.Analysis
