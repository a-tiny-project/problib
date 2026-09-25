module

public import Problib.Inference.Population
public import Problib.Measure.Product.Countable
public import Problib.Measure.Kernel.Piecewise
set_option autoImplicit false

/-! Resampling a population.

Resampling draws one parent lane for every child lane and gives every child
its parent's value and the population's mean weight `W/N` (`resample`). The
offspring equation asks that each lane's expected number of children be
proportional to its weight, in the form `W · (1/M) · Σ_j P(a_j = i) = w_i`
(`OffspringUnbiased`). It has no division, so it asks nothing more when
`W = 0`. Under it, resampling keeps every population's empirical measure in
expectation over the parents, population by population (`empirical_resample`).
Because the identity holds for each population, the decision to resample may
read the population (`resampling_policy_invariant`).

The equation constrains expected counts, not the joint law of the children.
Per-child categorical marginals give it whatever the children's dependence
(`offspring_unbiased_of_marginals`). At total weight zero every child weight is
zero and so is the empirical measure, so the parents there are a declared map
(`ZeroWeightPolicy`): the identity when the lanes are the same, and position
modulo the parent count otherwise (`zeroParents`). -/

namespace Problib.Inference

open Problib.Real Problib.Measure
open Problib.Measure.SimpleFunction (finiteSum finiteSum_eq_unique finiteSum_comm
  finiteSum_map_mul_left)

universe u

variable {α : Type u}

public section

/-! ### Total weight -/

/-- The total weight `W = Σ_j w_j` of a population. -/
@[expose] noncomputable def totalWeight {ι : Type} (lanes : Lanes ι)
    (draws : ι → α × NNReal) : NNReal :=
  lanes.sum fun index => (draws index).2

/-- The mean weight is the share times the total weight. -/
theorem meanWeight_eq {ι : Type} (lanes : Lanes ι) (draws : ι → α × NNReal) :
    meanWeight lanes draws = NNReal.mul lanes.share (totalWeight lanes draws) :=
  rfl

theorem totalWeight_measurable {ι : Type} (lanes : Lanes ι) (space : Space α) :
    MeasurableMap (populationSpace ι space) weightSpace (totalWeight lanes) := by
  refine weight_measurable_of_finite ?_
  have equal : (fun draws : ι → α × NNReal => ENNReal.finite (totalWeight lanes draws)) =
      fun draws => finiteSum (lanes.list.map fun index => drawWeight (draws index)) :=
    funext fun draws => lanes.finite_sum fun index => (draws index).2
  rw [equal]
  exact ENNRealMeasurable.finiteSum_map lanes.list fun index =>
    (drawWeight_measurable space).comp (lane_measurable space index)

theorem meanWeight_measurable {ι : Type} (lanes : Lanes ι) (space : Space α) :
    MeasurableMap (populationSpace ι space) weightSpace (meanWeight lanes) :=
  weight_mul_measurable (MeasurableMap.constant _ weightSpace lanes.share)
    (totalWeight_measurable lanes space)

private theorem term_eq_zero {Index : Type} (values : Index → ENNReal) :
    ∀ indices : List Index, finiteSum (indices.map values) = ENNReal.zero →
      ∀ index, index ∈ indices → values index = ENNReal.zero
  | [], _, _, member => (List.not_mem_nil member).elim
  | head :: tail, zero, index, member => by
      simp only [List.map, finiteSum] at zero
      have split := ENNReal.add_eq_zero_iff.mp zero
      rcases List.mem_cons.mp member with same | inTail
      · rw [same]
        exact split.1
      · exact term_eq_zero values tail split.2 index inTail

/-- At total weight zero every weight is zero. -/
theorem weight_eq_zero {ι : Type} {lanes : Lanes ι} {draws : ι → α × NNReal}
    (zero : totalWeight lanes draws = NNReal.zero) (index : ι) :
    (draws index).2 = NNReal.zero := by
  have total : finiteSum (lanes.list.map fun lane => ENNReal.finite (draws lane).2) =
      ENNReal.zero := by
    rw [← Lanes.finite_sum]
    exact congrArg ENNReal.finite zero
  exact ENNReal.finite_injective
    (term_eq_zero _ lanes.list total index (lanes.enumeration.complete index))

/-! ### Positions -/

namespace Lanes

variable {ι : Type}

/-- The position of a lane in the enumeration. -/
noncomputable def position (lanes : Lanes ι) (lane : ι) : Nat := by
  classical
  exact lanes.list.idxOf lane

private theorem idxOf_injective [DecidableEq ι] (list : List ι) {first second : ι}
    (firstMember : first ∈ list) (same : list.idxOf first = list.idxOf second) :
    first = second := by
  induction list with
  | nil => exact (List.not_mem_nil firstMember).elim
  | cons head tail induction =>
      rw [List.idxOf_cons, List.idxOf_cons] at same
      by_cases firstHead : head = first
      · by_cases secondHead : head = second
        · exact firstHead.symm.trans secondHead
        · rw [beq_iff_eq.mpr firstHead, beq_eq_false_iff_ne.mpr secondHead] at same
          simp at same
      · by_cases secondHead : head = second
        · rw [beq_eq_false_iff_ne.mpr firstHead, beq_iff_eq.mpr secondHead] at same
          simp at same
        · rw [beq_eq_false_iff_ne.mpr firstHead, beq_eq_false_iff_ne.mpr secondHead,
            cond_false, cond_false] at same
          exact induction ((List.mem_cons.mp firstMember).resolve_left (Ne.symm firstHead))
            (Nat.add_right_cancel same)

/-- Distinct lanes have distinct positions. -/
theorem position_injective (lanes : Lanes ι) : Function.Injective lanes.position := by
  classical
  intro first second same
  exact idxOf_injective lanes.list (lanes.enumeration.complete first) same

end Lanes

/-! ### Ancestors and the resampled population -/

/-- One parent per child. Parent indices are discrete. -/
abbrev ancestorSpace (ι κ : Type) : Space (κ → ι) := Space.pi fun _ : κ => Space.discrete ι

/-- Any function of one child's parent is measurable. -/
theorem parent_measurable {ι κ : Type} (values : ι → ENNReal) (child : κ) :
    ENNRealMeasurable (ancestorSpace ι κ) (fun parents => values (parents child)) :=
  (ENNRealMeasurable.of_measurableMap (MeasurableMap.from_discrete ennrealBorel values)).comp
    (Space.coordinate_measurable (fun _ : κ => Space.discrete ι) child)

/-- The parents naming one lane for one child form a measurable set. -/
theorem parent_region_measurable {ι κ : Type} (child : κ) (index : ι) :
    (ancestorSpace ι κ).Measurable (fun parents : κ → ι => parents child = index) :=
  (Space.coordinate_measurable (fun _ : κ => Space.discrete ι) child :
    MeasurableMap (ancestorSpace ι κ) (Space.discrete ι) fun parents => parents child)
    (Space.discrete_measurable fun lane : ι => lane = index)

/-- Reading a child's parent from a population, jointly in the population and
the parents. -/
theorem select_measurable {ι κ : Type} (lanes : Lanes ι) (space : Space α) (child : κ) :
    MeasurableMap (Space.product (populationSpace ι space) (ancestorSpace ι κ))
      (Space.product space weightSpace) (fun pair => pair.1 (pair.2 child)) := by
  have evaluate : MeasurableMap (Space.product (Space.discrete ι) (populationSpace ι space))
      (Space.product space weightSpace) (fun pair => pair.2 pair.1) :=
    MeasurableMap.uncurry_of_countable_first (source := populationSpace ι space)
      (target := Space.product space weightSpace) lanes.position lanes.position_injective
      (function := fun (index : ι) (draws : ι → α × NNReal) => draws index)
      fun index => lane_measurable space index
  intro region regionMeasurable
  exact MeasurableMap.comp evaluate (Space.pair_measurable
    (MeasurableMap.comp (Space.coordinate_measurable (fun _ : κ => Space.discrete ι) child)
      (Space.second_measurable _ _))
    (Space.first_measurable _ _)) regionMeasurable

theorem resample_measurable {ι κ : Type} (lanes : Lanes ι) (space : Space α) :
    MeasurableMap (Space.product (populationSpace ι space) (ancestorSpace ι κ))
      (populationSpace κ space)
      (fun pair child => ((pair.1 (pair.2 child)).1, meanWeight lanes pair.1)) :=
  Space.pi_measurable (spaces := fun _ : κ => Space.product space weightSpace) fun child =>
    Space.pair_measurable
      (MeasurableMap.comp (Space.first_measurable space weightSpace)
        (select_measurable lanes space child))
      (MeasurableMap.comp (meanWeight_measurable lanes space) (Space.first_measurable _ _))

/-- Child `j` copies parent `a_j`'s value and carries the mean parent weight
`W/N`. -/
@[expose] noncomputable def resample {ι κ : Type} (lanes : Lanes ι) {space : Space α}
    (ancestors : Kernel (populationSpace ι space) (ancestorSpace ι κ))
    (ancestorsFinite : Kernel.IsSFinite ancestors) :
    Kernel (populationSpace ι space) (populationSpace κ space) :=
  (ancestors.attach ancestorsFinite).map _ (resample_measurable lanes space)

theorem resample_apply {ι κ : Type} (lanes : Lanes ι) {space : Space α}
    (ancestors : Kernel (populationSpace ι space) (ancestorSpace ι κ))
    (ancestorsFinite : Kernel.IsSFinite ancestors) (draws : ι → α × NNReal) :
    resample lanes ancestors ancestorsFinite draws =
      (ancestors draws).map
        (fun parents child => ((draws (parents child)).1, meanWeight lanes draws))
        (MeasurableMap.comp (resample_measurable lanes space)
          (Kernel.pair_left_measurable (source := populationSpace ι space) draws)) := by
  rw [resample, Kernel.map_apply, Kernel.attach_apply, Measure.map_comp]

/-! ### Counting offspring -/

/-- Integrating a function of one child's parent sums over the parent lanes. -/
theorem lintegral_parent {ι κ : Type} (lanes : Lanes ι) (measure : Measure (ancestorSpace ι κ))
    (child : κ) (values : ι → ENNReal) :
    lintegral measure (fun parents => values (parents child)) =
      finiteSum (lanes.list.map fun index =>
        ENNReal.mul (values index) (measure (fun parents => parents child = index))) := by
  have pointwise : ∀ parents : κ → ι, values (parents child) =
      finiteSum (lanes.list.map fun index =>
        ennrealIndicator (fun parents : κ → ι => parents child = index)
          (fun _ => values index) parents) := by
    intro parents
    have away : ∀ index, index ∈ lanes.list → index ≠ parents child →
        ennrealIndicator (fun parents : κ → ι => parents child = index)
          (fun _ => values index) parents = ENNReal.zero := by
      intro index _ different
      have notSame : ¬parents child = index := fun same => different same.symm
      unfold ennrealIndicator ennrealPiecewise
      simp [notSame]
    rw [finiteSum_eq_unique lanes.list (parents child) lanes.enumeration.nodup
      (lanes.enumeration.complete _) _ away]
    unfold ennrealIndicator ennrealPiecewise
    simp
  rw [lintegral_congr _ pointwise, lintegral_finiteSum_map _ lanes.list fun index =>
    ENNRealMeasurable.indicator (parent_region_measurable child index)
      (ENNRealMeasurable.constant _ (values index))]
  refine congrArg finiteSum (List.map_congr_left fun index _ => ?_)
  rw [lintegral_indicator _ _ (parent_region_measurable child index), lintegral_const,
    Measure.restrict_apply_univ]

/-- Integrating a sum over the children of a function of each child's parent
weighs every parent lane by its expected number of children. -/
theorem lintegral_offspring {ι κ : Type} (inLanes : Lanes ι) (outLanes : Lanes κ)
    (measure : Measure (ancestorSpace ι κ)) (values : ι → ENNReal) :
    lintegral measure (fun parents =>
        finiteSum (outLanes.list.map fun child => values (parents child))) =
      finiteSum (inLanes.list.map fun index => ENNReal.mul (values index)
        (finiteSum (outLanes.list.map fun child =>
          measure (fun parents => parents child = index)))) := by
  rw [lintegral_finiteSum_map _ outLanes.list fun child => parent_measurable values child]
  simp only [lintegral_parent inLanes measure _ values]
  rw [finiteSum_comm]
  simp only [finiteSum_map_mul_left]

/-! ### The offspring equation -/

/-- Expected offspring proportional to weight: `W · (1/M) · Σ_j P(a_j = i) = w_i`. -/
@[expose] def OffspringUnbiased {ι κ : Type} (inLanes : Lanes ι) (outLanes : Lanes κ)
    {space : Space α} (ancestors : Kernel (populationSpace ι space) (ancestorSpace ι κ)) :
    Prop :=
  ∀ draws index, ENNReal.mul (ENNReal.finite (totalWeight inLanes draws))
      (ENNReal.mul (ENNReal.finite outLanes.share)
        (finiteSum (outLanes.list.map fun child =>
          ancestors draws (fun parents => parents child = index)))) =
    ENNReal.finite (draws index).2

/-- ResampInv: the step keeps every population's empirical measure. -/
@[expose] def ResampleInvariant {ι κ : Type} (inLanes : Lanes ι) (outLanes : Lanes κ)
    {space : Space α} (step : Kernel (populationSpace ι space) (populationSpace κ space)) :
    Prop :=
  step.comp (empirical outLanes space) = empirical inLanes space

private theorem mul_left_comm (first second third : ENNReal) :
    ENNReal.mul first (ENNReal.mul second third) =
      ENNReal.mul second (ENNReal.mul first third) := by
  rw [← ENNReal.mul_assoc, ENNReal.mul_comm first second, ENNReal.mul_assoc]

/-- The per-lane rearrangement in `empirical_resample`:
`s · (((n · W) · v) · c) = n · ((W · (s · c)) · v)`. -/
private theorem resample_factors (outShare inShare total value count : ENNReal) :
    ENNReal.mul outShare
        (ENNReal.mul (ENNReal.mul (ENNReal.mul inShare total) value) count) =
      ENNReal.mul inShare
        (ENNReal.mul (ENNReal.mul total (ENNReal.mul outShare count)) value) := by
  rw [ENNReal.mul_assoc (ENNReal.mul inShare total) value count,
    ENNReal.mul_assoc inShare total, mul_left_comm outShare inShare,
    mul_left_comm outShare total, ENNReal.mul_assoc total (ENNReal.mul outShare count) value,
    ENNReal.mul_assoc outShare count value, ENNReal.mul_comm value count]

/-- Under the offspring equation, resampling keeps every population's
empirical measure. -/
theorem empirical_resample {ι κ : Type} {inLanes : Lanes ι} {outLanes : Lanes κ}
    {space : Space α} {ancestors : Kernel (populationSpace ι space) (ancestorSpace ι κ)}
    {ancestorsFinite : Kernel.IsSFinite ancestors}
    (unbiased : OffspringUnbiased inLanes outLanes ancestors) :
    ResampleInvariant inLanes outLanes (resample inLanes ancestors ancestorsFinite) := by
  apply Kernel.ext
  intro draws
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  -- Every child carries its parent's value at the mean weight.
  have children : ∀ parents : κ → ι,
      lintegral (empirical outLanes space
          (fun child => ((draws (parents child)).1, meanWeight inLanes draws))) function =
        ENNReal.mul (ENNReal.finite outLanes.share)
          (finiteSum (outLanes.list.map fun child =>
            ENNReal.mul (ENNReal.finite (meanWeight inLanes draws))
              (function (draws (parents child)).1))) :=
    fun parents => lintegral_empirical outLanes _ measurable
  rw [Kernel.lintegral_comp _ _ _ measurable, resample_apply,
    lintegral_map _ _ _ (Kernel.lintegral_measurable _ measurable), lintegral_congr _ children,
    lintegral_smul _ _ (ENNRealMeasurable.finiteSum_map outLanes.list fun child =>
      parent_measurable (fun index => ENNReal.mul (ENNReal.finite (meanWeight inLanes draws))
        (function (draws index).1)) child),
    lintegral_offspring inLanes outLanes _ fun index =>
      ENNReal.mul (ENNReal.finite (meanWeight inLanes draws)) (function (draws index).1),
    lintegral_empirical inLanes draws measurable,
    ← finiteSum_map_mul_left, ← finiteSum_map_mul_left]
  refine congrArg finiteSum (List.map_congr_left fun index _ => ?_)
  show ENNReal.mul (ENNReal.finite outLanes.share)
      (ENNReal.mul (ENNReal.mul (ENNReal.finite (meanWeight inLanes draws))
          (function (draws index).1))
        (finiteSum (outLanes.list.map fun child =>
          ancestors draws (fun parents => parents child = index)))) =
    ENNReal.mul (ENNReal.finite inLanes.share)
      (ENNReal.mul (ENNReal.finite (draws index).2) (function (draws index).1))
  rw [meanWeight_eq, ← ENNReal.finite_mul_finite, resample_factors, unbiased draws index]

/-- A Markov step that keeps every population's empirical measure keeps any
target invariant. -/
theorem step_invariant_of_resample {ι κ : Type} {inLanes : Lanes ι} {outLanes : Lanes κ}
    {space : Space α} {target : Measure space}
    {step : Kernel (populationSpace ι space) (populationSpace κ space)}
    (markov : ∀ draws, Measure.IsProbability (step draws))
    (invariant : ResampleInvariant inLanes outLanes step) :
    StepInvariant inLanes outLanes target target step := by
  intro population populationInvariant
  refine ⟨populationInvariant.probability.bind _ markov, ?_⟩
  rw [Measure.bind_assoc, invariant, populationInvariant.mean]

/-- Deciding from the population whether to resample keeps every population's
empirical measure when both branches do. -/
theorem resampling_policy_invariant {ι κ : Type} {inLanes : Lanes ι} {outLanes : Lanes κ}
    {space : Space α} {region : Set (ι → α × NNReal)}
    (regionMeasurable : (populationSpace ι space).Measurable region)
    {now keep : Kernel (populationSpace ι space) (populationSpace κ space)}
    (nowInvariant : ResampleInvariant inLanes outLanes now)
    (keepInvariant : ResampleInvariant inLanes outLanes keep) :
    ResampleInvariant inLanes outLanes (Kernel.piecewise region regionMeasurable now keep) := by
  apply Kernel.ext
  intro draws
  rw [Kernel.comp_apply]
  by_cases member : region draws
  · rw [Kernel.piecewise_apply_of_mem _ _ _ _ _ member]
    exact congrArg (fun kernel => kernel draws) nowInvariant
  · rw [Kernel.piecewise_apply_of_not_mem _ _ _ _ _ member]
    exact congrArg (fun kernel => kernel draws) keepInvariant

/-! ### Zero total weight -/

/-- The zero-weight policy: at total weight zero, the parents are a declared
map. -/
@[expose] def ZeroWeightPolicy {ι κ : Type} (inLanes : Lanes ι) {space : Space α}
    (ancestors : Kernel (populationSpace ι space) (ancestorSpace ι κ)) (parents : κ → ι) :
    Prop :=
  ∀ draws, totalWeight inLanes draws = NNReal.zero →
    ancestors draws = Measure.dirac _ parents

/-- At total weight zero, resampling copies the declared parents at weight
zero. -/
theorem resample_zero_weight {ι κ : Type} {inLanes : Lanes ι} {space : Space α}
    {ancestors : Kernel (populationSpace ι space) (ancestorSpace ι κ)}
    {ancestorsFinite : Kernel.IsSFinite ancestors} {parents : κ → ι}
    (policy : ZeroWeightPolicy inLanes ancestors parents) {draws : ι → α × NNReal}
    (zero : totalWeight inLanes draws = NNReal.zero) :
    resample inLanes ancestors ancestorsFinite draws =
      Measure.dirac _ (fun child => ((draws (parents child)).1, NNReal.zero)) := by
  have mean : meanWeight inLanes draws = NNReal.zero := by
    rw [meanWeight_eq, zero, NNReal.mul_zero]
  rw [resample_apply, policy draws zero, Measure.map_dirac, mean]

/-- With the same lanes and the identity parents, resampling at total weight
zero returns the population unchanged. -/
theorem resample_zero_weight_keeps {ι : Type} {lanes : Lanes ι} {space : Space α}
    {ancestors : Kernel (populationSpace ι space) (ancestorSpace ι ι)}
    {ancestorsFinite : Kernel.IsSFinite ancestors}
    (policy : ZeroWeightPolicy lanes ancestors fun child => child) {draws : ι → α × NNReal}
    (zero : totalWeight lanes draws = NNReal.zero) :
    resample lanes ancestors ancestorsFinite draws = Measure.dirac _ draws := by
  rw [resample_zero_weight policy zero]
  congr 1
  funext child
  exact Prod.ext rfl (weight_eq_zero zero child).symm

/-- The declared parents at zero weight: the child at position `p` takes the
parent at position `p mod N`. -/
@[expose] noncomputable def zeroParents {ι κ : Type} (inLanes : Lanes ι) (outLanes : Lanes κ)
    (child : κ) : ι :=
  inLanes.list[outLanes.position child % inLanes.count]'(Nat.mod_lt _ inLanes.count_pos)

/-! ### Categorical marginals -/

/-- Mass `w_i / W` at each lane `i`. It is read only where `W ≠ 0`. -/
@[expose] noncomputable def categorical {ι : Type} (lanes : Lanes ι)
    (draws : ι → α × NNReal) : Measure (Space.discrete ι) :=
  Measure.listSum (lanes.list.map fun index =>
    Measure.smul (ENNReal.finite (NNReal.div (draws index).2 (totalWeight lanes draws)))
      (Measure.dirac _ index))

theorem categorical_apply {ι : Type} (lanes : Lanes ι) (draws : ι → α × NNReal) (index : ι) :
    categorical lanes draws (fun lane => lane = index) =
      ENNReal.finite (NNReal.div (draws index).2 (totalWeight lanes draws)) := by
  have single : (Space.discrete ι).Measurable (fun lane => lane = index) :=
    Space.discrete_measurable _
  have atom : ∀ other, Measure.smul
      (ENNReal.finite (NNReal.div (draws other).2 (totalWeight lanes draws)))
      (Measure.dirac (Space.discrete ι) other) (fun lane => lane = index) =
      ENNReal.mul (ENNReal.finite (NNReal.div (draws other).2 (totalWeight lanes draws)))
        (Measure.dirac (Space.discrete ι) other (fun lane => lane = index)) :=
    fun other => Measure.smul_apply_measurable _ _ single
  rw [categorical, Measure.listSum_apply _ single, List.map_map]
  refine (finiteSum_eq_unique lanes.list index lanes.enumeration.nodup
    (lanes.enumeration.complete index) _ fun other _ different => ?_).trans ?_
  · show Measure.smul _ (Measure.dirac _ other) (fun lane => lane = index) = ENNReal.zero
    rw [atom, Measure.dirac_apply_of_not_mem _ other single different, ENNReal.mul_zero]
  · show Measure.smul _ (Measure.dirac _ index) (fun lane => lane = index) = _
    rw [atom, Measure.dirac_apply_of_mem _ index single rfl, ENNReal.mul_one]

/-- Per-child categorical marginals give the offspring equation, whatever the
joint law of the children. -/
theorem offspring_unbiased_of_marginals {ι κ : Type} {inLanes : Lanes ι} {outLanes : Lanes κ}
    {space : Space α} {ancestors : Kernel (populationSpace ι space) (ancestorSpace ι κ)}
    (marginals : ∀ draws child, totalWeight inLanes draws ≠ NNReal.zero →
      (ancestors draws).map (fun parents => parents child)
          (Space.coordinate_measurable (fun _ : κ => Space.discrete ι) child) =
        categorical inLanes draws) :
    OffspringUnbiased inLanes outLanes ancestors := by
  intro draws index
  by_cases zero : totalWeight inLanes draws = NNReal.zero
  · rw [zero, weight_eq_zero zero index]
    exact ENNReal.zero_mul _
  · have each : ∀ child, ancestors draws (fun parents => parents child = index) =
        ENNReal.finite (NNReal.div (draws index).2 (totalWeight inLanes draws)) := by
      intro child
      rw [← categorical_apply inLanes draws index, ← marginals draws child zero]
      exact (Measure.map_apply (ancestors draws) (fun parents : κ → ι => parents child)
        (Space.coordinate_measurable (fun _ : κ => Space.discrete ι) child)
        (Space.discrete_measurable fun lane : ι => lane = index)).symm
    simp only [each]
    rw [outLanes.average_const, ENNReal.finite_mul_finite, NNReal.mul_div_cancel _ zero]

end

end Problib.Inference
