module

public import Problib.Inference.Resampling
public import Problib.Measure.Kernel.Product.Finite
public import Problib.Measure.Uniform
import Problib.Measure.Integral.Lebesgue.Transport
import Problib.Measure.Product.Countable
import Problib.Measure.Extended.Conversion
import Problib.Measure.Real.Arithmetic
import Problib.Measure.Real.Order
import Problib.Measure.Uniform.Band

set_option autoImplicit false

/-! # Systematic and multinomial ancestors

Both kernels draw one parent per child, and both follow `ZeroWeightPolicy`: at
total weight zero the parents are `zeroParents`, through `Kernel.piecewise` on
the zero-total region.

- `systematicAncestors` draws one uniform `u`. The child at position `p` of `M`
  reads the categorical index at `(p + u) / M`. Its offspring counts are
  unbiased (`systematic_offspring_unbiased`), and its children are dependent.
- `multinomialAncestors` draws every child's parent independently from
  `categorical`, through `Kernel.finProduct`. Its offspring counts are unbiased
  (`multinomial_offspring_unbiased`), and two distinct children read their
  parents independently (`multinomial_pair`).

`categoricalIndex` is the first lane in enumeration order whose cumulative
share of the weight exceeds `u`, or the fallback lane. Its uniform mass at lane
`i` is `w_i / W` (`categorical_mass`). Comparing reals is classical here, so the
index is noncomputable. No runtime reads it: Church draws its ancestors through
`normalize`.

RePPL's proof closure imports `Problib.Inference.Resampling` and not this
module.
-/

namespace Problib.Inference

open Problib.Measure Problib.Real
open Problib.Measure.Real (Carrier borel UnitInterval unitBorel uniform01 uniform01_univ
  uniform01_isProbability uniform01_real_initial uniform01_real_initial_of_one_le
  unitInclusion_measurable measurable_iio measurable_lt measurable_div measurable_sub measurable_mul
  toReal_measurable ofReal_measurable)
open Problib.Analysis (categorical categorical_apply categorical_isProbability
  discrete_apply listSum_shares)
open Problib.Real.Construction

variable {α : Type} {space : Space α}

public section

/-! ### The zero-total region -/

/-- The populations whose total weight is zero. -/
@[expose] def zeroTotal {ι : Type} (lanes : Lanes ι) : Set (ι → α × NNReal) :=
  fun draws => ¬ENNReal.lt ENNReal.zero (ENNReal.finite (totalWeight lanes draws))

theorem zeroTotal_measurable {ι : Type} (lanes : Lanes ι) (space : Space α) :
    (populationSpace ι space).Measurable (zeroTotal lanes) :=
  (populationSpace ι space).complement
    (finite_weight_measurable (totalWeight_measurable lanes space) ENNReal.zero)

theorem zeroTotal_iff {ι : Type} (lanes : Lanes ι) (draws : ι → α × NNReal) :
    zeroTotal lanes draws ↔ totalWeight lanes draws = NNReal.zero := by
  constructor
  · intro zero
    exact NNReal.le_antisymm
      (Classical.byContradiction fun above =>
        zero (And.intro (NNReal.zero_le _) above :
          ENNReal.lt ENNReal.zero (ENNReal.finite (totalWeight lanes draws))))
      (NNReal.zero_le _)
  · intro zero below
    apply below.2
    rw [zero]
    exact NNReal.le_refl _

/-! ### Categorical shares -/

/-! ### Picking a lane by its share interval -/

/-- Lane `lane`'s share `w / W` of the total weight. -/
@[expose] noncomputable def laneShare {ι : Type} (lanes : Lanes ι) (draws : ι → α × NNReal)
    (lane : ι) : NNReal :=
  NNReal.div (draws lane).2 (totalWeight lanes draws)

open Classical in
/-- The lane of `list` whose interval holds `point`, the intervals read from
`offset` on. A lane's interval ends at the cumulative share through it, which
`bound` turns into the threshold `point` is compared with. The pick is the first
lane whose threshold exceeds `point`, and the last lane otherwise. -/
@[expose] noncomputable def pickLane {ι : Type} (share : ι → NNReal) (bound : NNReal → Carrier)
    (point : Carrier) : NNReal → List ι → ι → ι
  | _, [], fallback => fallback
  | _, [lane], _ => lane
  | offset, lane :: next :: rest, fallback =>
      if Dedekind.lt point (bound (NNReal.add offset (share lane))) then lane
      else pickLane share bound point (NNReal.add offset (share lane)) (next :: rest) fallback

open Classical in
/-- The cumulative share before `index` in `list`, from `offset` on. -/
@[expose] noncomputable def shareBefore {ι : Type} (share : ι → NNReal) :
    NNReal → List ι → ι → NNReal
  | offset, [], _ => offset
  | offset, lane :: rest, index =>
      if lane = index then offset else shareBefore share (NNReal.add offset (share lane)) rest index

/-- The uniform mass below the threshold of a cumulative share. -/
@[expose] noncomputable def massBelow (bound : NNReal → Carrier) (share : NNReal) : ENNReal :=
  uniform01 fun point : UnitInterval => Dedekind.lt point.val (bound share)

private theorem le_add_self_right (left right : NNReal) : NNReal.le left (NNReal.add left right) := by
  have grown := NNReal.add_le_add (NNReal.le_refl left) (NNReal.zero_le right)
  rwa [NNReal.add_zero] at grown

theorem pickLane_mem {ι : Type} (share : ι → NNReal) (bound : NNReal → Carrier) (point : Carrier)
    (fallback : ι) :
    ∀ (offset : NNReal) (lane : ι) (rest : List ι),
      pickLane share bound point offset (lane :: rest) fallback ∈ lane :: rest
  | _, lane, [] => List.mem_cons.mpr (Or.inl rfl)
  | offset, lane, next :: rest => by
      simp only [pickLane]
      by_cases below : Dedekind.lt point (bound (NNReal.add offset (share lane)))
      · rw [ite_eq_left below]
        exact List.mem_cons.mpr (Or.inl rfl)
      · rw [ite_eq_right below]
        exact List.mem_cons.mpr (Or.inr (pickLane_mem share bound point fallback _ next rest))

/-- The cumulative share through `index` is at most the share of the whole list. -/
theorem shareBefore_add_le {ι : Type} (share : ι → NNReal) (index : ι) :
    ∀ (offset : NNReal) (list : List ι), index ∈ list →
      NNReal.le (NNReal.add (shareBefore share offset list index) (share index))
        (NNReal.add offset (NNReal.additiveLaws.listSum (list.map share)))
  | _, [], member => nomatch member
  | offset, lane :: rest, member => by
      show NNReal.le _ (NNReal.add offset
        (NNReal.add (share lane) (NNReal.additiveLaws.listSum (rest.map share))))
      rw [← NNReal.add_assoc]
      by_cases equal : lane = index
      · subst equal
        rw [shareBefore, ite_eq_left rfl]
        exact le_add_self_right _ _
      · rw [shareBefore, ite_eq_right equal]
        exact shareBefore_add_le share index _ rest
          ((List.mem_cons.mp member).resolve_left fun same => equal same.symm)

private theorem below_measurable (threshold : Carrier) :
    unitBorel.Measurable (fun point : UnitInterval => Dedekind.lt point.val threshold) :=
  unitInclusion_measurable (measurable_iio threshold)

/-- The mass below a larger threshold is the mass below the smaller one and the
mass between them. -/
private theorem uniform01_between {lower upper : Carrier} (ordered : Dedekind.le lower upper) :
    ENNReal.add
        (uniform01 fun point : UnitInterval =>
          ¬Dedekind.lt point.val lower ∧ Dedekind.lt point.val upper)
        (uniform01 fun point : UnitInterval => Dedekind.lt point.val lower) =
      uniform01 fun point : UnitInterval => Dedekind.lt point.val upper := by
  refine (Measure.union_disjoint uniform01
    (unitBorel.inter (unitBorel.complement (below_measurable lower)) (below_measurable upper))
    (below_measurable lower) fun _ between below => between.1 below).symm.trans ?_
  refine congrArg (fun set => uniform01 set) (Set.ext fun point => ?_)
  exact ⟨fun member => member.elim (fun between => between.2)
      fun below => Dedekind.lt_of_lt_of_le below ordered,
    fun below => (Classical.em (Dedekind.lt point.val lower)).elim Or.inr
      fun above => Or.inl ⟨above, below⟩⟩

/-- The mass at or above a threshold and the mass below it make one. -/
private theorem uniform01_above (lower : Carrier) :
    ENNReal.add (uniform01 fun point : UnitInterval => ¬Dedekind.lt point.val lower)
        (uniform01 fun point : UnitInterval => Dedekind.lt point.val lower) =
      ENNReal.one := by
  refine (Measure.union_disjoint uniform01 (unitBorel.complement (below_measurable lower))
    (below_measurable lower) fun _ above below => above below).symm.trans ?_
  rw [← uniform01_univ]
  exact congrArg (fun set => uniform01 set)
    (Set.ext fun point => ⟨fun _ => trivial, fun _ => (Classical.em _).symm⟩)

/-- The interval law. Read from `offset` on, the points `pickLane` sends to
`index` fill the gap between the thresholds before and through `index`, once
the threshold of the whole list holds all the mass. -/
theorem pickLane_mass {ι : Type} (share : ι → NNReal) (bound : NNReal → Carrier)
    (monotone : ∀ {left right : NNReal}, NNReal.le left right →
      Dedekind.le (bound left) (bound right))
    (fallback index : ι) :
    ∀ (offset : NNReal) (list : List ι), list.Nodup → index ∈ list →
      massBelow bound
          (NNReal.add offset (NNReal.additiveLaws.listSum (list.map share))) = ENNReal.one →
      ENNReal.add
          (uniform01 fun point : UnitInterval => ¬Dedekind.lt point.val (bound offset) ∧
            pickLane share bound point.val offset list fallback = index)
          (massBelow bound (shareBefore share offset list index)) =
        massBelow bound (NNReal.add (shareBefore share offset list index) (share index))
  | _, [], _, member, _ => nomatch member
  | offset, [lane], _, member, whole => by
      have equal : index = lane := List.mem_singleton.mp member
      subst equal
      have before : shareBefore share offset [index] index = offset := by
        rw [shareBefore, ite_eq_left rfl]
      have through : NNReal.add offset (NNReal.additiveLaws.listSum (([index]).map share)) =
          NNReal.add offset (share index) := by
        show NNReal.add offset (NNReal.add (share index) NNReal.zero) = _
        rw [NNReal.add_zero]
      rw [before, ← through, whole]
      have same : (fun point : UnitInterval => ¬Dedekind.lt point.val (bound offset) ∧
          pickLane share bound point.val offset [index] fallback = index) =
          fun point => ¬Dedekind.lt point.val (bound offset) :=
        Set.ext fun _ => ⟨fun both => both.1, fun above => ⟨above, rfl⟩⟩
      rw [same]
      exact uniform01_above (bound offset)
  | offset, lane :: next :: rest, nodup, member, whole => by
      have fresh : lane ∉ next :: rest := (List.nodup_cons.mp nodup).1
      have tailNodup : (next :: rest).Nodup := (List.nodup_cons.mp nodup).2
      have grown : Dedekind.le (bound offset) (bound (NNReal.add offset (share lane))) :=
        monotone (le_add_self_right offset (share lane))
      by_cases equal : lane = index
      · subst equal
        have before : shareBefore share offset (lane :: next :: rest) lane = offset := by
          rw [shareBefore, ite_eq_left rfl]
        have same : (fun point : UnitInterval => ¬Dedekind.lt point.val (bound offset) ∧
            pickLane share bound point.val offset (lane :: next :: rest) fallback = lane) =
            fun point => ¬Dedekind.lt point.val (bound offset) ∧
              Dedekind.lt point.val (bound (NNReal.add offset (share lane))) := by
          refine Set.ext fun point => ?_
          simp only [pickLane]
          by_cases below : Dedekind.lt point.val (bound (NNReal.add offset (share lane)))
          · rw [ite_eq_left below]
            exact ⟨fun both => ⟨both.1, below⟩, fun both => ⟨both.1, rfl⟩⟩
          · rw [ite_eq_right below]
            exact ⟨fun both => absurd
                (both.2 ▸ pickLane_mem share bound point.val fallback _ next rest) fresh,
              fun both => absurd both.2 below⟩
        rw [before, same]
        exact uniform01_between grown
      · have tailMember : index ∈ next :: rest :=
          (List.mem_cons.mp member).resolve_left fun same => equal same.symm
        have before : shareBefore share offset (lane :: next :: rest) index =
            shareBefore share (NNReal.add offset (share lane)) (next :: rest) index := by
          rw [shareBefore, ite_eq_right equal]
        have tailWhole : massBelow bound (NNReal.add (NNReal.add offset (share lane))
            (NNReal.additiveLaws.listSum ((next :: rest).map share))) = ENNReal.one := by
          rw [NNReal.add_assoc]
          exact whole
        have same : (fun point : UnitInterval => ¬Dedekind.lt point.val (bound offset) ∧
            pickLane share bound point.val offset (lane :: next :: rest) fallback = index) =
            fun point => ¬Dedekind.lt point.val (bound (NNReal.add offset (share lane))) ∧
              pickLane share bound point.val (NNReal.add offset (share lane)) (next :: rest)
                fallback = index := by
          refine Set.ext fun point => ?_
          simp only [pickLane]
          by_cases below : Dedekind.lt point.val (bound (NNReal.add offset (share lane)))
          · rw [ite_eq_left below]
            exact ⟨fun both => absurd both.2 equal, fun both => absurd below both.1⟩
          · rw [ite_eq_right below]
            exact ⟨fun both => ⟨below, both.2⟩,
              fun both => ⟨fun early => below (Dedekind.lt_of_lt_of_le early grown), both.2⟩⟩
        rw [before, same]
        exact pickLane_mass share bound monotone fallback index _ (next :: rest) tailNodup
          tailMember tailWhole

/-- The sum of two measurable weights is measurable. -/
private theorem weight_add_measurable {σ : Type} {source : Space σ} {left right : σ → NNReal}
    (leftMeasurable : MeasurableMap source weightSpace left)
    (rightMeasurable : MeasurableMap source weightSpace right) :
    MeasurableMap source weightSpace (fun input => NNReal.add (left input) (right input)) :=
  weight_measurable_of_finite (ENNRealMeasurable.add (finite_weight_measurable leftMeasurable)
    (finite_weight_measurable rightMeasurable))

/-- The quotient of two measurable weights is measurable. -/
theorem weight_div_measurable {σ : Type} {source : Space σ} {left right : σ → NNReal}
    (leftMeasurable : MeasurableMap source weightSpace left)
    (rightMeasurable : MeasurableMap source weightSpace right) :
    MeasurableMap source weightSpace (fun input => NNReal.div (left input) (right input)) := by
  refine weight_measurable_of_finite ?_
  have real : MeasurableMap source borel (fun input =>
      Dedekind.div (NNReal.toReal (left input)) (NNReal.toReal (right input))) :=
    measurable_div
      (MeasurableMap.comp toReal_measurable
        (MeasurableMap.comp (Space.comap_map ENNReal.finite ennrealBorel) leftMeasurable))
      (MeasurableMap.comp toReal_measurable
        (MeasurableMap.comp (Space.comap_map ENNReal.finite ennrealBorel) rightMeasurable))
  have equal : (fun input => ENNReal.finite (NNReal.div (left input) (right input))) =
      fun input => ENNReal.ofReal
        (Dedekind.div (NNReal.toReal (left input)) (NNReal.toReal (right input))) :=
    funext fun input => (ENNReal.ofReal_toReal_finite _).symm
  rw [equal]
  exact ENNRealMeasurable.comp ofReal_measurable real

theorem laneShare_measurable {ι : Type} (lanes : Lanes ι) (space : Space α) (lane : ι) :
    MeasurableMap (populationSpace ι space) weightSpace
      (fun draws => laneShare lanes draws lane) :=
  weight_div_measurable
    (MeasurableMap.comp (Space.second_measurable space weightSpace) (lane_measurable space lane))
    (totalWeight_measurable lanes space)

/-- The pick is measurable jointly in the input that sets the shares and the
uniform point. -/
theorem pickLane_measurable {σ ι : Type} {source : Space σ} (share : σ → ι → NNReal)
    (shareMeasurable : ∀ lane, MeasurableMap source weightSpace fun input => share input lane)
    (bound : NNReal → Carrier) (boundMeasurable : MeasurableMap weightSpace borel bound)
    (fallback : ι) :
    ∀ (list : List ι) (offset : σ → NNReal), MeasurableMap source weightSpace offset →
      MeasurableMap (Space.product source unitBorel) (Space.discrete ι)
        (fun pair => pickLane (share pair.1) bound pair.2.val (offset pair.1) list fallback)
  | [], _, _ => MeasurableMap.constant _ _ fallback
  | [lane], _, _ => MeasurableMap.constant _ _ lane
  | lane :: next :: rest, offset, offsetMeasurable => by
      have nextMeasurable : MeasurableMap source weightSpace
          (fun input => NNReal.add (offset input) (share input lane)) :=
        weight_add_measurable offsetMeasurable (shareMeasurable lane)
      have region : (Space.product source unitBorel).Measurable (fun pair : σ × UnitInterval =>
          Dedekind.lt pair.2.val (bound (NNReal.add (offset pair.1) (share pair.1 lane)))) :=
        measurable_lt
          (MeasurableMap.comp unitInclusion_measurable (Space.second_measurable source unitBorel))
          (MeasurableMap.comp boundMeasurable
            (MeasurableMap.comp nextMeasurable (Space.first_measurable source unitBorel)))
      have later : MeasurableMap (Space.product source unitBorel) (Space.discrete ι)
          (fun pair => pickLane (share pair.1) bound pair.2.val
            (NNReal.add (offset pair.1) (share pair.1 lane)) (next :: rest) fallback) :=
        pickLane_measurable share shareMeasurable bound boundMeasurable fallback
          (next :: rest) _ nextMeasurable
      apply MeasurableMap.to_discrete
      intro set
      have equal : Set.preimage (fun pair : σ × UnitInterval =>
          pickLane (share pair.1) bound pair.2.val (offset pair.1) (lane :: next :: rest) fallback) set =
          Set.union
            (Set.inter (fun pair : σ × UnitInterval =>
              Dedekind.lt pair.2.val (bound (NNReal.add (offset pair.1) (share pair.1 lane))))
              (Set.preimage (fun _ : σ × UnitInterval => lane) set))
            (Set.inter (Set.complement fun pair : σ × UnitInterval =>
              Dedekind.lt pair.2.val (bound (NNReal.add (offset pair.1) (share pair.1 lane))))
              (Set.preimage (fun pair : σ × UnitInterval =>
                pickLane (share pair.1) bound pair.2.val (NNReal.add (offset pair.1) (share pair.1 lane))
                  (next :: rest) fallback) set)) := by
        refine Set.ext fun pair => ?_
        simp only [Set.preimage, Set.union, Set.inter, Set.complement, pickLane]
        by_cases below : Dedekind.lt pair.2.val (bound (NNReal.add (offset pair.1) (share pair.1 lane)))
        · rw [ite_eq_left below]
          exact ⟨fun member => Or.inl ⟨below, member⟩,
            fun either => either.elim (fun both => both.2) fun both => absurd below both.1⟩
        · rw [ite_eq_right below]
          exact ⟨fun member => Or.inr ⟨below, member⟩,
            fun either => either.elim (fun both => absurd both.1 below) fun both => both.2⟩
      rw [equal]
      exact (Space.product source unitBorel).union
        ((Space.product source unitBorel).inter region
          (MeasurableMap.constant _ (Space.discrete ι) lane (Space.discrete_measurable set)))
        ((Space.product source unitBorel).inter ((Space.product source unitBorel).complement region)
          (later (Space.discrete_measurable set)))

/-! ### The categorical index -/

/-- The lane whose share interval holds `point`. -/
@[expose] noncomputable def categoricalIndex {ι : Type} (lanes : Lanes ι)
    (draws : ι → α × NNReal) (fallback : ι) (point : UnitInterval) : ι :=
  pickLane (laneShare lanes draws) NNReal.toReal point.val NNReal.zero lanes.list fallback

theorem categoricalIndex_measurable {ι : Type} (lanes : Lanes ι) (fallback : ι) :
    MeasurableMap (Space.product (populationSpace ι space) unitBorel) (Space.discrete ι)
      (fun pair => categoricalIndex lanes pair.1 fallback pair.2) :=
  pickLane_measurable (fun draws => laneShare lanes draws) (laneShare_measurable lanes space)
    NNReal.toReal weight_toReal_measurable fallback lanes.list (fun _ => NNReal.zero)
    (MeasurableMap.constant _ _ _)

/-- At positive total weight, the uniform mass of the points indexing lane `i`
is its share of the weight. -/
theorem categorical_mass {ι : Type} (lanes : Lanes ι) (fallback : ι)
    (draws : ι → α × NNReal) (positive : totalWeight lanes draws ≠ NNReal.zero) (index : ι) :
    uniform01 (fun point => categoricalIndex lanes draws fallback point = index) =
      ENNReal.finite (laneShare lanes draws index) := by
  have whole : NNReal.add NNReal.zero
      (NNReal.additiveLaws.listSum (lanes.list.map (laneShare lanes draws))) =
      NNReal.one := by
    rw [NNReal.zero_add]
    exact listSum_shares lanes.list (weights := fun lane => (draws lane).2) positive
  have initial : ∀ share, NNReal.le share NNReal.one →
      massBelow NNReal.toReal share = ENNReal.finite share := fun share atMostOne => by
    unfold massBelow
    rw [uniform01_real_initial _ atMostOne]
    exact ENNReal.ofReal_toReal_finite share
  have mass := pickLane_mass (laneShare lanes draws) NNReal.toReal (fun included => included)
    fallback index NNReal.zero lanes.list lanes.enumeration.nodup
    (lanes.enumeration.complete index) (by
      rw [whole]
      exact initial NNReal.one (NNReal.le_refl _))
  have bounded := shareBefore_add_le (laneShare lanes draws) index NNReal.zero lanes.list
    (lanes.enumeration.complete index)
  rw [whole] at bounded
  rw [initial _ (NNReal.le_trans (le_add_self_right _ _) bounded), initial _ bounded] at mass
  have same : (fun point : UnitInterval => ¬Dedekind.lt point.val (NNReal.toReal NNReal.zero) ∧
      pickLane (laneShare lanes draws) NNReal.toReal point.val NNReal.zero lanes.list fallback =
        index) =
      fun point => categoricalIndex lanes draws fallback point = index :=
    Set.ext fun point => ⟨fun both => both.2,
      fun picked => ⟨fun negative => Dedekind.not_le_of_lt negative point.property.1, picked⟩⟩
  rw [same] at mass
  refine ENNReal.add_right_cancel_of_finite (factor := ENNReal.finite _) trivial (mass.trans ?_)
  rw [NNReal.add_comm]
  rfl

/-- At positive total weight, the uniform draw pushed through the interval pick
is the categorical law of the weights. -/
theorem map_categoricalIndex {ι : Type} (lanes : Lanes ι) (draws : ι → α × NNReal)
    (fallback : ι) (positive : totalWeight lanes draws ≠ NNReal.zero)
    (measurable : MeasurableMap unitBorel (Space.discrete ι)
      (categoricalIndex lanes draws fallback)) :
    uniform01.map (categoricalIndex lanes draws fallback) measurable =
      categorical lanes.list fun lane => (draws lane).2 := by
  apply Measure.ext
  intro set _
  rw [discrete_apply _ lanes.enumeration set, categorical_apply]
  refine congrArg ENNReal.additiveLaws.listSum (List.map_congr_left fun lane _ => ?_)
  rw [Measure.map_apply _ _ _ (Space.discrete_measurable _),
    show Set.preimage (categoricalIndex lanes draws fallback) (fun other => other = lane) =
      fun point => categoricalIndex lanes draws fallback point = lane from rfl,
    categorical_mass lanes fallback draws positive lane]
  rfl

/-- The categorical law of the lanes' weights, read as a kernel of the
population. -/
@[expose] noncomputable def categoricalKernel {ι : Type} (lanes : Lanes ι) (space : Space α) :
    Kernel (populationSpace ι space) (Space.discrete ι) where
  toFun draws := categorical lanes.list fun lane => (draws lane).2
  measurable := by
    intro set measurable
    have equal : (fun draws : ι → α × NNReal =>
        categorical lanes.list (fun lane => (draws lane).2) set) =
        fun draws : ι → α × NNReal =>
        ENNReal.additiveLaws.listSum (lanes.list.map fun index => ENNReal.mul
          (ENNReal.finite (NNReal.div (draws index).2 (totalWeight lanes draws)))
          (Measure.dirac (Space.discrete ι) index set)) :=
      funext fun draws => categorical_apply lanes.list _ set
    show ENNRealMeasurable (populationSpace ι space)
      (fun draws : ι → α × NNReal => categorical lanes.list (fun lane => (draws lane).2) set)
    rw [equal]
    exact ENNRealMeasurable.listSum_map lanes.list fun index =>
      ENNRealMeasurable.mul (finite_weight_measurable (laneShare_measurable lanes space index))
        (ENNRealMeasurable.constant _ _)

/-! ### Systematic ancestors -/

/-- A count as a weight. -/
@[expose] noncomputable def natWeight (count : Nat) : NNReal :=
  NNReal.ofRat (count : Rat) Rat.natCast_nonneg

theorem natWeight_zero : natWeight 0 = NNReal.zero :=
  (NNReal.ofRat_congr rfl).trans NNReal.ofRat_zero

theorem natWeight_succ (count : Nat) :
    natWeight (count + 1) = NNReal.add (natWeight count) NNReal.one := by
  have one : natWeight 1 = NNReal.one := (NNReal.ofRat_congr rfl).trans NNReal.ofRat_one
  rw [← one]
  unfold natWeight
  rw [← NNReal.ofRat_add]
  exact NNReal.ofRat_congr (Rat.natCast_add count 1)

theorem natWeight_add (left : Nat) :
    ∀ right, natWeight (left + right) = NNReal.add (natWeight left) (natWeight right)
  | 0 => by rw [Nat.add_zero, natWeight_zero, NNReal.add_zero]
  | right + 1 => by
      rw [← Nat.add_assoc, natWeight_succ, natWeight_succ, natWeight_add left right,
        NNReal.add_assoc]

/-- A child's position among the out-lanes. -/
@[expose] noncomputable def childIndex {κ : Type} (outLanes : Lanes κ) (child : κ) : Nat := by
  classical
  exact outLanes.list.idxOf child

theorem childIndex_lt {κ : Type} (outLanes : Lanes κ) (child : κ) :
    childIndex outLanes child < outLanes.count := by
  classical
  exact List.idxOf_lt_length_of_mem (outLanes.enumeration.complete child)

private theorem idxOf_map {κ : Type} [DecidableEq κ] :
    ∀ list : List κ, list.Nodup → list.map (fun child => list.idxOf child) = List.range list.length
  | [], _ => rfl
  | lane :: rest, nodup => by
      have fresh := (List.nodup_cons.mp nodup).1
      rw [List.length_cons, List.range_succ_eq_map, ← idxOf_map rest (List.nodup_cons.mp nodup).2,
        List.map_cons, List.map_map]
      simp only [List.idxOf_cons_self]
      congr 1
      apply List.map_congr_left
      intro other member
      have different : lane ≠ other := fun same => fresh (same ▸ member)
      show (lane :: rest).idxOf other = rest.idxOf other + 1
      rw [List.idxOf_cons, beq_eq_false_iff_ne.mpr different]
      simp only [Bool.false_eq_true, ite_false]

/-- The children's positions enumerate `0, …, M - 1`. -/
theorem childIndex_map {κ : Type} (outLanes : Lanes κ) :
    outLanes.list.map (childIndex outLanes) = List.range outLanes.count := by
  classical
  exact idxOf_map outLanes.list outLanes.enumeration.nodup

/-- Child `child`, at position `p` of `M`, reads the point `(p + u) / M`. That
point lies below a cumulative share `c` exactly when `u` lies below `M · c - p`. -/
@[expose] noncomputable def systematicBound {κ : Type} (outLanes : Lanes κ) (child : κ)
    (share : NNReal) : Carrier :=
  Dedekind.sub (NNReal.toReal (NNReal.mul (natWeight outLanes.count) share))
    (NNReal.toReal (natWeight (childIndex outLanes child)))

private theorem systematicBound_monotone {κ : Type} (outLanes : Lanes κ) (child : κ)
    {left right : NNReal} (included : NNReal.le left right) :
    Dedekind.le (systematicBound outLanes child left) (systematicBound outLanes child right) := by
  unfold systematicBound
  rw [Dedekind.sub_eq_add_neg, Dedekind.sub_eq_add_neg]
  exact Dedekind.add_le_add (NNReal.mul_le_mul_left included _) (Dedekind.le_refl _)

private theorem systematicBound_measurable {κ : Type} (outLanes : Lanes κ) (child : κ) :
    MeasurableMap weightSpace borel (systematicBound outLanes child) :=
  measurable_sub
    (MeasurableMap.comp weight_toReal_measurable
      (weight_mul_measurable (MeasurableMap.constant weightSpace weightSpace _)
        (MeasurableMap.identity weightSpace)))
    (MeasurableMap.constant _ borel _)

private theorem le_sub_of_add_le {first second third : Carrier}
    (included : Dedekind.le (Dedekind.add first second) third) :
    Dedekind.le first (Dedekind.sub third second) := by
  have shifted := (Dedekind.add_le_add_right_iff (shift := Dedekind.neg second)).mpr included
  rwa [Dedekind.add_assoc, Dedekind.add_neg, Dedekind.add_zero, ← Dedekind.sub_eq_add_neg] at shifted

/-- The whole share's threshold is at least one, since `p < M`. -/
private theorem systematicBound_one {κ : Type} (outLanes : Lanes κ) (child : κ) :
    Dedekind.le Dedekind.one (systematicBound outLanes child NNReal.one) := by
  have split : outLanes.count =
      childIndex outLanes child + 1 + (outLanes.count - (childIndex outLanes child + 1)) :=
    (Nat.add_sub_of_le (childIndex_lt outLanes child)).symm
  unfold systematicBound
  rw [NNReal.mul_one]
  apply le_sub_of_add_le
  rw [split, natWeight_add, natWeight_succ, NNReal.toReal_add, NNReal.toReal_add, NNReal.toReal_one,
    Dedekind.add_comm Dedekind.one]
  have grown := Dedekind.add_le_add
    (Dedekind.le_refl
      (Dedekind.add (NNReal.toReal (natWeight (childIndex outLanes child))) Dedekind.one))
    (natWeight (outLanes.count - (childIndex outLanes child + 1))).property
  rwa [Dedekind.add_zero] at grown

/-- No point lies below the threshold of the empty share, which is `-p`. -/
private theorem systematicBound_zero {κ : Type} (outLanes : Lanes κ) (child : κ)
    (point : UnitInterval) :
    ¬Dedekind.lt point.val (systematicBound outLanes child NNReal.zero) := by
  unfold systematicBound
  rw [NNReal.mul_zero, NNReal.toReal_zero, Dedekind.zero_sub]
  intro below
  exact Dedekind.not_le_of_lt below (Dedekind.le_trans
    (Dedekind.neg_nonpositive_iff.mp (natWeight (childIndex outLanes child)).property)
    point.property.1)

/-- Every child's parent from one shared uniform. -/
@[expose] noncomputable def systematicParents {ι κ : Type} (inLanes : Lanes ι)
    (outLanes : Lanes κ) (draws : ι → α × NNReal) (point : UnitInterval) : κ → ι :=
  fun child => pickLane (laneShare inLanes draws) (systematicBound outLanes child) point.val
    NNReal.zero inLanes.list (zeroParents inLanes outLanes child)

theorem systematicParents_measurable {ι κ : Type} (inLanes : Lanes ι) (outLanes : Lanes κ) :
    MeasurableMap (Space.product (populationSpace ι space) unitBorel) (ancestorSpace ι κ)
      (fun pair => systematicParents inLanes outLanes pair.1 pair.2) :=
  Space.pi_measurable fun child =>
    pickLane_measurable (fun draws => laneShare inLanes draws) (laneShare_measurable inLanes space)
      (systematicBound outLanes child) (systematicBound_measurable outLanes child)
      (zeroParents inLanes outLanes child) inLanes.list (fun _ => NNReal.zero)
      (MeasurableMap.constant _ _ _)

/-- One uniform, shared by every child. At zero total weight, `zeroParents`. -/
@[expose] noncomputable def systematicAncestors {ι κ : Type} (inLanes : Lanes ι)
    (outLanes : Lanes κ) (space : Space α) :
    Kernel (populationSpace ι space) (ancestorSpace ι κ) :=
  Kernel.piecewise (zeroTotal inLanes) (zeroTotal_measurable inLanes space)
    (Kernel.const _ (Measure.dirac _ (zeroParents inLanes outLanes)))
    (((Kernel.const (populationSpace ι space) uniform01).attach
        (Kernel.IsSFinite.ofMarkov fun _ => uniform01_isProbability)).map
      (fun pair => systematicParents inLanes outLanes pair.1 pair.2)
      (systematicParents_measurable inLanes outLanes))

theorem systematic_zero_weight {ι κ : Type} (inLanes : Lanes ι) (outLanes : Lanes κ) :
    ZeroWeightPolicy inLanes (systematicAncestors inLanes outLanes space)
      (zeroParents inLanes outLanes) := fun draws zero =>
  Kernel.piecewise_apply_of_mem _ _ _ _ draws ((zeroTotal_iff inLanes draws).mpr zero)

/-- At positive total weight, a child reads a parent on the uniform mass of the
points it sends there. -/
theorem systematic_apply {ι κ : Type} (inLanes : Lanes ι) (outLanes : Lanes κ)
    (draws : ι → α × NNReal) (positive : totalWeight inLanes draws ≠ NNReal.zero)
    (child : κ) (index : ι) :
    systematicAncestors inLanes outLanes space draws (fun parents => parents child = index) =
      uniform01 fun point : UnitInterval =>
        systematicParents inLanes outLanes draws point child = index := by
  unfold systematicAncestors
  rw [Kernel.piecewise_apply_of_not_mem _ _ _ _ draws fun zero =>
      positive ((zeroTotal_iff inLanes draws).mp zero),
    Kernel.map_apply, Kernel.attach_apply,
    Measure.map_apply _ _ _ (parent_region_measurable child index),
    Measure.map_apply _ _ _
      (systematicParents_measurable inLanes outLanes (parent_region_measurable child index))]
  rfl

/-- Each child reads parent `index` on the mass between its thresholds before
and through `index`. -/
private theorem systematic_child_mass {ι κ : Type} (inLanes : Lanes ι) (outLanes : Lanes κ)
    (draws : ι → α × NNReal) (positive : totalWeight inLanes draws ≠ NNReal.zero)
    (index : ι) (child : κ) :
    ENNReal.add
        (uniform01 fun point : UnitInterval =>
          systematicParents inLanes outLanes draws point child = index)
        (massBelow (systematicBound outLanes child)
          (shareBefore (laneShare inLanes draws) NNReal.zero inLanes.list index)) =
      massBelow (systematicBound outLanes child)
        (NNReal.add (shareBefore (laneShare inLanes draws) NNReal.zero inLanes.list index)
          (laneShare inLanes draws index)) := by
  have whole : massBelow (systematicBound outLanes child)
      (NNReal.add NNReal.zero
        (NNReal.additiveLaws.listSum (inLanes.list.map (laneShare inLanes draws)))) =
      ENNReal.one := by
    rw [NNReal.zero_add,
      show NNReal.additiveLaws.listSum (inLanes.list.map (laneShare inLanes draws)) =
          NNReal.one from
        listSum_shares inLanes.list (weights := fun lane => (draws lane).2) positive]
    exact uniform01_real_initial_of_one_le _ (systematicBound_one outLanes child)
  have mass := pickLane_mass (laneShare inLanes draws) (systematicBound outLanes child)
    (systematicBound_monotone outLanes child) (zeroParents inLanes outLanes child) index
    NNReal.zero inLanes.list inLanes.enumeration.nodup (inLanes.enumeration.complete index) whole
  have same : (fun point : UnitInterval =>
      ¬Dedekind.lt point.val (systematicBound outLanes child NNReal.zero) ∧
        pickLane (laneShare inLanes draws) (systematicBound outLanes child) point.val NNReal.zero
          inLanes.list (zeroParents inLanes outLanes child) = index) =
      fun point => systematicParents inLanes outLanes draws point child = index :=
    Set.ext fun point =>
      ⟨fun both => both.2, fun picked => ⟨systematicBound_zero outLanes child point, picked⟩⟩
  rw [same] at mass
  exact mass

private theorem sub_add_eq_sub_sub (level first second : Carrier) :
    Dedekind.sub level (Dedekind.add first second) =
      Dedekind.sub (Dedekind.sub level second) first := by
  rw [Dedekind.sub_eq_add_neg, Dedekind.sub_eq_add_neg, Dedekind.sub_eq_add_neg, Dedekind.neg_add,
    Dedekind.add_assoc, Dedekind.add_comm (Dedekind.neg first)]

/-- The unit intervals `[p, p + 1)` for `p < M` tile `[0, M)`: the uniform
masses below `y - p` add up to `y`. -/
private theorem uniform01_tiling : ∀ (count : Nat) (level : Carrier),
    Dedekind.le Dedekind.zero level → Dedekind.le level (NNReal.toReal (natWeight count)) →
    ENNReal.additiveLaws.listSum ((List.range count).map fun position =>
      uniform01 fun point : UnitInterval =>
        Dedekind.lt point.val (Dedekind.sub level (NNReal.toReal (natWeight position)))) =
      ENNReal.ofReal level
  | 0, level, nonnegative, atMost => by
      rw [natWeight_zero] at atMost
      rw [(Dedekind.le_antisymm atMost nonnegative).trans NNReal.toReal_zero, ENNReal.ofReal_zero]
      rfl
  | count + 1, level, nonnegative, atMost => by
      have shifted : ∀ position : Nat,
          Dedekind.sub level (NNReal.toReal (natWeight (position + 1))) =
            Dedekind.sub (Dedekind.sub level Dedekind.one) (NNReal.toReal (natWeight position)) :=
        fun position => by
          rw [natWeight_succ, NNReal.toReal_add, NNReal.toReal_one, sub_add_eq_sub_sub]
      rw [natWeight_succ, NNReal.toReal_add, NNReal.toReal_one] at atMost
      simp only [List.range_succ_eq_map, List.map_cons, List.map_map, Function.comp_def,
        Nat.succ_eq_add_one, shifted, natWeight_zero, NNReal.toReal_zero, Dedekind.sub_zero]
      show ENNReal.add _ (ENNReal.additiveLaws.listSum _) = _
      by_cases high : Dedekind.le Dedekind.one level
      · have lowered : Dedekind.le (Dedekind.sub level Dedekind.one)
            (NNReal.toReal (natWeight count)) := by
          have shifted := (Dedekind.add_le_add_right_iff (shift := Dedekind.neg Dedekind.one)).mpr
            atMost
          rwa [Dedekind.add_assoc, Dedekind.add_neg, Dedekind.add_zero,
            ← Dedekind.sub_eq_add_neg] at shifted
        rw [uniform01_tiling count _ (Dedekind.sub_nonnegative high) lowered,
          uniform01_real_initial_of_one_le level high, ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add (Dedekind.le_of_lt Dedekind.one_positive)
            (Dedekind.sub_nonnegative high),
          Dedekind.add_sub_cancel]
      · have below : Dedekind.lt level Dedekind.one := Dedekind.lt_of_not_le high
        rw [uniform01_real_initial level (Dedekind.le_of_lt below)]
        have vanish : ∀ position : Nat, (uniform01 fun point : UnitInterval => Dedekind.lt point.val
            (Dedekind.sub (Dedekind.sub level Dedekind.one) (NNReal.toReal (natWeight position)))) =
            ENNReal.zero := by
          intro position
          have empty : (fun point : UnitInterval => Dedekind.lt point.val
              (Dedekind.sub (Dedekind.sub level Dedekind.one)
                (NNReal.toReal (natWeight position)))) = Set.empty := by
            refine Set.ext fun point => ⟨fun early => ?_, False.elim⟩
            have lifted := Dedekind.add_lt_add_right
              (Dedekind.add (NNReal.toReal (natWeight position)) Dedekind.one) early
            have back : Dedekind.add
                (Dedekind.sub (Dedekind.sub level Dedekind.one) (NNReal.toReal (natWeight position)))
                (Dedekind.add (NNReal.toReal (natWeight position)) Dedekind.one) = level := by
              rw [← Dedekind.add_assoc, Dedekind.sub_add_cancel, Dedekind.sub_add_cancel]
            rw [back] at lifted
            have floor := Dedekind.add_le_add
              (Dedekind.add_nonnegative point.property.1 (natWeight position).property)
              (Dedekind.le_refl Dedekind.one)
            rw [Dedekind.zero_add, Dedekind.add_assoc] at floor
            exact Dedekind.not_le_of_lt (Dedekind.lt_of_le_of_lt floor lifted)
              (Dedekind.le_of_lt below)
          rw [empty, Measure.empty_apply]
        simp only [vanish]
        rw [ENNReal.additiveLaws.listSum_map_zero, ENNReal.add_zero]

/-- Summed over the children, the masses below a share's thresholds make `M`
times the share. -/
private theorem systematic_sum_below {κ : Type} (outLanes : Lanes κ) (share : NNReal)
    (atMostOne : NNReal.le share NNReal.one) :
    ENNReal.additiveLaws.listSum (outLanes.list.map fun child =>
        massBelow (systematicBound outLanes child) share) =
      ENNReal.finite (NNReal.mul (natWeight outLanes.count) share) := by
  have reindex : outLanes.list.map (fun child => massBelow (systematicBound outLanes child) share) =
      (List.range outLanes.count).map fun position => uniform01 fun point : UnitInterval =>
        Dedekind.lt point.val
          (Dedekind.sub (NNReal.toReal (NNReal.mul (natWeight outLanes.count) share))
            (NNReal.toReal (natWeight position))) := by
    rw [← childIndex_map outLanes, List.map_map]
    rfl
  have bounded := NNReal.mul_le_mul_left atMostOne (natWeight outLanes.count)
  rw [NNReal.mul_one] at bounded
  rw [reindex, uniform01_tiling outLanes.count
    (NNReal.toReal (NNReal.mul (natWeight outLanes.count) share))
    (NNReal.mul (natWeight outLanes.count) share).property bounded]
  exact ENNReal.ofReal_toReal_finite _

/-- Systematic resampling's offspring counts are unbiased: child `p` reads the
point `(p + u)/M`, and the `M` points meet lane `i`'s interval `M · w_i / W`
times on average. -/
theorem systematic_offspring_unbiased {ι κ : Type} (inLanes : Lanes ι) (outLanes : Lanes κ) :
    OffspringUnbiased inLanes outLanes (systematicAncestors inLanes outLanes space) := by
  intro draws index
  by_cases zero : totalWeight inLanes draws = NNReal.zero
  · rw [zero, weight_eq_zero zero index]
    exact ENNReal.zero_mul _
  · have before := shareBefore_add_le (laneShare inLanes draws) index NNReal.zero inLanes.list
      (inLanes.enumeration.complete index)
    have whole : NNReal.add NNReal.zero
        (NNReal.additiveLaws.listSum (inLanes.list.map (laneShare inLanes draws))) =
        NNReal.one := by
      rw [NNReal.zero_add]
      exact listSum_shares inLanes.list (weights := fun lane => (draws lane).2) zero
    rw [whole] at before
    have sums := ENNReal.additiveLaws.listSum_map_add outLanes.list
      (fun child => uniform01 fun point : UnitInterval =>
        systematicParents inLanes outLanes draws point child = index)
      (fun child => massBelow (systematicBound outLanes child)
        (shareBefore (laneShare inLanes draws) NNReal.zero inLanes.list index))
    simp only [systematic_child_mass inLanes outLanes draws zero index] at sums
    rw [systematic_sum_below outLanes _ before,
      systematic_sum_below outLanes _ (NNReal.le_trans (le_add_self_right _ _) before)] at sums
    have counts : ENNReal.additiveLaws.listSum (outLanes.list.map fun child =>
        systematicAncestors inLanes outLanes space draws (fun parents => parents child = index)) =
        ENNReal.finite (NNReal.mul (natWeight outLanes.count) (laneShare inLanes draws index)) := by
      simp only [systematic_apply inLanes outLanes draws zero]
      refine ENNReal.add_right_cancel_of_finite ?finite (sums.symm.trans ?shape)
      case shape =>
        rw [NNReal.mul_add, NNReal.add_comm]
        rfl
      case finite => exact trivial
    have unit : NNReal.mul outLanes.share (natWeight outLanes.count) = NNReal.one :=
      outLanes.share_mul_count
    rw [counts, ENNReal.finite_mul_finite, ENNReal.finite_mul_finite, ← NNReal.mul_assoc outLanes.share,
      unit, NNReal.one_mul, laneShare, NNReal.mul_div_cancel _ zero]

/-! ### Multinomial ancestors -/

/-- One child's parent: categorical, or `zeroParents` at zero total weight. -/
@[expose] noncomputable def ancestorLane {ι : Type} (inLanes : Lanes ι) (count : Nat)
    [NeZero count] (space : Space α) (child : Fin count) :
    Kernel (populationSpace ι space) (Space.discrete ι) :=
  Kernel.piecewise (zeroTotal inLanes) (zeroTotal_measurable inLanes space)
    (Kernel.const _ (Measure.dirac _ (zeroParents inLanes (Lanes.fin count) child)))
    (categoricalKernel inLanes space)

theorem ancestorLane_positive {ι : Type} (inLanes : Lanes ι) (count : Nat) [NeZero count]
    (space : Space α) (child : Fin count) (draws : ι → α × NNReal)
    (positive : totalWeight inLanes draws ≠ NNReal.zero) :
    ancestorLane inLanes count space child draws =
      categorical inLanes.list fun lane => (draws lane).2 := by
  unfold ancestorLane
  exact Kernel.piecewise_apply_of_not_mem _ _ _ _ draws fun zero =>
    positive ((zeroTotal_iff inLanes draws).mp zero)

/-- Each child's parent is a probability: the Dirac at zero total weight, and
`categorical` otherwise. -/
theorem ancestorLane_markov {ι : Type} (inLanes : Lanes ι) (count : Nat) [NeZero count]
    (space : Space α) (child : Fin count) (draws : ι → α × NNReal) :
    Measure.IsProbability (ancestorLane inLanes count space child draws) := by
  by_cases zero : totalWeight inLanes draws = NNReal.zero
  · unfold ancestorLane
    rw [Kernel.piecewise_apply_of_mem _ _ _ _ draws ((zeroTotal_iff inLanes draws).mpr zero)]
    exact Measure.IsProbability.dirac _ _
  · rw [ancestorLane_positive inLanes count space child draws zero]
    exact categorical_isProbability inLanes.list zero

noncomputable def ancestorLaneFinite {ι : Type} (inLanes : Lanes ι) (count : Nat)
    [NeZero count] (space : Space α) (child : Fin count) :
    Kernel.IsSFinite (ancestorLane inLanes count space child) :=
  Kernel.IsSFinite.ofMarkov (ancestorLane_markov inLanes count space child)

/-- Every child's parent, drawn independently. -/
@[expose] noncomputable def multinomialAncestors {ι : Type} (inLanes : Lanes ι) (count : Nat)
    [NeZero count] (space : Space α) :
    Kernel (populationSpace ι space) (ancestorSpace ι (Fin count)) :=
  Kernel.finProduct count (ancestorLane inLanes count space) (ancestorLaneFinite inLanes count space)

/-- The children's parents form a probability at every population. -/
theorem multinomial_markov {ι : Type} (inLanes : Lanes ι) (count : Nat) [NeZero count]
    (space : Space α) (draws : ι → α × NNReal) :
    Measure.IsProbability (multinomialAncestors inLanes count space draws) :=
  Kernel.finProduct_markov count _ _ (ancestorLane_markov inLanes count space) draws

noncomputable def multinomialFinite {ι : Type} (inLanes : Lanes ι) (count : Nat)
    [NeZero count] (space : Space α) :
    Kernel.IsSFinite (multinomialAncestors inLanes count space) :=
  Kernel.IsSFinite.ofMarkov (multinomial_markov inLanes count space)

theorem multinomial_zero_weight {ι : Type} (inLanes : Lanes ι) (count : Nat) [NeZero count] :
    ZeroWeightPolicy inLanes (multinomialAncestors inLanes count space)
      (zeroParents inLanes (Lanes.fin count)) := fun draws zero =>
  Kernel.finProduct_dirac count _ _ fun _ =>
    Kernel.piecewise_apply_of_mem _ _ _ _ draws ((zeroTotal_iff inLanes draws).mpr zero)

/-- At positive total weight, every child's parent is categorical. -/
theorem multinomial_marginal {ι : Type} (inLanes : Lanes ι) (count : Nat) [NeZero count]
    (draws : ι → α × NNReal) (positive : totalWeight inLanes draws ≠ NNReal.zero)
    (child : Fin count) :
    (multinomialAncestors inLanes count space draws).map (fun parents => parents child)
        (Space.coordinate_measurable (fun _ : Fin count => Space.discrete ι) child) =
      categorical inLanes.list fun lane => (draws lane).2 := by
  apply Measure.ext
  intro region measurable
  have indicatorMeasurable : ENNRealMeasurable (Space.discrete ι)
      (ennrealIndicator region fun _ => ENNReal.one) :=
    ENNRealMeasurable.indicator measurable (ENNRealMeasurable.constant _ ENNReal.one)
  rw [apply_eq_lintegral_indicator ((multinomialAncestors inLanes count space draws).map _ _)
      measurable,
    lintegral_map _ _ _ indicatorMeasurable,
    apply_eq_lintegral_indicator (categorical inLanes.list fun lane => (draws lane).2)
      measurable,
    ← ancestorLane_positive inLanes count space child draws positive]
  exact Kernel.lintegral_finProduct_coordinate count _ _ (ancestorLane_markov inLanes count space)
    child draws _ indicatorMeasurable

theorem multinomial_offspring_unbiased {ι : Type} (inLanes : Lanes ι) (count : Nat)
    [NeZero count] :
    OffspringUnbiased inLanes (Lanes.fin count) (multinomialAncestors inLanes count space) :=
  offspring_unbiased_of_marginals fun draws child positive =>
    multinomial_marginal inLanes count draws positive child

/-- At positive total weight, two distinct children read their parents
independently. -/
theorem multinomial_pair {ι : Type} (inLanes : Lanes ι) (count : Nat) [NeZero count]
    (draws : ι → α × NNReal) (positive : totalWeight inLanes draws ≠ NNReal.zero)
    (first second : Fin count) (distinct : first ≠ second) (function : ι × ι → ENNReal) :
    lintegral (multinomialAncestors inLanes count space draws)
        (fun parents => function (parents first, parents second)) =
      lintegral (categorical inLanes.list fun lane => (draws lane).2) fun parent =>
        lintegral (categorical inLanes.list fun lane => (draws lane).2) fun other =>
          function (parent, other) := by
  have functionMeasurable : ENNRealMeasurable (Space.product (Space.discrete ι) (Space.discrete ι))
      function :=
    ENNRealMeasurable.of_measurableMap (MeasurableMap.uncurry_of_countable_first
      (source := Space.discrete ι) (target := ennrealBorel) inLanes.position
      inLanes.position_injective (function := fun parent other => function (parent, other))
      fun _ => MeasurableMap.from_discrete ennrealBorel _)
  refine (Kernel.lintegral_finProduct_pair count _ _ (ancestorLane_markov inLanes count space)
    first second distinct draws function functionMeasurable).trans ?_
  rw [ancestorLane_positive inLanes count space first draws positive,
    ancestorLane_positive inLanes count space second draws positive]

end

end Problib.Inference
