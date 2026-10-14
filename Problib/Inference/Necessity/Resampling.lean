module

public import Problib.Inference.Resampling.Ancestors
public import Problib.Inference.Necessity.Weighting
set_option autoImplicit false

/-! Necessity for resampling.

A child must carry the mean parent weight `W/N`. Resetting the weight to one
breaks proper weighting outright: a one-lane law with weights `1` and `3` is
properly weighted for `(1/2)δ_false + (3/2)δ_true`, and after the reset it is
properly weighted for no positive multiple of that target
(`reset_weight_not_properlyWeighted`). At one lane the mean weight is the
weight, so `resample` keeps it. A normalizable target does not make a sampled
population's total weight positive, which is why the zero-weight policy is
declared rather than assumed away (`zero_total_positive_target`).

Unbiased offspring counts do not make a resampler consistent. The resampler that
draws one parent and copies it into every child meets the offspring equation,
yet every population it returns holds one value, so its self-normalized
estimate of the indicator of `false` is `0` or `1` surely, from any incoming
law (`singleAncestor_inconsistent`). The uniform target gives that indicator
mass `1/2`. A single fair draw copied into every lane is invariant for the
uniform target and fails the same way (`replicated_sample_inconsistent`).
Multinomial resampling keeps the empirical measure's mean but not the
independence of the lanes: two independent lanes with weights `1` at `false`
and `3` at `true` resample to children that are both `true` with probability
`17/32`, while each child is `true` with probability `5/8`
(`resampled_lanes_dependent`). -/

namespace Problib.Inference.Necessity.Resampling

open Problib.Real Problib.Measure
open Problib.Inference.Necessity.Weighting (bools fair halfMass rationalWeight fair_probability
  lintegral_fair half_ofRat half_sum_ofRat)
open Problib.Analysis (categorical lintegral_categorical)

public section

/-! ### Necessity 1: the reset weight -/

/-- A fair draw with weight `1` at `false` and `3` at `true`. -/
@[expose] noncomputable def unevenLaw : Measure (Space.product bools weightSpace) :=
  fair (Space.product bools weightSpace)
    (false, rationalWeight 1 (by decide +kernel)) (true, rationalWeight 3 (by decide +kernel))

/-- The target it is properly weighted for, `(1/2)δ_false + (3/2)δ_true`. -/
@[expose] noncomputable def unevenTarget : Measure bools :=
  Measure.add (Measure.smul halfMass (Measure.dirac bools false))
    (Measure.smul (ENNReal.ofRat (3 / 2) (by decide +kernel)) (Measure.dirac bools true))

/-- Reset every weight to one. -/
theorem reset_measurable :
    MeasurableMap (Space.product bools weightSpace) (Space.product bools weightSpace)
      (fun draw => (draw.1, NNReal.one)) :=
  Space.pair_measurable (Space.first_measurable bools weightSpace)
    (MeasurableMap.constant _ weightSpace NNReal.one)

/-- The law is properly weighted for the uneven target. After the reset it is
properly weighted for `(1/2)δ_false + (1/2)δ_true`, which is no multiple of the
uneven target, so no scale of the target is properly weighted. -/
theorem reset_weight_not_properlyWeighted :
    ProperlyWeighted unevenTarget unevenLaw ∧
      ∀ scale : ENNReal,
        ¬ProperlyWeighted (Measure.smul scale unevenTarget)
          (unevenLaw.map (fun draw => (draw.1, NNReal.one)) reset_measurable) := by
  have targetIntegral : ∀ function : Bool → ENNReal, lintegral unevenTarget function =
      ENNReal.add (ENNReal.mul halfMass (function false))
        (ENNReal.mul (ENNReal.ofRat (3 / 2) (by decide +kernel)) (function true)) := by
    intro function
    have measurable := ENNRealMeasurable.of_measurableMap
      (MeasurableMap.from_discrete ennrealBorel function)
    rw [unevenTarget, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
      lintegral_dirac _ _ measurable, lintegral_dirac _ _ measurable]
  have properlyWeighted : ProperlyWeighted unevenTarget unevenLaw := by
    refine properlyWeighted_iff_lintegral.mpr ⟨fair_probability _ _ _, fun function measurable => ?_⟩
    rw [unevenLaw, lintegral_fair _ _ _ (weighted_integrand_measurable measurable),
      targetIntegral]
    show ENNReal.mul halfMass (ENNReal.add
        (ENNReal.mul (ENNReal.ofRat 1 (by decide +kernel)) (function false))
        (ENNReal.mul (ENNReal.ofRat 3 (by decide +kernel)) (function true))) = _
    rw [ENNReal.mul_add, ← ENNReal.mul_assoc, ← ENNReal.mul_assoc,
      half_ofRat 1 (1 / 2) _ (by decide +kernel) (by decide +kernel),
      half_ofRat 3 (3 / 2) _ (by decide +kernel) (by decide +kernel)]
    rfl
  refine ⟨properlyWeighted, fun scale reset => ?_⟩
  -- The reset law is the fair choice of `(false, 1)` and `(true, 1)`. Reading it
  -- at the indicator of `false` gives `1/2 = c/2`, and at the indicator of
  -- `true` it gives `1/2 = 3c/2`, so `1/2 = 3/2`.
  have resetLaw : unevenLaw.map (fun draw => (draw.1, NNReal.one)) reset_measurable =
      fair (Space.product bools weightSpace) (false, NNReal.one) (true, NNReal.one) := by
    rw [unevenLaw, fair, Measure.map_smul, Measure.map_add, Measure.map_dirac, Measure.map_dirac]
    rfl
  rw [resetLaw] at reset
  have indicator : ∀ function : Bool → ENNReal,
      ENNReal.mul halfMass (ENNReal.add (ENNReal.mul ENNReal.one (function false))
          (ENNReal.mul ENNReal.one (function true))) =
        ENNReal.mul scale (ENNReal.add (ENNReal.mul halfMass (function false))
          (ENNReal.mul (ENNReal.ofRat (3 / 2) (by decide +kernel)) (function true))) := by
    intro function
    have measurable := ENNRealMeasurable.of_measurableMap
      (MeasurableMap.from_discrete ennrealBorel function)
    have equation := reset.lintegral measurable
    rw [lintegral_fair _ _ _ (weighted_integrand_measurable measurable), lintegral_smul_measure,
      targetIntegral] at equation
    exact equation
  have falseEquation := indicator fun value => if value then ENNReal.zero else ENNReal.one
  have trueEquation := indicator fun value => if value then ENNReal.one else ENNReal.zero
  change ENNReal.mul halfMass (ENNReal.add (ENNReal.mul ENNReal.one ENNReal.one)
      (ENNReal.mul ENNReal.one ENNReal.zero)) =
    ENNReal.mul scale (ENNReal.add (ENNReal.mul halfMass ENNReal.one)
      (ENNReal.mul (ENNReal.ofRat (3 / 2) (by decide +kernel)) ENNReal.zero)) at falseEquation
  change ENNReal.mul halfMass (ENNReal.add (ENNReal.mul ENNReal.one ENNReal.zero)
      (ENNReal.mul ENNReal.one ENNReal.one)) =
    ENNReal.mul scale (ENNReal.add (ENNReal.mul halfMass ENNReal.zero)
      (ENNReal.mul (ENNReal.ofRat (3 / 2) (by decide +kernel)) ENNReal.one)) at trueEquation
  simp only [ENNReal.mul_one, ENNReal.mul_zero, ENNReal.add_zero, ENNReal.zero_add]
    at falseEquation trueEquation
  rw [← half_ofRat 3 (3 / 2) (by decide +kernel) (by decide +kernel) (by decide +kernel),
    ENNReal.mul_comm halfMass, ← ENNReal.mul_assoc, ENNReal.mul_comm scale,
    ENNReal.mul_assoc, ← falseEquation, ENNReal.mul_comm,
    half_ofRat 3 (3 / 2) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
    at trueEquation
  have bound : ENNReal.le (ENNReal.ofRat (3 / 2) (by decide +kernel))
      (ENNReal.ofRat (1 / 2) (by decide +kernel)) := by
    rw [← trueEquation]
    exact ENNReal.le_refl _
  exact absurd ((ENNReal.ofRat_le_iff _ _ _ _).mp bound) (by decide +kernel)

/-! ### Necessity 7: a zero total with a positive target -/

/-- One lane. -/
@[expose] def oneLane : Lanes (Fin 1) := Lanes.fin 1

/-- One-lane importance draws from the fair coin for `δ_true`: weight `0` at
`false` and `2` at `true`. -/
@[expose] noncomputable def zeroOrTwo : Measure (populationSpace (Fin 1) bools) :=
  fair (populationSpace (Fin 1) bools)
    (fun _ => (false, NNReal.zero)) (fun _ => (true, rationalWeight 2 (by decide +kernel)))

/-- The population is invariant for `δ_true`, whose mass is one, and its total
weight is zero with probability one half. -/
theorem zero_total_positive_target :
    EmpiricalInvariant oneLane (Measure.dirac bools true) zeroOrTwo ∧
      zeroOrTwo (fun draws => totalWeight oneLane draws = NNReal.zero) = halfMass := by
  have single : ∀ values : Fin 1 → ENNReal,
      ENNReal.mul (ENNReal.finite oneLane.share)
          (ENNReal.additiveLaws.listSum (oneLane.list.map values)) = values 0 :=
    fun values => oneLane.average_const (values 0)
  refine ⟨⟨fair_probability _ _ _, ?_⟩, ?_⟩
  · refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
    rw [Measure.lintegral_bind _ _ measurable, zeroOrTwo,
      lintegral_fair _ _ _ (Kernel.lintegral_measurable _ measurable),
      lintegral_empirical oneLane _ measurable, lintegral_empirical oneLane _ measurable,
      single, single, lintegral_dirac _ _ measurable]
    show ENNReal.mul halfMass (ENNReal.add (ENNReal.mul ENNReal.zero (function false))
        (ENNReal.mul (ENNReal.ofRat 2 (by decide +kernel)) (function true))) = function true
    rw [ENNReal.zero_mul, ENNReal.zero_add, ← ENNReal.mul_assoc,
      half_ofRat 2 1 _ (by decide +kernel) (by decide +kernel), ENNReal.ofRat_one,
      ENNReal.one_mul]
  · have region : (populationSpace (Fin 1) bools).Measurable
        (fun draws => totalWeight oneLane draws = NNReal.zero) := by
      have preimage := (finite_weight_measurable
        (totalWeight_measurable oneLane bools)).singleton ENNReal.zero
      have same : (fun draws : Fin 1 → Bool × NNReal => totalWeight oneLane draws = NNReal.zero) =
          Set.preimage (fun draws => ENNReal.finite (totalWeight oneLane draws))
            (ennrealSingleton ENNReal.zero) :=
        funext fun draws =>
          propext ⟨congrArg ENNReal.finite, fun equal => ENNReal.finite_injective equal⟩
      rw [same]
      exact preimage
    rw [zeroOrTwo, fair, Measure.smul_apply_measurable _ _ region,
      Measure.add_apply_measurable _ _ region,
      Measure.dirac_apply_of_mem _ _ region (by
        show NNReal.add NNReal.zero NNReal.zero = NNReal.zero
        exact NNReal.add_zero _),
      Measure.dirac_apply_of_not_mem _ _ region (by
        intro zero
        have ordered := (NNReal.ofRat_lt_iff 0 2 (by decide +kernel) (by decide +kernel)).mpr
          (by decide +kernel)
        have same : NNReal.ofRat 2 (by decide +kernel) = NNReal.zero :=
          (NNReal.add_zero _).symm.trans zero
        rw [NNReal.ofRat_zero, same] at ordered
        exact NNReal.lt_irrefl _ ordered),
      ENNReal.add_zero, ENNReal.mul_one]

/-! ### Shared arithmetic -/

private theorem ofRat_ne_zero (value : Rat) (nonnegative : 0 ≤ value) (positive : 0 < value) :
    NNReal.ofRat value nonnegative ≠ NNReal.zero := by
  intro zero
  have ordered := (NNReal.ofRat_lt_iff 0 value (by decide +kernel) nonnegative).mpr positive
  rw [NNReal.ofRat_zero, zero] at ordered
  exact NNReal.lt_irrefl _ ordered

/-- Two rational weights, summed over two lanes. -/
private theorem weights_add (first second total : Rat) (firstNonnegative : 0 ≤ first)
    (secondNonnegative : 0 ≤ second) (totalNonnegative : 0 ≤ total)
    (same : first + second = total) :
    NNReal.add (NNReal.ofRat first firstNonnegative)
        (NNReal.add (NNReal.ofRat second secondNonnegative) NNReal.zero) =
      NNReal.ofRat total totalNonnegative := by
  rw [NNReal.add_zero, ← NNReal.ofRat_add]
  subst same
  rfl

/-- A rational weight over a positive rational total. -/
private theorem weight_ratio (weight total quotient : Rat) (weightNonnegative : 0 ≤ weight)
    (totalNonnegative : 0 ≤ total) (quotientNonnegative : 0 ≤ quotient) (positive : 0 < total)
    (same : quotient * total = weight) :
    NNReal.div (NNReal.ofRat weight weightNonnegative) (NNReal.ofRat total totalNonnegative) =
      NNReal.ofRat quotient quotientNonnegative := by
  have nonzero := ofRat_ne_zero total totalNonnegative positive
  apply NNReal.mul_right_cancel nonzero
  rw [NNReal.div_mul_cancel _ nonzero, ← NNReal.ofRat_mul]
  subst same
  rfl

private theorem ofRat_same {left right : Rat} (equal : left = right) {leftNonnegative : 0 ≤ left}
    {rightNonnegative : 0 ≤ right} :
    ENNReal.ofRat left leftNonnegative = ENNReal.ofRat right rightNonnegative := by
  subst equal
  rfl

/-- A rational square. -/
private theorem square_ofRat (value square : Rat) (nonnegative : 0 ≤ value)
    (squareNonnegative : 0 ≤ square) (same : value * value = square) :
    ENNReal.mul (ENNReal.ofRat value nonnegative) (ENNReal.ofRat value nonnegative) =
      ENNReal.ofRat square squareNonnegative := by
  rw [← ENNReal.ofRat_mul]
  subst same
  rfl

private theorem half_two : ENNReal.mul halfMass (ENNReal.add ENNReal.one ENNReal.one) = ENNReal.one := by
  rw [← ENNReal.ofRat_one, half_sum_ofRat 1 1 1 _ _ _ (by decide +kernel)]

/-- Half of a doubled value. -/
private theorem halve (value : ENNReal) : ENNReal.mul halfMass (ENNReal.add value value) = value := by
  rw [← ENNReal.mul_one value, ← ENNReal.mul_add, ← ENNReal.mul_assoc, ENNReal.mul_comm halfMass,
    ENNReal.mul_assoc, half_two]

/-! ### Necessity 4: one ancestor for every child -/

/-- The self-normalized estimate of the indicator of `false`: the weight on
`false` over the total weight, and zero at total weight zero. -/
@[expose] noncomputable def falseEstimate {κ : Type} (lanes : Lanes κ)
    (draws : κ → Bool × NNReal) : NNReal :=
  NNReal.div (NNReal.additiveLaws.listSum (lanes.list.map fun lane =>
      if (draws lane).1 then NNReal.zero else (draws lane).2))
    (totalWeight lanes draws)

/-- Some lane holds `value`. -/
@[expose] def holds {κ : Type} (list : List κ) (value : Bool) : Set (κ → Bool × NNReal) :=
  fun draws => ∃ lane ∈ list, (draws lane).1 = value

/-- Some lane holds `true` and some lane holds `false`. -/
@[expose] def Mixed {κ : Type} (lanes : Lanes κ) : Set (κ → Bool × NNReal) :=
  Set.inter (holds lanes.list true) (holds lanes.list false)

private theorem holds_measurable {κ : Type} (value : Bool) :
    ∀ list : List κ, (populationSpace κ bools).Measurable (holds list value)
  | [] => by
      have same : holds ([] : List κ) value = Set.empty :=
        Set.ext fun _ => ⟨fun ⟨_, member, _⟩ => (nomatch member), False.elim⟩
      rw [same]
      exact (populationSpace κ bools).empty
  | head :: tail => by
      have same : holds (head :: tail) value =
          Set.union (Set.preimage (fun draws : κ → Bool × NNReal => (draws head).1)
            (fun current => current = value)) (holds tail value) := by
        refine Set.ext fun draws => ⟨fun ⟨lane, member, equal⟩ => ?_, fun member => ?_⟩
        · rcases List.mem_cons.mp member with first | later
          · subst first
            exact Or.inl equal
          · exact Or.inr ⟨lane, later, equal⟩
        · rcases member with equal | ⟨lane, later, equal⟩
          · exact ⟨head, List.mem_cons_self, equal⟩
          · exact ⟨lane, List.mem_cons_of_mem _ later, equal⟩
      rw [same]
      exact (populationSpace κ bools).union
        ((MeasurableMap.comp (Space.first_measurable bools weightSpace)
          (lane_measurable bools head)) (Space.discrete_measurable _))
        (holds_measurable value tail)

theorem mixed_measurable {κ : Type} (lanes : Lanes κ) :
    (populationSpace κ bools).Measurable (Mixed lanes) :=
  (populationSpace κ bools).inter (holds_measurable true lanes.list)
    (holds_measurable false lanes.list)

/-- A population that is not mixed estimates the indicator of `false` as `0`
or `1`. -/
theorem falseEstimate_of_not_mixed {κ : Type} (lanes : Lanes κ) (draws : κ → Bool × NNReal)
    (single : ¬Mixed lanes draws) :
    falseEstimate lanes draws = NNReal.zero ∨ falseEstimate lanes draws = NNReal.one := by
  by_cases someTrue : holds lanes.list true draws
  · -- Every lane holds `true`, so the weight on `false` is zero.
    have allTrue : ∀ lane ∈ lanes.list, (draws lane).1 = true := by
      intro lane member
      cases value : (draws lane).1 with
      | true => rfl
      | false => exact absurd ⟨someTrue, ⟨lane, member, value⟩⟩ single
    left
    unfold falseEstimate
    have numerator : (NNReal.additiveLaws.listSum (lanes.list.map fun lane =>
        if (draws lane).1 then NNReal.zero else (draws lane).2)) =
        NNReal.zero := by
      exact NNReal.additiveLaws.listSum_map_eq_zero lanes.list _ fun lane member => by
        rw [allTrue lane member]
        rfl
    rw [numerator, NNReal.zero_div]
  · -- Every lane holds `false`, so the weight on `false` is the total weight.
    have allFalse : ∀ lane ∈ lanes.list, (draws lane).1 = false := by
      intro lane member
      cases value : (draws lane).1 with
      | false => rfl
      | true => exact absurd ⟨lane, member, value⟩ someTrue
    have numerator : (NNReal.additiveLaws.listSum (lanes.list.map fun lane =>
        if (draws lane).1 then NNReal.zero else (draws lane).2)) =
        totalWeight lanes draws :=
      NNReal.additiveLaws.listSum_map_congr lanes.list fun lane member => by
        rw [allFalse lane member]
        rfl
    unfold falseEstimate
    rw [numerator]
    by_cases zero : totalWeight lanes draws = NNReal.zero
    · left
      rw [zero, NNReal.zero_div]
    · right
      exact NNReal.div_self zero

/-- The estimate is neither `0` nor `1`. -/
@[expose] def Undecided {κ : Type} (lanes : Lanes κ) : Set (κ → Bool × NNReal) :=
  fun draws => falseEstimate lanes draws ≠ NNReal.zero ∧ falseEstimate lanes draws ≠ NNReal.one

private theorem undecided_mixed {κ : Type} (lanes : Lanes κ) :
    Set.Subset (Undecided lanes) (Mixed lanes) := by
  intro draws undecided
  refine Classical.byContradiction fun single => ?_
  rcases falseEstimate_of_not_mixed lanes draws single with zero | one
  · exact undecided.1 zero
  · exact undecided.2 one

/-- A law that never returns a mixed population never returns an undecided
estimate. -/
private theorem undecided_null {κ : Type} (lanes : Lanes κ) (measure : Measure (populationSpace κ bools))
    (unmixed : measure (Mixed lanes) = ENNReal.zero) : measure (Undecided lanes) = ENNReal.zero := by
  have bound := Measure.mono measure (undecided_mixed lanes)
  rw [unmixed] at bound
  exact ENNReal.le_antisymm bound (ENNReal.zero_le _)

/-- A law on single values, copied into every lane, returns no mixed population. -/
private theorem copies_unmixed {κ β : Type} {source : Space β} (lanes : Lanes κ) (measure : Measure source)
    (copy : β → Bool × NNReal)
    (copyMeasurable : MeasurableMap source (populationSpace κ bools) fun value (_ : κ) => copy value) :
    (measure.map (fun value (_ : κ) => copy value) copyMeasurable) (Mixed lanes) = ENNReal.zero := by
  have empty : Set.preimage (fun value (_ : κ) => copy value) (Mixed lanes) = Set.empty :=
    Set.ext fun _ => ⟨fun ⟨⟨_, _, holdsTrue⟩, ⟨_, _, holdsFalse⟩⟩ =>
      (nomatch holdsTrue.symm.trans holdsFalse), False.elim⟩
  rw [Measure.map_apply _ _ _ (mixed_measurable lanes), empty, Measure.empty_apply]

/-- One parent, drawn from `categorical`, copied into every child. -/
@[expose] noncomputable def singleAncestor {ι : Type} (inLanes : Lanes ι) (count : Nat)
    [NeZero count] :
    Kernel (populationSpace ι bools) (ancestorSpace ι (Fin count)) :=
  (ancestorLane inLanes count bools 0).map (fun parent (_ : Fin count) => parent)
    (MeasurableMap.from_discrete _ _)

theorem singleAncestor_markov {ι : Type} (inLanes : Lanes ι) (count : Nat) [NeZero count]
    (draws : ι → Bool × NNReal) : Measure.IsProbability (singleAncestor inLanes count draws) :=
  (ancestorLane_markov inLanes count bools 0 draws).map (fun parent (_ : Fin count) => parent)
    (MeasurableMap.from_discrete _ _)

noncomputable def singleAncestorFinite {ι : Type} (inLanes : Lanes ι) (count : Nat)
    [NeZero count] : Kernel.IsSFinite (singleAncestor inLanes count) :=
  Kernel.IsSFinite.ofMarkov (singleAncestor_markov inLanes count)

/-- Every child's parent is categorical, so the offspring counts are
unbiased. -/
theorem singleAncestor_unbiased {ι : Type} (inLanes : Lanes ι) (count : Nat) [NeZero count] :
    OffspringUnbiased inLanes (Lanes.fin count) (singleAncestor inLanes count) :=
  offspring_unbiased_of_marginals fun draws child positive => by
    rw [singleAncestor, Kernel.map_apply _ _ (MeasurableMap.from_discrete _ _), Measure.map_comp,
      ← ancestorLane_positive inLanes count bools 0 draws positive]
    exact Measure.map_id _

/-- The single-ancestor resampler has unbiased offspring counts, and from any
incoming law its estimate of the indicator of `false` is `0` or `1` surely. -/
theorem singleAncestor_inconsistent {ι : Type} (inLanes : Lanes ι) (count : Nat) [NeZero count] :
    OffspringUnbiased inLanes (Lanes.fin count) (singleAncestor inLanes count) ∧
      ∀ population : Measure (populationSpace ι bools),
        population.bind (resample inLanes (singleAncestor inLanes count)
          (singleAncestorFinite inLanes count)) (Undecided (Lanes.fin count)) = ENNReal.zero := by
  refine ⟨singleAncestor_unbiased inLanes count, fun population => undecided_null _ _ ?_⟩
  have each : ∀ draws, resample inLanes (singleAncestor inLanes count)
      (singleAncestorFinite inLanes count) draws (Mixed (Lanes.fin count)) = ENNReal.zero := by
    intro draws
    rw [resample_apply, singleAncestor, Kernel.map_apply _ _ (MeasurableMap.from_discrete _ _),
      Measure.map_comp]
    exact copies_unmixed _ _ (fun parent => ((draws parent).1, meanWeight inLanes draws)) _
  rw [Measure.bind_apply _ _ (mixed_measurable _), lintegral_congr _ each, lintegral_zero]

/-- A fair draw of `false` or `true` at weight one. -/
@[expose] noncomputable def fairDraw : Measure (Space.product bools weightSpace) :=
  fair (Space.product bools weightSpace) (false, NNReal.one) (true, NNReal.one)

/-- One fair draw copied into every lane. -/
@[expose] noncomputable def replicated {κ : Type} : Measure (populationSpace κ bools) :=
  fairDraw.map (fun draw (_ : κ) => draw) (Space.pi_measurable fun _ => MeasurableMap.identity _)

/-- A single draw replicated into every lane is invariant for the uniform
target, and its estimate of the indicator of `false` is `0` or `1` surely. -/
theorem replicated_sample_inconsistent {κ : Type} (lanes : Lanes κ) :
    EmpiricalInvariant lanes (fair bools false true) (replicated (κ := κ)) ∧
      replicated (κ := κ) (Undecided lanes) = ENNReal.zero := by
  have properlyWeighted : ProperlyWeighted (fair bools false true) fairDraw := by
    refine properlyWeighted_iff_lintegral.mpr ⟨fair_probability _ _ _, fun function measurable => ?_⟩
    rw [fairDraw, lintegral_fair _ _ _ (weighted_integrand_measurable measurable),
      lintegral_fair _ _ _ measurable]
    show ENNReal.mul halfMass (ENNReal.add (ENNReal.mul ENNReal.one (function false))
        (ENNReal.mul ENNReal.one (function true))) = _
    rw [ENNReal.one_mul, ENNReal.one_mul]
  have copyMeasurable : MeasurableMap (Space.product bools weightSpace) (populationSpace κ bools)
      fun draw (_ : κ) => draw :=
    Space.pi_measurable fun _ => MeasurableMap.identity _
  refine ⟨empirical_replicate ((fair_probability _ _ _).map _ copyMeasurable) (fun index => ?_)
      properlyWeighted, undecided_null _ _ (copies_unmixed lanes fairDraw (fun draw => draw) copyMeasurable)⟩
  rw [replicated, Measure.map_comp _ _ _ copyMeasurable]
  exact Measure.map_id _

/-! ### Necessity 10: dependent resampled lanes -/

/-- A population of two lanes. -/
@[expose] def twoLanes (first second : Bool × NNReal) : Fin 2 → Bool × NNReal :=
  fun lane => if lane.val = 0 then first else second

/-- The draw `(false, 1)`. -/
@[expose] noncomputable def lowDraw : Bool × NNReal := (false, rationalWeight 1 (by decide +kernel))

/-- The draw `(true, 3)`. -/
@[expose] noncomputable def highDraw : Bool × NNReal := (true, rationalWeight 3 (by decide +kernel))

/-- Two lanes drawn independently from `unevenLaw`: each of the four
populations with probability one quarter. -/
@[expose] noncomputable def twoLaneLaw : Measure (populationSpace (Fin 2) bools) :=
  Measure.smul halfMass (Measure.add
    (fair _ (twoLanes lowDraw lowDraw) (twoLanes lowDraw highDraw))
    (fair _ (twoLanes highDraw lowDraw) (twoLanes highDraw highDraw)))

private theorem lintegral_twoLaneLaw {function : (Fin 2 → Bool × NNReal) → ENNReal}
    (measurable : ENNRealMeasurable (populationSpace (Fin 2) bools) function) :
    lintegral twoLaneLaw function =
      ENNReal.mul halfMass (ENNReal.add
        (ENNReal.mul halfMass (ENNReal.add (function (twoLanes lowDraw lowDraw))
          (function (twoLanes lowDraw highDraw))))
        (ENNReal.mul halfMass (ENNReal.add (function (twoLanes highDraw lowDraw))
          (function (twoLanes highDraw highDraw))))) := by
  rw [twoLaneLaw, lintegral_smul_measure, lintegral_add_measure, lintegral_fair _ _ _ measurable,
    lintegral_fair _ _ _ measurable]

private theorem twoLaneLaw_probability : Measure.IsProbability twoLaneLaw := by
  constructor
  have univ := (populationSpace (Fin 2) bools).univ
  rw [twoLaneLaw, Measure.smul_apply_measurable _ _ univ, Measure.add_apply_measurable _ _ univ,
    (fair_probability _ _ _).univ_eq_one, (fair_probability _ _ _).univ_eq_one, half_two]

/-- Each lane of `twoLaneLaw` is `unevenLaw`, so the population is invariant for
`unevenTarget`. -/
private theorem twoLaneLaw_invariant : EmpiricalInvariant (Lanes.fin 2) unevenTarget twoLaneLaw := by
  refine empirical_replicate twoLaneLaw_probability (fun index => ?_) reset_weight_not_properlyWeighted.1
  refine (Measure.eq_iff_lintegral _ _).mpr fun function measurable => ?_
  rw [lintegral_map _ _ _ measurable, lintegral_twoLaneLaw (measurable.comp (lane_measurable _ index)),
    unevenLaw, lintegral_fair _ _ _ measurable]
  match index with
  | ⟨0, _⟩ =>
      show ENNReal.mul halfMass (ENNReal.add
          (ENNReal.mul halfMass (ENNReal.add (function lowDraw) (function lowDraw)))
          (ENNReal.mul halfMass (ENNReal.add (function highDraw) (function highDraw)))) =
        ENNReal.mul halfMass (ENNReal.add (function lowDraw) (function highDraw))
      rw [halve, halve]
  | ⟨1, _⟩ =>
      show ENNReal.mul halfMass (ENNReal.add
          (ENNReal.mul halfMass (ENNReal.add (function lowDraw) (function highDraw)))
          (ENNReal.mul halfMass (ENNReal.add (function lowDraw) (function highDraw)))) =
        ENNReal.mul halfMass (ENNReal.add (function lowDraw) (function highDraw))
      rw [halve]

/-- Multinomial resampling of two lanes into two children. -/
@[expose] noncomputable def resampledTwo :
    Kernel (populationSpace (Fin 2) bools) (populationSpace (Fin 2) bools) :=
  resample (Lanes.fin 2) (multinomialAncestors (Lanes.fin 2) 2 bools)
    (multinomialFinite (Lanes.fin 2) 2 bools)

/-- Child `child` holds `true`. -/
@[expose] def childTrue (child : Fin 2) : Set (Fin 2 → Bool × NNReal) :=
  fun draws => (draws child).1 = true

/-- Both children hold `true`. -/
@[expose] def bothTrue : Set (Fin 2 → Bool × NNReal) :=
  Set.inter (childTrue 0) (childTrue 1)

private theorem childTrue_measurable (child : Fin 2) :
    (populationSpace (Fin 2) bools).Measurable (childTrue child) :=
  (MeasurableMap.comp (Space.first_measurable bools weightSpace) (lane_measurable bools child))
    (Space.discrete_measurable fun value : Bool => value = true)

private theorem bothTrue_measurable : (populationSpace (Fin 2) bools).Measurable bothTrue :=
  (populationSpace (Fin 2) bools).inter (childTrue_measurable 0) (childTrue_measurable 1)

/-- The indicator of a lane holding `true`. -/
@[expose] noncomputable def trueAt (draws : Fin 2 → Bool × NNReal) (lane : Fin 2) : ENNReal :=
  if (draws lane).1 then ENNReal.one else ENNReal.zero

/-- The categorical mass of the lanes holding `true`. -/
@[expose] noncomputable def trueMass (draws : Fin 2 → Bool × NNReal) : ENNReal :=
  lintegral (categorical (Lanes.fin 2).list fun lane => (draws lane).2) (trueAt draws)

private theorem indicator_trueAt (draws : Fin 2 → Bool × NNReal) (lane : Fin 2) :
    ennrealIndicator (fun lane : Fin 2 => (draws lane).1 = true) (fun _ => ENNReal.one) lane =
      trueAt draws lane := by
  unfold ennrealIndicator ennrealPiecewise trueAt
  by_cases holdsTrue : (draws lane).1 = true
  · rw [ite_eq_left holdsTrue, ite_eq_left holdsTrue]
  · rw [ite_eq_right holdsTrue, ite_eq_right holdsTrue]

/-- At positive total weight, each child holds `true` with the categorical mass
of the lanes holding `true`. -/
private theorem resampledTwo_child (draws : Fin 2 → Bool × NNReal)
    (positive : totalWeight (Lanes.fin 2) draws ≠ NNReal.zero) (child : Fin 2) :
    resampledTwo draws (childTrue child) = trueMass draws := by
  have region : (Space.discrete (Fin 2)).Measurable fun lane : Fin 2 => (draws lane).1 = true :=
    Space.discrete_measurable _
  have marginal := Measure.map_apply (multinomialAncestors (Lanes.fin 2) 2 bools draws)
    (fun parents => parents child)
    (Space.coordinate_measurable (fun _ : Fin 2 => Space.discrete (Fin 2)) child) region
  rw [multinomial_marginal (Lanes.fin 2) 2 draws positive child] at marginal
  have mass := apply_eq_lintegral_indicator
    (categorical (Lanes.fin 2).list fun lane => (draws lane).2) region
  rw [lintegral_congr _ (indicator_trueAt draws)] at mass
  rw [resampledTwo, resample_apply, Measure.map_apply _ _ _ (childTrue_measurable child), trueMass,
    ← mass, marginal]
  rfl

/-- At positive total weight, both children hold `true` with the square of that
mass. -/
private theorem resampledTwo_both (draws : Fin 2 → Bool × NNReal)
    (positive : totalWeight (Lanes.fin 2) draws ≠ NNReal.zero) :
    resampledTwo draws bothTrue = ENNReal.mul (trueMass draws) (trueMass draws) := by
  have indicatorMeasurable : ENNRealMeasurable (populationSpace (Fin 2) bools)
      (ennrealIndicator bothTrue fun _ => ENNReal.one) :=
    ENNRealMeasurable.indicator bothTrue_measurable (ENNRealMeasurable.constant _ ENNReal.one)
  have laneMeasurable : ENNRealMeasurable (Space.discrete (Fin 2)) (trueAt draws) :=
    ENNRealMeasurable.of_measurableMap (MeasurableMap.from_discrete ennrealBorel _)
  have pointwise : ∀ parents : Fin 2 → Fin 2,
      ennrealIndicator bothTrue (fun _ => ENNReal.one)
          (fun child => ((draws (parents child)).1, meanWeight (Lanes.fin 2) draws)) =
        (fun pair : Fin 2 × Fin 2 => ENNReal.mul (trueAt draws pair.1) (trueAt draws pair.2))
          (parents 0, parents 1) := by
    intro parents
    unfold ennrealIndicator ennrealPiecewise trueAt bothTrue childTrue Set.inter
    dsimp only
    by_cases first : (draws (parents 0)).1 = true <;>
      by_cases second : (draws (parents 1)).1 = true
    · rw [ite_eq_left ⟨first, second⟩, ite_eq_left first, ite_eq_left second, ENNReal.mul_one]
    · rw [ite_eq_right fun both => second both.2, ite_eq_left first, ite_eq_right second, ENNReal.mul_zero]
    · rw [ite_eq_right fun both => first both.1, ite_eq_right first, ite_eq_left second, ENNReal.zero_mul]
    · rw [ite_eq_right fun both => first both.1, ite_eq_right first, ite_eq_right second, ENNReal.zero_mul]
  rw [apply_eq_lintegral_indicator _ bothTrue_measurable, resampledTwo, resample_apply,
    lintegral_map _ _ _ indicatorMeasurable, lintegral_congr _ pointwise,
    multinomial_pair (Lanes.fin 2) 2 draws positive 0 1 (by decide)
      (fun pair : Fin 2 × Fin 2 => ENNReal.mul (trueAt draws pair.1) (trueAt draws pair.2))]
  have inner : ∀ parent, lintegral (categorical (Lanes.fin 2).list fun lane => (draws lane).2)
      (fun other => ENNReal.mul (trueAt draws parent) (trueAt draws other)) =
      ENNReal.mul (trueMass draws) (trueAt draws parent) := by
    intro parent
    rw [lintegral_smul _ _ laneMeasurable, ENNReal.mul_comm]
    rfl
  simp only [inner]
  rw [lintegral_smul _ _ laneMeasurable]
  rfl

/-- The categorical mass of `true` over two lanes, as a finite sum. -/
private theorem trueMass_two (first second : Bool × NNReal) :
    trueMass (twoLanes first second) =
      ENNReal.add (ENNReal.mul (ENNReal.finite (NNReal.div first.2
          (NNReal.add first.2 (NNReal.add second.2 NNReal.zero))))
          (if first.1 then ENNReal.one else ENNReal.zero))
        (ENNReal.add (ENNReal.mul (ENNReal.finite (NNReal.div second.2
          (NNReal.add first.2 (NNReal.add second.2 NNReal.zero))))
          (if second.1 then ENNReal.one else ENNReal.zero)) ENNReal.zero) := by
  rw [trueMass, lintegral_categorical]
  rfl

private theorem total_two (first second : Bool × NNReal) :
    totalWeight (Lanes.fin 2) (twoLanes first second) =
      NNReal.add first.2 (NNReal.add second.2 NNReal.zero) :=
  rfl

private theorem positive_two (first second total : Rat) (firstNonnegative : 0 ≤ first)
    (secondNonnegative : 0 ≤ second) (totalNonnegative : 0 ≤ total) (value value' : Bool)
    (same : first + second = total) (positive : 0 < total) :
    totalWeight (Lanes.fin 2) (twoLanes (value, NNReal.ofRat first firstNonnegative)
      (value', NNReal.ofRat second secondNonnegative)) ≠ NNReal.zero := by
  rw [total_two]
  show NNReal.add (NNReal.ofRat first firstNonnegative)
      (NNReal.add (NNReal.ofRat second secondNonnegative) NNReal.zero) ≠ NNReal.zero
  rw [weights_add first second total firstNonnegative secondNonnegative totalNonnegative same]
  exact ofRat_ne_zero total totalNonnegative positive

private theorem trueMass_lowLow :
    trueMass (twoLanes lowDraw lowDraw) = ENNReal.ofRat 0 (by decide +kernel) := by
  rw [trueMass_two]
  show ENNReal.add (ENNReal.mul _ ENNReal.zero) (ENNReal.add (ENNReal.mul _ ENNReal.zero) ENNReal.zero) = _
  rw [ENNReal.mul_zero, ENNReal.add_zero, ENNReal.add_zero, ENNReal.ofRat_zero]

private theorem trueMass_lowHigh :
    trueMass (twoLanes lowDraw highDraw) = ENNReal.ofRat (3 / 4) (by decide +kernel) := by
  rw [trueMass_two]
  show ENNReal.add (ENNReal.mul _ ENNReal.zero)
      (ENNReal.add (ENNReal.mul (ENNReal.finite (NNReal.div (NNReal.ofRat 3 (by decide +kernel))
        (NNReal.add (NNReal.ofRat 1 (by decide +kernel))
          (NNReal.add (NNReal.ofRat 3 (by decide +kernel)) NNReal.zero)))) ENNReal.one)
        ENNReal.zero) = _
  rw [ENNReal.mul_zero, ENNReal.zero_add, ENNReal.add_zero, ENNReal.mul_one,
    weights_add 1 3 4 _ _ (by decide +kernel) (by decide +kernel),
    weight_ratio 3 4 (3 / 4) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  rfl

private theorem trueMass_highLow :
    trueMass (twoLanes highDraw lowDraw) = ENNReal.ofRat (3 / 4) (by decide +kernel) := by
  rw [trueMass_two]
  show ENNReal.add (ENNReal.mul (ENNReal.finite (NNReal.div (NNReal.ofRat 3 (by decide +kernel))
        (NNReal.add (NNReal.ofRat 3 (by decide +kernel))
          (NNReal.add (NNReal.ofRat 1 (by decide +kernel)) NNReal.zero)))) ENNReal.one)
      (ENNReal.add (ENNReal.mul _ ENNReal.zero) ENNReal.zero) = _
  rw [ENNReal.mul_zero, ENNReal.add_zero, ENNReal.add_zero, ENNReal.mul_one,
    weights_add 3 1 4 _ _ (by decide +kernel) (by decide +kernel),
    weight_ratio 3 4 (3 / 4) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  rfl

private theorem trueMass_highHigh :
    trueMass (twoLanes highDraw highDraw) = ENNReal.ofRat 1 (by decide +kernel) := by
  rw [trueMass_two]
  show ENNReal.add (ENNReal.mul (ENNReal.finite (NNReal.div (NNReal.ofRat 3 (by decide +kernel))
        (NNReal.add (NNReal.ofRat 3 (by decide +kernel))
          (NNReal.add (NNReal.ofRat 3 (by decide +kernel)) NNReal.zero)))) ENNReal.one)
      (ENNReal.add (ENNReal.mul (ENNReal.finite (NNReal.div (NNReal.ofRat 3 (by decide +kernel))
        (NNReal.add (NNReal.ofRat 3 (by decide +kernel))
          (NNReal.add (NNReal.ofRat 3 (by decide +kernel)) NNReal.zero)))) ENNReal.one)
        ENNReal.zero) = _
  rw [ENNReal.add_zero, ENNReal.mul_one,
    weights_add 3 3 6 _ _ (by decide +kernel) (by decide +kernel),
    weight_ratio 3 6 (1 / 2) _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  exact (ENNReal.ofRat_add (1 / 2) (1 / 2) _ _).symm.trans (ofRat_same (by decide +kernel))

/-- The average of four rational values, in the shape of `lintegral_twoLaneLaw`. -/
private theorem quarter_mean (first second third fourth firstPair secondPair total : Rat)
    (firstNonnegative : 0 ≤ first) (secondNonnegative : 0 ≤ second) (thirdNonnegative : 0 ≤ third)
    (fourthNonnegative : 0 ≤ fourth) (firstPairNonnegative : 0 ≤ firstPair)
    (secondPairNonnegative : 0 ≤ secondPair) (totalNonnegative : 0 ≤ total)
    (firstSame : 1 / 2 * (first + second) = firstPair)
    (secondSame : 1 / 2 * (third + fourth) = secondPair)
    (totalSame : 1 / 2 * (firstPair + secondPair) = total) :
    ENNReal.mul halfMass (ENNReal.add
        (ENNReal.mul halfMass (ENNReal.add (ENNReal.ofRat first firstNonnegative)
          (ENNReal.ofRat second secondNonnegative)))
        (ENNReal.mul halfMass (ENNReal.add (ENNReal.ofRat third thirdNonnegative)
          (ENNReal.ofRat fourth fourthNonnegative)))) =
      ENNReal.ofRat total totalNonnegative := by
  rw [half_sum_ofRat first second firstPair _ _ firstPairNonnegative firstSame,
    half_sum_ofRat third fourth secondPair _ _ secondPairNonnegative secondSame,
    half_sum_ofRat firstPair secondPair total _ _ totalNonnegative totalSame]

/-- Two independent lanes with weights `1` at `false` and `3` at `true` are
multinomially resampled. The resampled law is invariant for `unevenTarget`, and
each child holds `true` with probability `5/8`, but both hold it with
probability `17/32`, not `(5/8)² = 25/64`. By hand: the four populations are
equally likely, and their masses of `true` are `0`, `3/4`, `3/4` and `1`. -/
theorem resampled_lanes_dependent :
    EmpiricalInvariant (Lanes.fin 2) unevenTarget (twoLaneLaw.bind resampledTwo) ∧
      (∀ child, twoLaneLaw.bind resampledTwo (childTrue child) =
        ENNReal.ofRat (5 / 8) (by decide +kernel)) ∧
      twoLaneLaw.bind resampledTwo bothTrue = ENNReal.ofRat (17 / 32) (by decide +kernel) ∧
      ENNReal.ofRat (17 / 32) (by decide +kernel) ≠
        ENNReal.mul (ENNReal.ofRat (5 / 8) (by decide +kernel))
          (ENNReal.ofRat (5 / 8) (by decide +kernel)) := by
  have markov : ∀ draws, Measure.IsProbability (resampledTwo draws) := fun draws => by
    rw [resampledTwo, resample_apply]
    exact (multinomial_markov (Lanes.fin 2) 2 bools draws).map _ _
  have lowLow : totalWeight (Lanes.fin 2) (twoLanes lowDraw lowDraw) ≠ NNReal.zero :=
    positive_two 1 1 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    false false (by decide +kernel) (by decide +kernel)
  have lowHigh : totalWeight (Lanes.fin 2) (twoLanes lowDraw highDraw) ≠ NNReal.zero :=
    positive_two 1 3 4 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    false true (by decide +kernel) (by decide +kernel)
  have highLow : totalWeight (Lanes.fin 2) (twoLanes highDraw lowDraw) ≠ NNReal.zero :=
    positive_two 3 1 4 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    true false (by decide +kernel) (by decide +kernel)
  have highHigh : totalWeight (Lanes.fin 2) (twoLanes highDraw highDraw) ≠ NNReal.zero :=
    positive_two 3 3 6 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    true true (by decide +kernel) (by decide +kernel)
  refine ⟨step_invariant_of_resample markov (empirical_resample
      (multinomial_offspring_unbiased (Lanes.fin 2) 2)) twoLaneLaw twoLaneLaw_invariant,
    fun child => ?_, ?_, ?_⟩
  · rw [Measure.bind_apply _ _ (childTrue_measurable child),
      lintegral_twoLaneLaw (resampledTwo.measurable (childTrue_measurable child)),
      resampledTwo_child _ lowLow, resampledTwo_child _ lowHigh, resampledTwo_child _ highLow,
      resampledTwo_child _ highHigh, trueMass_lowLow, trueMass_lowHigh, trueMass_highLow,
      trueMass_highHigh]
    exact quarter_mean 0 (3 / 4) (3 / 4) 1 (3 / 8) (7 / 8) (5 / 8) _ _ _ _
      (by decide +kernel) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · rw [Measure.bind_apply _ _ bothTrue_measurable,
      lintegral_twoLaneLaw (resampledTwo.measurable bothTrue_measurable),
      resampledTwo_both _ lowLow, resampledTwo_both _ lowHigh, resampledTwo_both _ highLow,
      resampledTwo_both _ highHigh, trueMass_lowLow, trueMass_lowHigh, trueMass_highLow,
      trueMass_highHigh,
      square_ofRat 0 0 _ (by decide +kernel) (by decide +kernel),
      square_ofRat (3 / 4) (9 / 16) _ (by decide +kernel) (by decide +kernel),
      square_ofRat 1 1 _ (by decide +kernel) (by decide +kernel)]
    exact quarter_mean 0 (9 / 16) (9 / 16) 1 (9 / 32) (25 / 32) (17 / 32) _ _ _ _
      (by decide +kernel) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · rw [square_ofRat (5 / 8) (25 / 64) _ (by decide +kernel) (by decide +kernel)]
    intro same
    have bound : ENNReal.le (ENNReal.ofRat (17 / 32) (by decide +kernel))
        (ENNReal.ofRat (25 / 64) (by decide +kernel)) := by
      rw [same]
      exact ENNReal.le_refl _
    exact absurd ((ENNReal.ofRat_le_iff _ _ _ _).mp bound) (by decide +kernel)

end

end Problib.Inference.Necessity.Resampling
