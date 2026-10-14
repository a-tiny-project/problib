module

public import Problib.Measure.Kernel.Iteration.Irreducibility
public import Problib.Measure.Kernel.Iteration.Minorization
public import Problib.Measure.AlmostEverywhere
public import Problib.Measure.Integral.Lebesgue.Infimum
public import Problib.Measure.Integral.Lebesgue.Subtract
public import Problib.Measure.Integral.Lebesgue.Zero
public import Problib.Measure.Null
public import Problib.Measure.Kernel.Iteration.Coupling
import Problib.Measure.Integral.Lebesgue.Algebra
import Problib.Measure.Integral.Lebesgue.AlmostEverywhere

set_option autoImplicit false

namespace Problib.Measure.Kernel

open Problib.Real

universe u
variable {α : Type u} {space : Space α}

@[expose] public def HarrisRecurrent (kernel : Kernel space space)
    (reference : Measure space) : Prop :=
  ∀ event, space.Measurable event → ENNReal.lt ENNReal.zero (reference event) →
    ∀ input, HitsAlmostSurely kernel event input

public structure PositiveHarris (kernel : Kernel space space)
    (law : Giry.Law space) : Prop where
  markov : ∀ input, Measure.IsProbability (kernel input)
  invariant : law.val.bind kernel = law.val
  harris : HarrisRecurrent kernel law.val

public theorem HarrisRecurrent.measureIrreducible
    {kernel : Kernel space space} {reference : Measure space}
    (markov : ∀ input, Measure.IsProbability (kernel input))
    (harris : HarrisRecurrent kernel reference)
    (nonzero : ENNReal.lt ENNReal.zero (reference Set.univ)) :
    MeasureIrreducible kernel reference := by
  refine ⟨nonzero, ?_⟩
  intro event measurable positive input
  have sure : ∀ state, hitKernel kernel event measurable state Set.univ =
      ENNReal.one := fun state =>
    (hitsAlmostSurely_iff kernel event state measurable).mp
      (harris event measurable positive state)
  have reaches : ∀ state, ∃ count,
      ENNReal.lt ENNReal.zero (iterate kernel count state event) := by
    intro state
    exact (hit_positive_iff_reaches kernel event measurable markov state).mp
      (by rw [sure state]; exact ENNReal.one_positive)
  have someIntegrated : ∃ count, ENNReal.lt ENNReal.zero
      ((kernel input).bind (iterate kernel count) event) := by
    apply Classical.byContradiction
    intro absent
    have zeroIntegral : ∀ count,
        lintegral (kernel input)
          (fun state => iterate kernel count state event) = ENNReal.zero := by
      intro count
      rw [← Measure.bind_apply (kernel input) (iterate kernel count) measurable]
      exact Classical.byContradiction (fun nonzero =>
        absent ⟨count, ENNReal.zero_lt_iff_ne_zero.mpr nonzero⟩)
    have zeroAE : ∀ count, (kernel input).AE (fun state =>
        iterate kernel count state event = ENNReal.zero) := by
      intro count
      exact (lintegral_eq_zero_iff
        ((iterate kernel count).measurable measurable)).mp
          (zeroIntegral count)
    have impossible : (kernel input).AE (fun _ => False) :=
      (Measure.ae_all_iff.mpr zeroAE).mono (fun state all => by
        rcases reaches state with ⟨count, reached⟩
        exact (ENNReal.zero_lt_iff_ne_zero.mp reached) (all count))
    have emptyMass : kernel input Set.univ = ENNReal.zero := by
      have same : Set.complement (fun _ : α => False) = Set.univ := by
        funext state
        apply propext
        constructor
        · intro _
          trivial
        · intro _ absent
          exact absent.elim
      exact same ▸ impossible
    rw [(markov input).univ_eq_one] at emptyMass
    exact ENNReal.one_ne_zero emptyMass
  rcases someIntegrated with ⟨count, reached⟩
  refine ⟨count, ?_⟩
  rw [iterate_succ, Kernel.comp_apply]
  exact reached

/-! ### Harris recurrence from a uniform minorization -/

/-- Survival for `first + second` steps averages the survival for `second`
steps over the surviving law after `first`. -/
private theorem survival_add (kernel : Kernel space space) {region : Set α}
    (measurable : space.Measurable region) (first second : Nat) (input : α) :
    survival kernel region measurable (first + second) input =
      lintegral (iterate (continueOutside kernel region measurable) first input)
        (survival kernel region measurable second) := by
  unfold survival
  rw [iterate_add, comp_apply_measurable _ _ _ space.univ]

/-- Surviving `count + 1` steps outside the region is at most the chance of
being outside it at time `count`. -/
private theorem survival_succ_le (kernel : Kernel space space) {region : Set α}
    (measurable : space.Measurable region)
    (markov : ∀ input, Measure.IsProbability (kernel input)) (count : Nat)
    (input : α) :
    ENNReal.le (survival kernel region measurable (count + 1) input)
      (ENNReal.sub ENNReal.one (iterate kernel count input region)) := by
  have outside : ∀ state, ENNReal.le
      (continueOutside kernel region measurable state Set.univ)
      (ennrealIndicator (Set.complement region) (fun _ => ENNReal.one) state) := by
    intro state
    by_cases member : region state
    · rw [continueOutside, piecewise_apply_of_mem _ _ _ _ _ member,
        Kernel.zero_apply, Measure.zero_apply]
      exact ENNReal.zero_le _
    · rw [continueOutside, piecewise_apply_of_not_mem _ _ _ _ _ member,
        (markov state).univ_eq_one,
        ennrealIndicator_of_mem (region := Set.complement region) (point := state) member]
      exact ENNReal.le_refl _
  have complementMeasurable := space.complement measurable
  have split := survival_add kernel measurable count 1 input
  have single : survival kernel region measurable 1 =
      fun state => continueOutside kernel region measurable state Set.univ := by
    funext state
    unfold survival
    rw [iterate_one]
  rw [single] at split
  rw [split]
  refine ENNReal.le_trans (lintegral_mono _ outside) ?_
  rw [← apply_eq_lintegral_indicator _ complementMeasurable,
    ← Measure.IsProbability.apply_complement (iterate_isProbability kernel markov count input)
      measurable]
  exact continueOutside_iterate_le kernel region measurable count input _
    complementMeasurable

/-- If every start enters the region at time `count` with chance at least
`floor`, survival over `blocks` blocks of `count + 1` steps is at most
`(1 - floor)` to the power `blocks`. -/
private theorem survival_blocks_le (kernel : Kernel space space) {region : Set α}
    (measurable : space.Measurable region)
    (markov : ∀ input, Measure.IsProbability (kernel input)) {count : Nat}
    {floor : ENNReal} (lower : ∀ input, ENNReal.le floor (iterate kernel count input region))
    (blocks : Nat) (input : α) :
    ENNReal.le (survival kernel region measurable (blocks * (count + 1)) input)
      (ENNReal.pow (ENNReal.sub ENNReal.one floor) blocks) := by
  induction blocks generalizing input with
  | zero =>
    rw [Nat.zero_mul, ENNReal.pow_zero]
    unfold survival
    rw [iterate_zero, Kernel.deterministic_apply, Measure.dirac_apply_univ]
    exact ENNReal.le_refl _
  | succ blocks induction =>
    rw [Nat.succ_mul blocks (count + 1), Nat.add_comm (blocks * (count + 1)) (count + 1),
      survival_add kernel measurable (count + 1)]
    have averaged := lintegral_mono
      (iterate (continueOutside kernel region measurable) (count + 1) input) induction
    rw [lintegral_const] at averaged
    refine ENNReal.le_trans averaged ?_
    have once : ENNReal.le
        (iterate (continueOutside kernel region measurable) (count + 1) input Set.univ)
        (ENNReal.sub ENNReal.one floor) :=
      ENNReal.le_trans (survival_succ_le kernel measurable markov count input)
        (ENNReal.sub_le_sub_left (lower input) ENNReal.one)
    rw [ENNReal.pow_succ, ENNReal.mul_comm (ENNReal.sub ENNReal.one floor)]
    exact ENNReal.mul_le_mul_left once _

/-- A positive floor at most one leaves a base below one. -/
private theorem sub_floor_lt_one {floor : ENNReal}
    (positive : ENNReal.lt ENNReal.zero floor) (atMostOne : ENNReal.le floor ENNReal.one) :
    ENNReal.lt (ENNReal.sub ENNReal.one floor) ENNReal.one := by
  rcases ENNReal.exists_finite_of_finite (ENNReal.finite_of_le atMostOne True.intro) with
    ⟨value, rfl⟩
  have valuePositive : NNReal.lt NNReal.zero value := positive
  have strict : NNReal.lt (NNReal.sub NNReal.one value)
      (NNReal.add (NNReal.sub NNReal.one value) value) := by
    have shifted :=
      (NNReal.add_lt_add_left_iff (shift := NNReal.sub NNReal.one value)).mpr
        valuePositive
    simpa only [NNReal.add_zero] using shifted
  rw [NNReal.sub_add_cancel atMostOne] at strict
  exact strict

/-- A uniform minorization makes every chain Harris recurrent for each of its
invariant laws: after enough steps every start charges each positive event,
so survival outside it decays geometrically over blocks. -/
public theorem harrisRecurrent_of_minorization
    {kernel : Kernel space space} {steps : Nat} {weight : NNReal}
    {reference : Giry.Law space}
    (minor : Minorization kernel steps weight reference)
    (law : Giry.Law space) (invariant : law.val.bind kernel = law.val) :
    HarrisRecurrent kernel law.val := by
  intro event measurable positive input
  rcases ENNReal.pow_eventually_lt (minorization_decay_base_lt_one minor) positive with
    ⟨stage, small⟩
  let decay := ENNReal.pow (ENNReal.sub ENNReal.one (ENNReal.finite weight)) stage
  have decayLess : ENNReal.lt decay (law.val event) := small stage (Nat.le_refl stage)
  let count := steps * stage
  let floor := ENNReal.sub (law.val event) decay
  have lower : ∀ state, ENNReal.le floor (iterate kernel count state event) := by
    intro state
    let start : Giry.Law space :=
      ⟨Measure.dirac space state, Measure.IsProbability.dirac space state⟩
    have contraction := minorization_contraction minor law start invariant count
    have divided : count / steps = stage := Nat.mul_div_cancel_left stage minor.stepsPositive
    rw [divided] at contraction
    have atMost : ENNReal.le
        (Giry.Law.totalVariation
          ⟨iterate kernel count state, iterate_isProbability kernel minor.markov count state⟩
          law) decay := by
      have bounded := ENNReal.le_trans contraction
        (ENNReal.mul_le_mul_left (Giry.Law.totalVariation_le_one start law) decay)
      rw [ENNReal.mul_one] at bounded
      have same : (⟨start.val.bind (iterate kernel count),
          start.property.bind (iterate kernel count)
            (iterate_isProbability kernel minor.markov count)⟩ : Giry.Law space) =
          ⟨iterate kernel count state,
            iterate_isProbability kernel minor.markov count state⟩ :=
        Subtype.ext (Measure.dirac_bind state (iterate kernel count))
      rw [same] at bounded
      exact bounded
    have gap := ENNReal.le_trans
      (Giry.Law.event_sub_le law ⟨iterate kernel count state,
        iterate_isProbability kernel minor.markov count state⟩ measurable)
      (by rw [Giry.Law.totalVariation_symm]; exact atMost)
    rw [ENNReal.sub_le_iff_le_add] at gap
    rw [ENNReal.sub_le_iff_le_add, ENNReal.add_comm]
    exact gap
  have floorPositive : ENNReal.lt ENNReal.zero floor := by
    rw [ENNReal.lt_sub_iff_add_lt, ENNReal.zero_add]
    exact decayLess
  have floorAtMostOne : ENNReal.le floor ENNReal.one :=
    ENNReal.le_trans (ENNReal.sub_le_self _ _) (law.property.apply_le_one event)
  refine ⟨measurable, ?_⟩
  rw [hit_mass_eq_one_iff_survival_vanishes kernel event measurable minor.markov input]
  apply ENNReal.eq_zero_of_le_zero
  rw [← ENNReal.iInf_pow_eq_zero (sub_floor_lt_one floorPositive floorAtMostOne)]
  exact ENNReal.le_iInf (fun blocks => ENNReal.le_trans
    (ENNReal.iInf_le _ (blocks * (count + 1)))
    (survival_blocks_le kernel measurable minor.markov lower blocks input))

private noncomputable def neverHitMass (kernel : Kernel space space)
    (event : Set α) (measurable : space.Measurable event) (input : α) : ENNReal :=
  ENNReal.iInf (fun count => survival kernel event measurable count input)

private theorem neverHitMass_measurable (kernel : Kernel space space)
    (event : Set α) (measurable : space.Measurable event) :
    ENNRealMeasurable space (neverHitMass kernel event measurable) := by
  exact ENNRealMeasurable.iInf (fun count =>
    (iterate (continueOutside kernel event measurable) count).measurable space.univ)

private theorem neverHitMass_le_one
    (kernel : Kernel space space) (event : Set α)
    (measurable : space.Measurable event)
    (_markov : ∀ input, Measure.IsProbability (kernel input)) (input : α) :
    ENNReal.le (neverHitMass kernel event measurable input) ENNReal.one := by
  have initial := ENNReal.iInf_le
    (fun count => survival kernel event measurable count input) 0
  rw [survival, iterate_zero, Kernel.deterministic_apply,
    Measure.dirac_apply_univ] at initial
  exact initial

private theorem neverHitMass_zero_on_event
    (kernel : Kernel space space) (event : Set α)
    (measurable : space.Measurable event) (input : α) (member : event input) :
    neverHitMass kernel event measurable input = ENNReal.zero := by
  have first := ENNReal.iInf_le
    (fun count => survival kernel event measurable count input) 1
  have stop : continueOutside kernel event measurable input =
      Measure.zero space := by
    rw [continueOutside, piecewise_apply_of_mem _ _ _ _ _ member,
      Kernel.zero_apply]
  rw [survival, iterate_succ, Kernel.comp_apply, stop,
    Measure.zero_bind, Measure.zero_apply] at first
  exact ENNReal.eq_zero_of_le_zero first

private theorem neverHitMass_subharmonic
    (kernel : Kernel space space) (event : Set α)
    (measurable : space.Measurable event)
    (markov : ∀ input, Measure.IsProbability (kernel input)) (input : α) :
    ENNReal.le (neverHitMass kernel event measurable input)
      (lintegral (kernel input) (neverHitMass kernel event measurable)) := by
  let T := continueOutside kernel event measurable
  have Tbound : ∀ state, ENNReal.le (T state Set.univ) ENNReal.one := by
    intro state
    have balance := hitting_conservative kernel event measurable markov state
    have bound := ENNReal.add_le_add_left
      (ENNReal.zero_le (exitInside event measurable state Set.univ))
      (T state Set.univ)
    rw [ENNReal.add_zero, balance] at bound
    exact bound
  have step : ∀ count state,
      ENNReal.le (survival kernel event measurable (count+1) state)
        (survival kernel event measurable count state) := by
    intro count state
    exact iterate_mass_antitone T Tbound (Nat.le_succ count) state
  have finiteTerm : ∃ count,
      ENNReal.Finite (lintegral (T input)
        (survival kernel event measurable count)) := by
    refine ⟨0, ?_⟩
    have initial : ∀ state, survival kernel event measurable 0 state =
        ENNReal.one := by
      intro state
      rw [survival, iterate_zero, Kernel.deterministic_apply,
        Measure.dirac_apply_univ]
    rw [lintegral_congr (T input) initial, lintegral_const,
      ENNReal.one_mul]
    exact ENNReal.finite_of_le (Tbound input) True.intro
  have limit := lintegral_iInf (T input)
    (fun count state => survival kernel event measurable count state)
    (fun count => (iterate T count).measurable space.univ)
    step finiteTerm
  have antitone : ∀ {first second}, first ≤ second →
      ENNReal.le (survival kernel event measurable second input)
        (survival kernel event measurable first input) := by
    intro first second included
    exact iterate_mass_antitone T Tbound included input
  have fixed : neverHitMass kernel event measurable input =
      lintegral (T input) (neverHitMass kernel event measurable) := by
    calc
      neverHitMass kernel event measurable input =
          ENNReal.iInf (fun count =>
            survival kernel event measurable (count + 1) input) := by
        rw [neverHitMass]
        have shifted := ENNReal.iInf_tail
          (fun count => survival kernel event measurable count input)
          antitone 1
        simpa only [Nat.add_comm 1] using shifted.symm
      _ = ENNReal.iInf (fun count => lintegral (T input)
          (survival kernel event measurable count)) := by
        apply congrArg ENNReal.iInf
        funext count
        exact survival_succ kernel event measurable count input
      _ = lintegral (T input) (neverHitMass kernel event measurable) :=
        limit.symm
  by_cases member : event input
  · rw [neverHitMass_zero_on_event kernel event measurable input member]
    exact ENNReal.zero_le _
  · rw [fixed]
    change ENNReal.le
      (lintegral ((continueOutside kernel event measurable) input)
        (neverHitMass kernel event measurable))
      (lintegral (kernel input) (neverHitMass kernel event measurable))
    rw [continueOutside,
      piecewise_apply_of_not_mem _ _ _ _ _ member]
    exact ENNReal.le_refl _

private theorem neverHitMass_harmonic_ae
    (kernel : Kernel space space) (reference : Measure space)
    (event : Set α) (measurable : space.Measurable event)
    (markov : ∀ input, Measure.IsProbability (kernel input))
    (finite : Measure.IsFinite reference)
    (invariant : reference.bind kernel = reference) :
    reference.AE (fun input =>
      neverHitMass kernel event measurable input =
        lintegral (kernel input) (neverHitMass kernel event measurable)) := by
  let g := neverHitMass kernel event measurable
  have gMeasurable := neverHitMass_measurable kernel event measurable
  have gBound := neverHitMass_le_one kernel event measurable markov
  have subharmonic := neverHitMass_subharmonic kernel event measurable markov
  have integralEqual :
      lintegral reference (fun input => lintegral (kernel input) g) =
        lintegral reference g := by
    rw [← Measure.lintegral_bind reference kernel gMeasurable, invariant]
  have finiteG : ENNReal.Finite (lintegral reference g) := by
    have bound := lintegral_mono reference gBound
    rw [lintegral_const, ENNReal.one_mul] at bound
    exact ENNReal.finite_of_le bound finite.univ_finite
  have zeroDifference : lintegral reference (fun input =>
      ENNReal.sub (lintegral (kernel input) g) (g input)) =
        ENNReal.zero := by
    rw [lintegral_sub reference
      (kernel.lintegral_measurable gMeasurable) gMeasurable finiteG
      subharmonic, integralEqual, ENNReal.sub_self]
  have differenceAE := (lintegral_eq_zero_iff
    (ENNRealMeasurable.sub (kernel.lintegral_measurable gMeasurable)
      gMeasurable)).mp zeroDifference
  exact differenceAE.mono (fun input zero =>
    ENNReal.le_antisymm (subharmonic input)
      (ENNReal.sub_eq_zero_iff_le.mp zero))

/-- Finite invariant mass and a.e. reachability imply a.e. certain hitting. -/
public theorem invariant_hits_of_reaches
    {kernel : Kernel space space} {reference : Measure space} {event : Set α}
    (markov : ∀ input, Measure.IsProbability (kernel input))
    (finite : Measure.IsFinite reference)
    (invariant : reference.bind kernel = reference)
    (measurable : space.Measurable event)
    (reach : reference.AE (fun input =>
      ∃ count, ENNReal.lt ENNReal.zero (iterate kernel count input event))) :
    reference.AE (HitsAlmostSurely kernel event) := by
  let g := neverHitMass kernel event measurable
  have gMeasurable := neverHitMass_measurable kernel event measurable
  have harmonic := neverHitMass_harmonic_ae kernel reference event measurable
    markov finite invariant
  have bounded := neverHitMass_le_one kernel event measurable markov
  -- ENNReal level-set step, expanded rather than hidden behind TV:
  have closedLevel : ∀ threshold : ENNReal,
      ENNReal.lt ENNReal.zero threshold → ENNReal.le threshold ENNReal.one →
      reference.AE (fun input =>
        ENNReal.le threshold (g input) →
          kernel input (fun state => ENNReal.lt (g state) threshold) =
            ENNReal.zero) := by
    intro threshold positive belowOne
    let truncated : α → ENNReal := fun input => ENNReal.min (g input) threshold
    have truncatedMeasurable : ENNRealMeasurable space truncated :=
      ENNRealMeasurable.min gMeasurable
        (ENNRealMeasurable.constant space threshold)
    have Jensen : ∀ input,
        ENNReal.le (lintegral (kernel input) truncated)
          (ENNReal.min (lintegral (kernel input) g) threshold) := by
      intro input
      have byG := lintegral_mono (kernel input)
        (fun state => ENNReal.min_le_left (g state) threshold)
      have byT := lintegral_mono (kernel input)
        (fun state => ENNReal.min_le_right (g state) threshold)
      rw [lintegral_const, (markov input).univ_eq_one,
        ENNReal.mul_one] at byT
      exact ENNReal.le_min byG byT
    have truncationEqualAE : reference.AE (fun input =>
        lintegral (kernel input) truncated =
          ENNReal.min (lintegral (kernel input) g) threshold) := by
      let after : α → ENNReal := fun input =>
        lintegral (kernel input) truncated
      let before : α → ENNReal := fun input =>
        ENNReal.min (lintegral (kernel input) g) threshold
      have afterMeasurable : ENNRealMeasurable space after :=
        kernel.lintegral_measurable truncatedMeasurable
      have beforeMeasurable : ENNRealMeasurable space before :=
        ENNRealMeasurable.min (kernel.lintegral_measurable gMeasurable)
          (ENNRealMeasurable.constant space threshold)
      have afterIntegral : lintegral reference after =
          lintegral reference truncated := by
        rw [← Measure.lintegral_bind reference kernel truncatedMeasurable,
          invariant]
      have beforeIntegral : lintegral reference before =
          lintegral reference truncated := by
        have same := lintegral_congr_ae (harmonic.mono
          (fun input equal => congrArg
            (fun value => ENNReal.min value threshold) equal.symm))
        exact same
      have afterFinite : ENNReal.Finite (lintegral reference after) := by
        have bound := lintegral_mono reference (fun input => by
          exact ENNReal.le_trans (Jensen input)
            (ENNReal.min_le_right _ _))
        rw [lintegral_const] at bound
        exact ENNReal.finite_of_le bound
          (ENNReal.mul_finite (by
            exact ENNReal.finite_of_le belowOne True.intro)
            finite.univ_finite)
      have vanished : lintegral reference (fun input =>
          ENNReal.sub (before input) (after input)) = ENNReal.zero := by
        rw [lintegral_sub reference beforeMeasurable afterMeasurable
          afterFinite Jensen, beforeIntegral, afterIntegral,
          ENNReal.sub_self]
      have equalAE := (lintegral_eq_zero_iff
        (ENNRealMeasurable.sub beforeMeasurable afterMeasurable)).mp vanished
      exact equalAE.mono (fun input zero =>
        ENNReal.le_antisymm (Jensen input)
          (ENNReal.sub_eq_zero_iff_le.mp zero))
    have absorbingAE := truncationEqualAE.and harmonic
    exact absorbingAE.mono (fun input ⟨truncatedEqual, harmonicAt⟩
      thresholdBelow => by
      have integrated : lintegral (kernel input) truncated = threshold := by
        rw [truncatedEqual, ← harmonicAt,
          ENNReal.min_eq_right thresholdBelow]
      have integralFinite : ENNReal.Finite
          (lintegral (kernel input) truncated) := by
        rw [integrated]
        exact ENNReal.finite_of_le belowOne True.intro
      have differenceZero : lintegral (kernel input) (fun state =>
          ENNReal.sub threshold (truncated state)) = ENNReal.zero := by
        rw [lintegral_sub (kernel input)
          (ENNRealMeasurable.constant space threshold) truncatedMeasurable
          integralFinite (fun state => ENNReal.min_le_right _ _),
          lintegral_const, (markov input).univ_eq_one,
          ENNReal.mul_one, integrated, ENNReal.sub_self]
      have noLow := (lintegral_eq_zero_iff
        (ENNRealMeasurable.sub
          (ENNRealMeasurable.constant space threshold)
          truncatedMeasurable)).mp differenceZero
      have outside : (kernel input).AE (fun state =>
          ¬ENNReal.lt (g state) threshold) :=
        noLow.mono (fun state vanished low => by
        have thresholdLeTruncated : ENNReal.le threshold
            (truncated state) := ENNReal.sub_eq_zero_iff_le.mp vanished
        have thresholdLeG := ENNReal.le_trans thresholdLeTruncated
          (ENNReal.min_le_left _ _)
        exact low.2 thresholdLeG)
      apply (show (kernel input).NullSet
        (Set.complement (fun state =>
          ¬ENNReal.lt (g state) threshold)) from outside).mono
      intro state low excluded
      exact excluded low)
  have levelNull : ∀ threshold : ENNReal,
      ENNReal.lt ENNReal.zero threshold → ENNReal.le threshold ENNReal.one →
      reference.NullSet (fun input => ENNReal.le threshold (g input)) := by
    intro threshold positive belowOne
    rcases (closedLevel threshold positive belowOne).exists_null_exception with
      ⟨bad, badMeasurable, badNull, good⟩
    let low : Set α := fun state => ENNReal.lt (g state) threshold
    have lowMeasurable : space.Measurable low := gMeasurable.iio threshold
    have eventLow : Set.Subset event low := by
      intro state member
      change ENNReal.lt
        (neverHitMass kernel event measurable state) threshold
      rw [neverHitMass_zero_on_event kernel event measurable state member]
      exact positive
    have invariantN : ∀ count,
        reference.bind (iterate kernel count) = reference := by
      intro count
      induction count with
      | zero =>
          rw [iterate_zero, Measure.bind_deterministic, Measure.map_id]
      | succ count induction =>
          rw [iterate_succ_right, ← Measure.bind_assoc, induction,
            invariant]
    have nullBadAE : ∀ count, reference.AE (fun input =>
        iterate kernel count input bad = ENNReal.zero) := by
      intro count
      have integralZero : lintegral reference (fun input =>
          iterate kernel count input bad) = ENNReal.zero := by
        rw [← Measure.bind_apply reference (iterate kernel count)
          badMeasurable, invariantN count]
        exact badNull
      exact (lintegral_eq_zero_iff
        ((iterate kernel count).measurable badMeasurable)).mp integralZero
    have allBadAE := (Measure.ae_all_iff.mpr nullBadAE)
    have outsideBadAE : reference.AE (fun input => ¬bad input) := by
      apply badNull.mono
      intro input doubleNeg
      exact Classical.not_not.mp doubleNeg
    have available := (allBadAE.and outsideBadAE).and reach
    have noLevel : reference.AE (fun input =>
        ¬ENNReal.le threshold (g input)) :=
      available.mono (fun input
        ⟨⟨allBad, outsideBad⟩, reached⟩ level => by
      have lowNull : ∀ count,
          iterate kernel count input low = ENNReal.zero := by
        intro count
        induction count with
        | zero =>
            rw [iterate_zero, Kernel.deterministic_apply]
            apply Measure.dirac_apply_of_not_mem space input lowMeasurable
            intro inLow
            exact inLow.2 level
        | succ count induction =>
            rw [iterate_succ_right,
              comp_apply_measurable _ _ _ lowMeasurable]
            apply lintegral_eq_zero_of_ae_zero
            have absent : (iterate kernel count input).AE (fun state =>
                kernel state low = ENNReal.zero) := by
              have nullUnion := (show
                  (iterate kernel count input).NullSet low from induction).union
                    (show (iterate kernel count input).NullSet bad from
                      allBad count)
              apply nullUnion.mono
              intro state failure
              by_cases inLow : low state
              · exact Or.inl inLow
              · by_cases inBad : bad state
                · exact Or.inr inBad
                · have above : ENNReal.le threshold (g state) := by
                    rcases ENNReal.le_total threshold (g state) with
                      included | reverse
                    · exact included
                    · apply Classical.byContradiction
                      intro notAbove
                      exact inLow ⟨reverse, notAbove⟩
                  exact False.elim (failure (good state inBad above))
            exact absent
      rcases reached with ⟨count, reachedAt⟩
      have bound := (iterate kernel count input).mono eventLow
      rw [lowNull count] at bound
      exact (ENNReal.zero_lt_iff_ne_zero.mp reachedAt)
        (ENNReal.eq_zero_of_le_zero bound))
    apply (show reference.NullSet
      (Set.complement (fun input => ¬ENNReal.le threshold (g input)))
      from noLevel).mono
    intro input level excluded
    exact excluded level
  have gZeroAE : reference.AE (fun input => g input = ENNReal.zero) := by
    let levels : Nat → Set α := fun index input =>
      ENNReal.lt ENNReal.zero (ENNReal.rationalBasis index) ∧
        ENNReal.le (ENNReal.rationalBasis index) (g input)
    have nullLevels : ∀ index, reference.NullSet (levels index) := by
      intro index
      by_cases positive : ENNReal.lt ENNReal.zero (ENNReal.rationalBasis index)
      · by_cases inhabited : ∃ input, levels index input
        · rcases inhabited with ⟨input, _, included⟩
          have belowOne : ENNReal.le (ENNReal.rationalBasis index)
              ENNReal.one := ENNReal.le_trans included (bounded input)
          exact (levelNull _ positive belowOne).mono
            (fun {_} member => member.2)
        · apply reference.null_empty.mono
          intro input member
          exact inhabited ⟨input, member⟩
      · apply reference.null_empty.mono
        intro input member
        exact positive member.1
    apply (Measure.NullSet.iUnion nullLevels).mono
    intro input nonzero
    rcases ENNReal.exists_rationalBasis_between
      (ENNReal.zero_lt_iff_ne_zero.mpr nonzero) with
      ⟨index, positive, below⟩
    exact ⟨index, positive, below.1⟩
  exact gZeroAE.mono (fun input zero => by
    apply (hitsAlmostSurely_iff kernel event input measurable).mpr
    exact (hit_mass_eq_one_iff_survival_vanishes kernel event measurable
      markov input).mpr zero)

public theorem invariant_hits_almost_everywhere
    {kernel : Kernel space space} {reference : Measure space} {event : Set α}
    (markov : ∀ input, Measure.IsProbability (kernel input))
    (finite : Measure.IsFinite reference)
    (invariant : reference.bind kernel = reference)
    (irreducible : MeasureIrreducible kernel reference)
    (measurable : space.Measurable event)
    (positive : ENNReal.lt ENNReal.zero (reference event)) :
    reference.AE (HitsAlmostSurely kernel event) := by
  apply invariant_hits_of_reaches markov finite invariant measurable
  exact reference.ae_of_forall (fun input => by
    rcases irreducible.reaches event measurable positive input with
      ⟨count, reached⟩
    exact ⟨count + 1, reached⟩)

section Coupling

variable {kernel : Kernel space space} {region : Set α}
  {weight : NNReal} {reference : Giry.Law space}

/-- Once the chain charges a one-step small set that its minorant charges, it
charges the set at every later time. -/
public theorem reach_persistent
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region)
    (selfCharge : ENNReal.lt ENNReal.zero (reference.val region))
    {count : Nat} {input : α}
    (positive : ENNReal.lt ENNReal.zero (iterate kernel count input region)) :
    ∀ later, count ≤ later →
      ENNReal.lt ENNReal.zero (iterate kernel later input region) := by
  classical
  let charge := ENNReal.mul (ENNReal.finite weight) (reference.val region)
  have chargeNonzero : charge ≠ ENNReal.zero := by
    intro zero
    rcases ENNReal.mul_eq_zero_iff.mp zero with weightZero | referenceZero
    · exact (ENNReal.zero_lt_iff_ne_zero.mp
        (show ENNReal.lt ENNReal.zero (ENNReal.finite weight) from
          minor.weightPositive)) weightZero
    · exact (ENNReal.zero_lt_iff_ne_zero.mp selfCharge) referenceZero
  have step : ∀ now, ENNReal.lt ENNReal.zero (iterate kernel now input region) →
      ENNReal.lt ENNReal.zero (iterate kernel (now + 1) input region) := by
    intro now nowPositive
    have lower : ENNReal.le (ENNReal.mul charge (iterate kernel now input region))
        (iterate kernel (now + 1) input region) := by
      rw [iterate_succ_right, comp_apply_measurable _ _ _ measurable]
      have pointwise : ∀ state, ENNReal.le
          (ennrealIndicator region (fun _ => charge) state) (kernel state region) := by
        intro state
        unfold ennrealIndicator ennrealPiecewise
        by_cases member : region state
        · rw [ite_eq_left member]
          have bound := minor.lower state member region measurable
          rw [Measure.smul_apply_measurable _ _ measurable, iterate_one] at bound
          exact bound
        · rw [ite_eq_right member]
          exact ENNReal.zero_le _
      have integral := lintegral_mono (iterate kernel now input) pointwise
      rw [lintegral_indicator _ _ measurable, lintegral_const,
        Measure.restrict_apply_univ] at integral
      exact integral
    apply ENNReal.zero_lt_iff_ne_zero.mpr
    intro zero
    rw [zero] at lower
    rcases ENNReal.mul_eq_zero_iff.mp (ENNReal.eq_zero_of_le_zero lower) with
      chargeZero | nowZero
    · exact chargeNonzero chargeZero
    · exact (ENNReal.zero_lt_iff_ne_zero.mp nowPositive) nowZero
  intro later included
  induction later with
  | zero =>
      have start := Nat.le_zero.mp included
      subst start
      exact positive
  | succ later induction =>
      rcases Nat.lt_or_eq_of_le included with before | equal
      · exact step later (induction (Nat.le_of_lt_succ before))
      · rw [← equal]
        exact positive

/-- Almost every pair of invariant starts charges `region × region` at one
common time. -/
public theorem pair_reaches_region_ae
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region)
    (selfCharge : ENNReal.lt ENNReal.zero (reference.val region))
    (law : Giry.Law space)
    (reach : law.val.AE (fun input =>
      ∃ count, ENNReal.lt ENNReal.zero (iterate kernel count input region))) :
    (Measure.prod law.val law.val
        (Measure.SFinite.ofFinite law.property.to_finite)).AE (fun pair =>
      ∃ count, ENNReal.lt ENNReal.zero
        (iterate (parallel kernel kernel (fun input => (minor.markov input).to_finite)
          (fun input => (minor.markov input).to_finite)) count pair
          (Set.product region region))) := by
  apply (Measure.AE.prod law.property.to_finite reach reach).mono
  rintro pair ⟨⟨leftCount, leftPositive⟩, ⟨rightCount, rightPositive⟩⟩
  refine ⟨max leftCount rightCount, ?_⟩
  have finiteIterates : ∀ count input,
      Measure.IsFinite (iterate kernel count input) :=
    fun count input => (iterate_isProbability kernel minor.markov count input).to_finite
  rw [iterate_parallel _ _ finiteIterates finiteIterates,
    parallel_apply_product _ _ _ _ pair measurable measurable]
  have leftLater := reach_persistent minor measurable selfCharge leftPositive
    (max leftCount rightCount) (Nat.le_max_left _ _)
  have rightLater := reach_persistent minor measurable selfCharge rightPositive
    (max leftCount rightCount) (Nat.le_max_right _ _)
  apply ENNReal.zero_lt_iff_ne_zero.mpr
  intro zero
  rcases ENNReal.mul_eq_zero_iff.mp zero with leftZero | rightZero
  · exact (ENNReal.zero_lt_iff_ne_zero.mp leftLater) leftZero
  · exact (ENNReal.zero_lt_iff_ne_zero.mp rightLater) rightZero

/-- Almost every pair of invariant starts hits `region × region` with
probability one. -/
public theorem pair_hits_region_ae
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region)
    (selfCharge : ENNReal.lt ENNReal.zero (reference.val region))
    (law : Giry.Law space) (invariant : law.val.bind kernel = law.val)
    (reach : law.val.AE (fun input =>
      ∃ count, ENNReal.lt ENNReal.zero (iterate kernel count input region))) :
    (Measure.prod law.val law.val
        (Measure.SFinite.ofFinite law.property.to_finite)).AE
      (HitsAlmostSurely (parallel kernel kernel
        (fun input => (minor.markov input).to_finite)
        (fun input => (minor.markov input).to_finite)) (Set.product region region)) :=
  invariant_hits_of_reaches (parallel_isProbability minor.markov minor.markov)
    (Measure.IsFinite.prod law.property.to_finite law.property.to_finite)
    (parallel_invariant _ _ _ _ law.property.to_finite law.property.to_finite
      invariant invariant)
    (Space.product_set_measurable space space measurable measurable)
    (pair_reaches_region_ae minor measurable selfCharge law reach)

/-- A measure invariant under a kernel is invariant under every iterate. -/
public theorem bind_iterate_of_invariant {measure : Measure space}
    (invariant : measure.bind kernel = measure) (count : Nat) :
    measure.bind (iterate kernel count) = measure := by
  induction count with
  | zero => rw [iterate_zero, Measure.bind_deterministic, Measure.map_id]
  | succ count induction =>
      rw [iterate_succ_right, ← Measure.bind_assoc, induction, invariant]

/-- The pairs from which the independent pair chain surely hits the region
product. -/
private def pairMiss
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) : Set (α × α) :=
  Set.complement (fun pair =>
    hitKernel (parallel kernel kernel (fun input => (minor.markov input).to_finite)
        (fun input => (minor.markov input).to_finite)) (Set.product region region)
      (Space.product_set_measurable space space measurable measurable)
      pair Set.univ = ENNReal.one)

/-- The pairs from which the pair chain never charges a pair that might miss
the region product. -/
private def pairGood
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) : Set (α × α) :=
  Set.iInter (fun count pair =>
    iterate (parallel kernel kernel (fun input => (minor.markov input).to_finite)
      (fun input => (minor.markov input).to_finite)) count pair
      (pairMiss minor measurable) = ENNReal.zero)

private theorem pairMiss_measurable
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) :
    (Space.product space space).Measurable (pairMiss minor measurable) :=
  (Space.product space space).complement
    (ENNRealMeasurable.singleton
      ((hitKernel (parallel kernel kernel
          (fun input => (minor.markov input).to_finite)
          (fun input => (minor.markov input).to_finite)) (Set.product region region)
        (Space.product_set_measurable space space measurable measurable)).measurable
        (Space.product space space).univ) ENNReal.one)

private theorem pairGood_measurable
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) :
    (Space.product space space).Measurable (pairGood minor measurable) :=
  (Space.product space space).iInter (fun count =>
    ENNRealMeasurable.singleton
      ((iterate (parallel kernel kernel (fun input => (minor.markov input).to_finite)
        (fun input => (minor.markov input).to_finite)) count).measurable
        (pairMiss_measurable minor measurable)) ENNReal.zero)

private theorem pairGood_hits
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) {pair : α × α}
    (good : pairGood minor measurable pair) :
    hitKernel (parallel kernel kernel (fun input => (minor.markov input).to_finite)
        (fun input => (minor.markov input).to_finite)) (Set.product region region)
      (Space.product_set_measurable space space measurable measurable)
      pair Set.univ = ENNReal.one := by
  classical
  have start := good 0
  dsimp only at start
  rw [iterate_zero, Kernel.deterministic_apply,
    Measure.dirac_apply _ _ (pairMiss_measurable minor measurable)] at start
  by_cases missing : pairMiss minor measurable pair
  · rw [ite_eq_left missing] at start
    exact absurd start ENNReal.one_ne_zero
  · exact Classical.byContradiction missing

/-- From a good pair, the pair chain charges no pair outside the good set. -/
private theorem pairGood_step
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) {pair : α × α}
    (good : pairGood minor measurable pair) :
    parallel kernel kernel (fun input => (minor.markov input).to_finite)
      (fun input => (minor.markov input).to_finite) pair
      (Set.complement (pairGood minor measurable)) = ENNReal.zero := by
  classical
  let pairKernel := parallel kernel kernel
    (fun input => (minor.markov input).to_finite)
    (fun input => (minor.markov input).to_finite)
  have missMeasurable := pairMiss_measurable minor measurable
  have eachNull : ∀ count, (pairKernel pair).NullSet (Set.complement (fun state =>
      iterate pairKernel count state (pairMiss minor measurable) = ENNReal.zero)) := by
    intro count
    have next := good (count + 1)
    dsimp only at next
    rw [iterate_succ, comp_apply_measurable _ _ _ missMeasurable] at next
    exact (lintegral_eq_zero_iff
      ((iterate pairKernel count).measurable missMeasurable)).mp next
  apply ENNReal.eq_zero_of_le_zero
  have bound := (Measure.NullSet.iUnion eachNull).mono (left := Set.complement
    (pairGood minor measurable)) (by
      intro state outside
      apply Classical.byContradiction
      intro never
      apply outside
      intro count
      apply Classical.byContradiction
      intro charged
      exact never ⟨count, charged⟩)
  rw [show (pairKernel pair) (Set.complement (pairGood minor measurable)) =
    ENNReal.zero from bound]
  exact ENNReal.le_refl _

/-- Almost every pair of invariant starts is good. -/
private theorem pairGood_ae
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region)
    (selfCharge : ENNReal.lt ENNReal.zero (reference.val region))
    (law : Giry.Law space) (invariant : law.val.bind kernel = law.val)
    (reach : law.val.AE (fun input =>
      ∃ count, ENNReal.lt ENNReal.zero (iterate kernel count input region))) :
    (Measure.prod law.val law.val
        (Measure.SFinite.ofFinite law.property.to_finite)).AE
      (pairGood minor measurable) := by
  let pairKernel := parallel kernel kernel
    (fun input => (minor.markov input).to_finite)
    (fun input => (minor.markov input).to_finite)
  let pairLaw := Measure.prod law.val law.val
    (Measure.SFinite.ofFinite law.property.to_finite)
  have missMeasurable := pairMiss_measurable minor measurable
  have hits := pair_hits_region_ae minor measurable selfCharge law invariant reach
  have missNull : pairLaw (pairMiss minor measurable) = ENNReal.zero :=
    hits.mono (fun pair ⟨_, certain⟩ => certain)
  have pairInvariant : pairLaw.bind pairKernel = pairLaw :=
    parallel_invariant _ _ _ _ law.property.to_finite law.property.to_finite
      invariant invariant
  apply Measure.ae_all_iff.mpr
  intro count
  have integral : lintegral pairLaw
      (fun pair => iterate pairKernel count pair (pairMiss minor measurable)) =
        ENNReal.zero := by
    rw [← Measure.bind_apply _ _ missMeasurable,
      bind_iterate_of_invariant pairInvariant count]
    exact missNull
  exact (lintegral_eq_zero_iff
    ((iterate pairKernel count).measurable missMeasurable)).mp integral

/-- The mass that never couples from a pair. -/
private noncomputable def uncoupledLimit
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) (pair : α × α) : ENNReal :=
  ENNReal.iInf (fun count => uncoupledMass minor measurable count pair)

private theorem uncoupledLimit_le_one
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) (pair : α × α) :
    ENNReal.le (uncoupledLimit minor measurable pair) ENNReal.one := by
  have initial := ENNReal.iInf_le
    (fun count => uncoupledMass minor measurable count pair) 0
  rw [uncoupledMass_zero] at initial
  exact initial

private theorem uncoupledLimit_subharmonic
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) (pair : α × α) :
    ENNReal.le (uncoupledLimit minor measurable pair)
      (lintegral (uncoupledKernel minor measurable pair)
        (uncoupledLimit minor measurable)) := by
  have finiteTerm : ∃ count, ENNReal.Finite
      (lintegral (uncoupledKernel minor measurable pair)
        (uncoupledMass minor measurable count)) := by
    refine ⟨0, ?_⟩
    rw [lintegral_congr _ (uncoupledMass_zero minor measurable), lintegral_const,
      ENNReal.one_mul]
    exact ENNReal.finite_of_le (uncoupledKernel_le_one minor measurable pair)
      True.intro
  have limit := lintegral_iInf (uncoupledKernel minor measurable pair)
    (fun count => uncoupledMass minor measurable count)
    (fun count => (iterate (uncoupledKernel minor measurable) count).measurable
      (Space.product space space).univ)
    (fun count state => uncoupledMass_antitone minor measurable
      (Nat.le_succ count) state)
    finiteTerm
  change ENNReal.le (uncoupledLimit minor measurable pair)
    (lintegral (uncoupledKernel minor measurable pair) (fun state =>
      ENNReal.iInf (fun count => uncoupledMass minor measurable count state)))
  rw [limit]
  apply ENNReal.le_iInf
  intro count
  have next : uncoupledMass minor measurable (count + 1) pair =
      lintegral (uncoupledKernel minor measurable pair)
        (uncoupledMass minor measurable count) := by
    rw [uncoupledMass, iterate_succ,
      comp_apply_measurable _ _ _ (Space.product space space).univ]
    rfl
  rw [← next]
  exact ENNReal.iInf_le _ (count + 1)

/-- The largest never-coupled mass over good pairs. -/
private noncomputable def goodSupremum
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) : ENNReal :=
  ENNReal.supremum (fun value => ∃ pair, pairGood minor measurable pair ∧
    value = uncoupledLimit minor measurable pair)

/-- Almost every step from a good pair lands on a good pair, under both the
pair chain and the uncoupled chain. -/
private theorem uncoupledKernel_good
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) {pair : α × α}
    (good : pairGood minor measurable pair) :
    (uncoupledKernel minor measurable pair).AE (pairGood minor measurable) :=
  uncoupledKernel_null_of_parallel_null minor measurable pair
    ((Space.product space space).complement (pairGood_measurable minor measurable))
    (pairGood_step minor measurable good)

/-- A trial from a good pair leaves at most the failed-trial share of the
supremum. -/
private theorem uncoupledLimit_region
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) {pair : α × α}
    (good : pairGood minor measurable pair)
    (member : Set.product region region pair) :
    ENNReal.le (uncoupledLimit minor measurable pair)
      (ENNReal.mul (goodSupremum minor measurable)
        (ENNReal.sub ENNReal.one (ENNReal.finite weight))) := by
  apply ENNReal.le_trans (uncoupledLimit_subharmonic minor measurable pair)
  have bound := lintegral_mono_ae (measure := uncoupledKernel minor measurable pair)
    (right := fun _ => goodSupremum minor measurable)
    ((uncoupledKernel_good minor measurable good).mono (fun state stateGood =>
      ENNReal.le_supremum ⟨state, stateGood, rfl⟩))
  rw [lintegral_const, uncoupledKernel_region_mass minor measurable pair member]
    at bound
  exact bound

/-- Off the region product the never-coupled mass is bounded by the trial
share plus the chance of not yet having reached the region product. -/
private theorem uncoupledLimit_survival
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) (horizon : Nat) :
    ∀ pair, pairGood minor measurable pair →
      ENNReal.le (uncoupledLimit minor measurable pair)
        (ENNReal.add
          (ENNReal.mul (goodSupremum minor measurable)
            (ENNReal.sub ENNReal.one (ENNReal.finite weight)))
          (survival (parallel kernel kernel
              (fun input => (minor.markov input).to_finite)
              (fun input => (minor.markov input).to_finite))
            (Set.product region region)
            (Space.product_set_measurable space space measurable measurable)
            horizon pair)) := by
  let share := ENNReal.mul (goodSupremum minor measurable)
    (ENNReal.sub ENNReal.one (ENNReal.finite weight))
  let pairKernel := parallel kernel kernel
    (fun input => (minor.markov input).to_finite)
    (fun input => (minor.markov input).to_finite)
  let pairMeasurable := Space.product_set_measurable space space measurable measurable
  have belowShare : ∀ extra, ENNReal.le share (ENNReal.add share extra) := by
    intro extra
    have bound := ENNReal.add_le_add_left (ENNReal.zero_le extra) share
    rw [ENNReal.add_zero] at bound
    exact bound
  induction horizon with
  | zero =>
      intro pair _
      rw [survival, iterate_zero, Kernel.deterministic_apply,
        Measure.dirac_apply_univ]
      have bound := ENNReal.add_le_add_right (ENNReal.zero_le share) ENNReal.one
      rw [ENNReal.zero_add] at bound
      exact ENNReal.le_trans (uncoupledLimit_le_one minor measurable pair) bound
  | succ horizon induction =>
      intro pair good
      by_cases member : Set.product region region pair
      · exact ENNReal.le_trans (uncoupledLimit_region minor measurable good member)
          (belowShare _)
      · have survivalMeasurable : ENNRealMeasurable (Space.product space space)
            (survival pairKernel (Set.product region region) pairMeasurable horizon) :=
          (iterate (continueOutside pairKernel (Set.product region region)
            pairMeasurable) horizon).measurable (Space.product space space).univ
        have integral := lintegral_mono_ae (measure := pairKernel pair)
          (left := uncoupledLimit minor measurable)
          (right := fun state => ENNReal.add share
            (survival pairKernel (Set.product region region) pairMeasurable
              horizon state))
          (Measure.AE.mono (pairGood_step minor measurable good)
            (fun state stateGood => induction state stateGood))
        rw [lintegral_add _ (ENNRealMeasurable.constant _ share) survivalMeasurable,
          lintegral_const, (parallel_isProbability minor.markov minor.markov
            pair).univ_eq_one, ENNReal.mul_one] at integral
        have next := survival_succ pairKernel (Set.product region region)
          pairMeasurable horizon pair
        rw [continueOutside, piecewise_apply_of_not_mem _ _ _ _ _ member] at next
        have subharmonic := uncoupledLimit_subharmonic minor measurable pair
        rw [uncoupledKernel_apply_of_not_mem minor measurable member] at subharmonic
        rw [next]
        exact ENNReal.le_trans subharmonic integral

private theorem uncoupledLimit_le_share
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) {pair : α × α}
    (good : pairGood minor measurable pair) :
    ENNReal.le (uncoupledLimit minor measurable pair)
      (ENNReal.mul (goodSupremum minor measurable)
        (ENNReal.sub ENNReal.one (ENNReal.finite weight))) := by
  have vanishes := (hit_mass_eq_one_iff_survival_vanishes _ _ _
    (parallel_isProbability minor.markov minor.markov) pair).mp
    (pairGood_hits minor measurable good)
  have difference : ENNReal.le
      (ENNReal.sub (uncoupledLimit minor measurable pair)
        (ENNReal.mul (goodSupremum minor measurable)
          (ENNReal.sub ENNReal.one (ENNReal.finite weight))))
      ENNReal.zero := by
    rw [← vanishes]
    apply ENNReal.le_iInf
    intro horizon
    apply ENNReal.sub_le_iff_le_add.mpr
    rw [ENNReal.add_comm]
    exact uncoupledLimit_survival minor measurable horizon pair good
  exact ENNReal.sub_eq_zero_iff_le.mp (ENNReal.eq_zero_of_le_zero difference)

private theorem goodSupremum_eq_zero
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region) :
    goodSupremum minor measurable = ENNReal.zero := by
  let supremum := goodSupremum minor measurable
  let failure := ENNReal.sub ENNReal.one (ENNReal.finite weight)
  have selfBound : ENNReal.le supremum (ENNReal.mul supremum failure) := by
    apply ENNReal.supremum_le
    rintro value ⟨pair, good, rfl⟩
    exact uncoupledLimit_le_share minor measurable good
  have bounded : ENNReal.le supremum ENNReal.one := by
    apply ENNReal.supremum_le
    rintro value ⟨pair, _, rfl⟩
    exact uncoupledLimit_le_one minor measurable pair
  have shareFinite : ENNReal.Finite (ENNReal.mul supremum failure) := by
    have below := ENNReal.mul_le_mul_left
      (ENNReal.sub_le_self ENNReal.one (ENNReal.finite weight)) supremum
    rw [ENNReal.mul_one] at below
    exact ENNReal.finite_of_le (ENNReal.le_trans below bounded) True.intro
  have split : ENNReal.add (ENNReal.mul supremum failure)
      (ENNReal.mul supremum (ENNReal.finite weight)) = supremum := by
    rw [← ENNReal.mul_add, ENNReal.sub_add_cancel
      (show ENNReal.le (ENNReal.finite weight) ENNReal.one from
        minor.weightAtMostOne), ENNReal.mul_one]
  have cancelled : ENNReal.le
      (ENNReal.add (ENNReal.mul supremum failure)
        (ENNReal.mul supremum (ENNReal.finite weight)))
      (ENNReal.add (ENNReal.mul supremum failure) ENNReal.zero) := by
    rw [split, ENNReal.add_zero]
    exact selfBound
  have zero := ENNReal.eq_zero_of_le_zero
    (ENNReal.le_of_add_le_add_left_of_finite shareFinite cancelled)
  rcases ENNReal.mul_eq_zero_iff.mp zero with supremumZero | weightZero
  · exact supremumZero
  · exact absurd weightZero (ENNReal.zero_lt_iff_ne_zero.mp
      (show ENNReal.lt ENNReal.zero (ENNReal.finite weight) from
        minor.weightPositive))

/-- Almost every pair of invariant starts eventually couples with
probability one. -/
public theorem uncoupledMass_vanishes
    (minor : MinorizationOn kernel region 1 weight reference)
    (measurable : space.Measurable region)
    (selfCharge : ENNReal.lt ENNReal.zero (reference.val region))
    (law : Giry.Law space) (invariant : law.val.bind kernel = law.val)
    (reach : law.val.AE (fun input =>
      ∃ count, ENNReal.lt ENNReal.zero (iterate kernel count input region))) :
    (Measure.prod law.val law.val
        (Measure.SFinite.ofFinite law.property.to_finite)).AE (fun pair =>
      ENNReal.iInf (fun count => uncoupledMass minor measurable count pair) =
        ENNReal.zero) := by
  apply (pairGood_ae minor measurable selfCharge law invariant reach).mono
  intro pair good
  have bound := uncoupledLimit_le_share minor measurable good
  rw [goodSupremum_eq_zero minor measurable, ENNReal.zero_mul] at bound
  exact ENNReal.eq_zero_of_le_zero bound

end Coupling

end Problib.Measure.Kernel
