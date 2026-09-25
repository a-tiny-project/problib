module

public import Problib.Measure.Kernel.Iteration.Irreducibility
public import Problib.Measure.Kernel.Iteration.Minorization
public import Problib.Measure.AlmostEverywhere
public import Problib.Measure.Integral.Lebesgue.Infimum
public import Problib.Measure.Integral.Lebesgue.Subtract
public import Problib.Measure.Integral.Lebesgue.Zero
public import Problib.Measure.Null

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

end Problib.Measure.Kernel
