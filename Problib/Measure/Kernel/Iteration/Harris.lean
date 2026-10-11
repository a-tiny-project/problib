module

public import Problib.Measure.Kernel.Iteration.Ergodic
public import Problib.Measure.Kernel.Iteration.Period
public import Problib.Measure.Kernel.Iteration.SmallSet.Existence
public import Problib.Measure.StandardBorel.Generator
import Problib.Measure.AlmostEverywhere.Basic
import Problib.Measure.Integral.Lebesgue.Zero

set_option autoImplicit false

/-!
# Every aperiodic positive Harris chain converges

A positive Harris chain on a countably generated space converges in total
variation to its invariant law from every start exactly when it is aperiodic
(`harris_converges_iff_aperiodic`).

The forward direction is `measureAperiodic_of_converges`. The backward direction
(`harris_aperiodic_converges`) starts from a small set charged by the invariant
law, which a countable generator provides (`exists_positive_small_set`). A shift
of its minorant charges the set (`charged_shift`). Aperiodicity minorizes the set
at every count past a threshold (`minorizedAt_eventually`), so one skeleton of
the chain has a one-step small set that its minorant charges and that every start
reaches (`skeleton_reaches`). The skeleton converges almost everywhere
(`strong_small_set_converges_ae`), the envelope carries back to the chain
(`converges_ae_of_skeleton`), and Harris recurrence carries it to every start
(`converges_of_harris_and_ae`).
-/

namespace Problib.Measure.Kernel

open Problib.Real

universe u
variable {α : Type u} {space : Space α}

public section

private theorem mul_positive {left right : ENNReal}
    (leftPositive : ENNReal.lt ENNReal.zero left)
    (rightPositive : ENNReal.lt ENNReal.zero right) :
    ENNReal.lt ENNReal.zero (ENNReal.mul left right) := by
  apply ENNReal.zero_lt_iff_ne_zero.mpr
  intro zero
  rcases ENNReal.mul_eq_zero_iff.mp zero with leftZero | rightZero
  · exact ENNReal.zero_lt_iff_ne_zero.mp leftPositive leftZero
  · exact ENNReal.zero_lt_iff_ne_zero.mp rightPositive rightZero

private theorem positive_of_le {left right : ENNReal}
    (positive : ENNReal.lt ENNReal.zero left) (included : ENNReal.le left right) :
    ENNReal.lt ENNReal.zero right := by
  apply ENNReal.zero_lt_iff_ne_zero.mpr
  intro zero
  rw [zero] at included
  exact ENNReal.zero_lt_iff_ne_zero.mp positive (ENNReal.eq_zero_of_le_zero included)

/-- Harris recurrence against a probability law makes the chain irreducible
against it. -/
private theorem PositiveHarris.irreducible {kernel : Kernel space space}
    {law : Giry.Law space} (harris : PositiveHarris kernel law) :
    MeasureIrreducible kernel law.val :=
  HarrisRecurrent.measureIrreducible harris.markov harris.harris
    (by rw [law.property.univ_eq_one]; exact ENNReal.one_positive)

/-- A chain that charges a small set at time `count` charges every event at
time `count + steps` at least by the set's mass times the minorant's charge. -/
private theorem iterate_through_region {kernel : Kernel space space}
    {region : Set α} {steps : Nat} {weight : NNReal} {minorant : Giry.Law space}
    (measurable : space.Measurable region)
    (minor : MinorizationOn kernel region steps weight minorant)
    (count : Nat) (input : α) {event : Set α} (eventMeasurable : space.Measurable event) :
    ENNReal.le
      (ENNReal.mul ((Measure.smul (ENNReal.finite weight) minorant.val) event)
        (iterate kernel count input region))
      (iterate kernel (count + steps) input event) := by
  rw [iterate_add, comp_apply_measurable _ _ _ eventMeasurable]
  exact lintegral_lower_on _ measurable
    (fun state member => minor.lower state member event eventMeasurable)

/-- A minorant that charges an event charges it after its positive weight. -/
private theorem minorant_charge_positive {kernel : Kernel space space}
    {region : Set α} {steps : Nat} {weight : NNReal} {minorant : Giry.Law space}
    (minor : MinorizationOn kernel region steps weight minorant)
    {event : Set α} (eventMeasurable : space.Measurable event)
    (charged : ENNReal.lt ENNReal.zero (minorant.val event)) :
    ENNReal.lt ENNReal.zero ((Measure.smul (ENNReal.finite weight) minorant.val) event) := by
  rw [Measure.smul_apply_measurable _ _ eventMeasurable]
  exact mul_positive
    (show ENNReal.lt ENNReal.zero (ENNReal.finite weight) from minor.weightPositive) charged

/-- Past the threshold every count minorizes the set, so from every start some
time of the `steps`-skeleton charges the set. -/
private theorem skeleton_reaches {kernel : Kernel space space} {law : Giry.Law space}
    {region : Set α} {minorant : Giry.Law space} {threshold : Nat}
    (irreducible : MeasureIrreducible kernel law.val)
    (measurable : space.Measurable region)
    (positive : ENNReal.lt ENNReal.zero (law.val region))
    (eventually : ∀ count, threshold ≤ count → MinorizedAt kernel region minorant count)
    (selfCharge : ENNReal.lt ENNReal.zero (minorant.val region))
    (steps : Nat) (stepsPositive : 0 < steps) (input : α) :
    ∃ count, ENNReal.lt ENNReal.zero (iterate (iterate kernel steps) count input region) := by
  rcases irreducible.reaches region measurable positive input with ⟨first, reached⟩
  have covers : first + 1 + threshold ≤ steps * (first + 1 + threshold) :=
    Nat.le_mul_of_pos_left _ stepsPositive
  generalize product : steps * (first + 1 + threshold) = total at covers
  rcases eventually (total - (first + 1)) (by omega) with ⟨weight, minor⟩
  refine ⟨first + 1 + threshold, ?_⟩
  rw [iterate_mul, product, show total = first + 1 + (total - (first + 1)) by omega]
  exact positive_of_le
    (mul_positive (minorant_charge_positive minor measurable selfCharge) reached)
    (iterate_through_region measurable minor (first + 1) input measurable)

/-- Under Harris recurrence some shift of a small set's minorant charges the
set: the states that reach the set at a given time cover the space, so the
minorant charges one of them. -/
private theorem charged_shift {kernel : Kernel space space} {law : Giry.Law space}
    {region : Set α} {steps : Nat} {weight : NNReal} {minorant : Giry.Law space}
    (irreducible : MeasureIrreducible kernel law.val)
    (measurable : space.Measurable region)
    (positive : ENNReal.lt ENNReal.zero (law.val region))
    (minor : MinorizationOn kernel region steps weight minorant) :
    ∃ count, ENNReal.lt ENNReal.zero
      ((iterateLaw kernel minor.markov minorant count).val region) := by
  apply Classical.byContradiction
  intro absent
  have null : ∀ count, minorant.val.NullSet (fun state =>
      ENNReal.lt ENNReal.zero (iterate kernel (count + 1) state region)) := by
    intro count
    apply positive_null_of_lintegral_zero minorant.val
      ((iterate kernel (count + 1)).measurable measurable)
    rw [← Measure.bind_apply minorant.val (iterate kernel (count + 1)) measurable]
    exact Classical.byContradiction (fun nonzero =>
      absent ⟨count + 1, ENNReal.zero_lt_iff_ne_zero.mpr nonzero⟩)
  have covered : minorant.val.NullSet Set.univ :=
    (Measure.NullSet.iUnion null).mono (left := Set.univ)
      (fun {state} _ => irreducible.reaches region measurable positive state)
  have total := minorant.property.univ_eq_one
  rw [covered] at total
  exact ENNReal.one_ne_zero total.symm

/-- The skeleton's envelope, read at `count / steps`, bounds the chain at
`count`: the remaining `count % steps` steps fix the invariant law and cannot
increase total variation. -/
private theorem converges_ae_of_skeleton {kernel : Kernel space space}
    {law : Giry.Law space}
    (markov : ∀ input, Measure.IsProbability (kernel input))
    (invariant : law.val.bind kernel = law.val)
    {steps : Nat} (stepsPositive : 0 < steps)
    (skeleton : ConvergesAlmostEverywhere (iterate kernel steps) law) :
    ConvergesAlmostEverywhere kernel law := by
  rcases skeleton.envelope with ⟨bound, boundMeasurable, bounds, vanishes⟩
  refine ⟨markov, fun count => bound (count / steps), fun count => boundMeasurable _, ?_, ?_⟩
  · intro count input
    let remainder := count % steps
    let start : Giry.Law space :=
      ⟨iterate (iterate kernel steps) (count / steps) input,
        iterate_isProbability _ skeleton.markov _ input⟩
    have nonexpansion := totalVariation_bind (iterate kernel remainder)
      (iterate_isProbability kernel markov remainder) start law
    have split : iterate kernel count =
        (iterate kernel (steps * (count / steps))).comp (iterate kernel remainder) := by
      have added := iterate_add kernel (steps * (count / steps)) (count % steps)
      rw [Nat.div_add_mod] at added
      exact added
    have same : Giry.Law.totalVariation
        ⟨iterate kernel count input, iterate_isProbability kernel markov count input⟩ law =
        Giry.Law.totalVariation
          ⟨start.val.bind (iterate kernel remainder),
            start.property.bind (iterate kernel remainder)
              (iterate_isProbability kernel markov remainder)⟩
          ⟨law.val.bind (iterate kernel remainder),
            law.property.bind (iterate kernel remainder)
              (iterate_isProbability kernel markov remainder)⟩ := by
      congr 1
      · apply Subtype.ext
        change iterate kernel count input =
          (iterate (iterate kernel steps) (count / steps) input).bind (iterate kernel remainder)
        rw [split, Kernel.comp_apply, iterate_mul]
      · exact Subtype.ext (invariant_iterate kernel law invariant remainder).symm
    rw [same]
    exact ENNReal.le_trans nonexpansion (bounds (count / steps) input)
  · exact vanishes.mono (fun input zero => by
      apply ENNReal.eq_zero_of_le_zero
      rw [← zero]
      exact ENNReal.le_iInf (fun blocks => by
        have atBlock := ENNReal.iInf_le (fun count => bound (count / steps) input)
          (steps * blocks)
        rw [Nat.mul_div_cancel_left blocks stepsPositive] at atBlock
        exact atBlock))

/-- An aperiodic positive Harris chain with a small set that its invariant law
charges converges in total variation from every start. -/
public theorem harris_aperiodic_converges_of_small_set
    {kernel : Kernel space space} {law : Giry.Law space} {region : Set α}
    (harris : PositiveHarris kernel law)
    (aperiodic : MeasureAperiodic kernel law.val)
    (small : SmallSet kernel region)
    (positive : ENNReal.lt ENNReal.zero (law.val region)) :
    ConvergesFromEveryLaw kernel law := by
  rcases small with ⟨measurable, steps, weight, minorant, minor⟩
  have irreducible := harris.irreducible
  rcases charged_shift irreducible measurable positive minor with ⟨shift, charged⟩
  rcases minorizedAt_eventually harris.invariant irreducible aperiodic measurable positive
      (minor.shift shift) charged with ⟨threshold, eventually⟩
  rcases eventually (threshold + 1) (Nat.le_succ threshold) with ⟨blockWeight, block⟩
  have skeleton := strong_small_set_converges_ae block.skeleton measurable charged law
    (invariant_iterate kernel law harris.invariant (threshold + 1))
    (Measure.ae_of_forall (fun input =>
      skeleton_reaches irreducible measurable positive eventually charged (threshold + 1)
        (Nat.succ_pos threshold) input))
  exact converges_of_harris_and_ae harris
    (converges_ae_of_skeleton harris.markov harris.invariant (Nat.succ_pos threshold) skeleton)

/-- Every aperiodic positive Harris chain on a countably generated space
converges in total variation to its invariant law from every start. -/
public theorem harris_aperiodic_converges
    {kernel : Kernel space space} {law : Giry.Law space}
    (generator : Space.CountableGenerator space)
    (harris : PositiveHarris kernel law)
    (aperiodic : MeasureAperiodic kernel law.val) :
    ConvergesFromEveryLaw kernel law := by
  rcases exists_positive_small_set generator harris.markov harris.irreducible
      law.property.to_finite with
    ⟨region, steps, weight, minorant, measurable, minor, positive, _⟩
  exact harris_aperiodic_converges_of_small_set harris aperiodic
    ⟨measurable, steps, weight, minorant, minor⟩ positive

/-- On a countably generated space a positive Harris chain converges from every
start exactly when it is aperiodic. -/
public theorem harris_converges_iff_aperiodic
    {kernel : Kernel space space} {law : Giry.Law space}
    (generator : Space.CountableGenerator space)
    (harris : PositiveHarris kernel law) :
    ConvergesFromEveryLaw kernel law ↔ MeasureAperiodic kernel law.val :=
  ⟨measureAperiodic_of_converges, harris_aperiodic_converges generator harris⟩

/-- Every aperiodic positive Harris chain on a standard-Borel space converges in
total variation from every start. -/
public theorem harris_aperiodic_converges_standardBorel
    {kernel : Kernel space space} {law : Giry.Law space}
    (presentation : StandardBorel space)
    (harris : PositiveHarris kernel law)
    (aperiodic : MeasureAperiodic kernel law.val) :
    ConvergesFromEveryLaw kernel law :=
  harris_aperiodic_converges presentation.countableGenerator harris aperiodic

end

end Problib.Measure.Kernel
