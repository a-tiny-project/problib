module

public import Problib.Measure.Kernel.TotalVariation
public import Problib.Measure.Kernel.Iteration.Basic
public import Problib.Real.Extended.Power
public import Problib.Analysis.Real.Sequence

set_option autoImplicit false

namespace Problib.Measure.Kernel

open Problib.Real

universe u

variable {α : Type u} {space : Space α}

/-- A uniform lower bound on one positive iterate of a Markov kernel. -/
public structure Minorization (kernel : Kernel space space) (steps : Nat)
    (weight : NNReal) (reference : Giry.Law space) : Prop where
  markov : ∀ input, Measure.IsProbability (kernel input)
  stepsPositive : 0 < steps
  weightPositive : NNReal.lt NNReal.zero weight
  weightAtMostOne : NNReal.le weight NNReal.one
  lower : ∀ input event, space.Measurable event →
    ENNReal.le
      ((Measure.smul (ENNReal.finite weight) reference.val) event)
      ((Kernel.iterate kernel steps input) event)

/-- A uniform lower bound on one positive iterate of a Markov kernel, from
every state of `region`. -/
public structure MinorizationOn (kernel : Kernel space space) (region : Set α)
    (steps : Nat) (weight : NNReal) (reference : Giry.Law space) : Prop where
  markov : ∀ input, Measure.IsProbability (kernel input)
  stepsPositive : 0 < steps
  weightPositive : NNReal.lt NNReal.zero weight
  weightAtMostOne : NNReal.le weight NNReal.one
  lower : ∀ input, region input → ∀ event, space.Measurable event →
    ENNReal.le
      ((Measure.smul (ENNReal.finite weight) reference.val) event)
      ((Kernel.iterate kernel steps input) event)

/-- A global minorization is exactly a local minorization on the whole
state space. -/
public theorem minorization_on_univ (kernel : Kernel space space) (steps : Nat)
    (weight : NNReal) (reference : Giry.Law space) :
    Minorization kernel steps weight reference ↔
      MinorizationOn kernel Set.univ steps weight reference := by
  constructor
  · intro minor
    exact ⟨minor.markov, minor.stepsPositive, minor.weightPositive,
      minor.weightAtMostOne, fun input _ event measurable =>
        minor.lower input event measurable⟩
  · intro minor
    exact ⟨minor.markov, minor.stepsPositive, minor.weightPositive,
      minor.weightAtMostOne, fun input event measurable =>
        minor.lower input (by trivial) event measurable⟩

/-- Every finite iterate of a Markov kernel remains Markov. -/
public theorem iterate_isProbability (kernel : Kernel space space)
    (markov : ∀ input, Measure.IsProbability (kernel input))
    (steps : Nat) (input : α) :
    Measure.IsProbability (iterate kernel steps input) := by
  induction steps generalizing input with
  | zero =>
      rw [iterate_zero, Kernel.deterministic_apply]
      exact Measure.IsProbability.dirac space input
  | succ steps induction =>
      rw [iterate_succ, Kernel.comp_apply]
      exact (markov input).bind (iterate kernel steps) induction

/-- An invariant probability law remains invariant under every iterate. -/
public theorem invariant_iterate (kernel : Kernel space space)
    (π : Giry.Law space) (invariant : π.val.bind kernel = π.val)
    (steps : Nat) : π.val.bind (iterate kernel steps) = π.val := by
  induction steps with
  | zero =>
      rw [iterate_zero, Measure.bind_deterministic, Measure.map_id]
  | succ steps induction =>
      rw [iterate_succ_right, ← Measure.bind_assoc, induction, invariant]

/-- Consecutive iteration counts compose in execution order. -/
public theorem iterate_add (kernel : Kernel space space) (first second : Nat) :
    iterate kernel (first + second) =
      (iterate kernel first).comp (iterate kernel second) := by
  induction second with
  | zero =>
      rw [Nat.add_zero, iterate_zero, comp_deterministic]
      apply Kernel.ext
      intro input
      rw [map_apply, Measure.map_id]
  | succ second induction =>
      rw [Nat.add_succ, iterate_succ_right, iterate_succ_right,
        ← comp_assoc, ← induction]

/-- Apply a finite number of Markov transitions to a probability law. -/
@[expose] public noncomputable def iterateLaw (kernel : Kernel space space)
    (markov : ∀ input, Measure.IsProbability (kernel input))
    (law : Giry.Law space) (steps : Nat) : Giry.Law space :=
  ⟨law.val.bind (iterate kernel steps),
    law.property.bind (iterate kernel steps)
      (iterate_isProbability kernel markov steps)⟩

public theorem iterateLaw_zero (kernel : Kernel space space)
    (markov : ∀ input, Measure.IsProbability (kernel input))
    (law : Giry.Law space) : iterateLaw kernel markov law 0 = law := by
  apply Subtype.ext
  change law.val.bind (iterate kernel 0) = law.val
  rw [iterate_zero, Measure.bind_deterministic, Measure.map_id]

public theorem iterateLaw_add (kernel : Kernel space space)
    (markov : ∀ input, Measure.IsProbability (kernel input))
    (law : Giry.Law space) (first second : Nat) :
    iterateLaw kernel markov law (first + second) =
      iterateLaw kernel markov (iterateLaw kernel markov law first) second := by
  apply Subtype.ext
  change law.val.bind (iterate kernel (first + second)) =
    (law.val.bind (iterate kernel first)).bind (iterate kernel second)
  rw [iterate_add, Measure.bind_assoc]

public theorem iterateLaw_invariant (kernel : Kernel space space)
    (markov : ∀ input, Measure.IsProbability (kernel input))
    (law : Giry.Law space) (invariant : law.val.bind kernel = law.val)
    (steps : Nat) : iterateLaw kernel markov law steps = law := by
  apply Subtype.ext
  exact invariant_iterate kernel law invariant steps

/-- Removing the common minorizing mass leaves at most the unused mass in
each event. The residual is constructed only for this fiberwise proof. -/
private theorem centered_event_le {kernel : Kernel space space}
    {steps : Nat} {weight : NNReal} {reference : Giry.Law space}
    (minor : Minorization kernel steps weight reference)
    (input : α) {event : Set α} (measurable : space.Measurable event) :
    ENNReal.le
      (ENNReal.sub ((iterate kernel steps input) event)
        (ENNReal.mul (ENNReal.finite weight) (reference.val event)))
      (ENNReal.sub ENNReal.one (ENNReal.finite weight)) := by
  have included : ∀ probe, space.Measurable probe →
      ENNReal.le ((Measure.smul (ENNReal.finite weight) reference.val) probe)
        ((iterate kernel steps input) probe) :=
    minor.lower input
  have finiteReference : Measure.IsFinite
      (Measure.smul (ENNReal.finite weight) reference.val) :=
    Measure.IsFinite.smul (ENNReal.finite weight) True.intro
      reference.property.to_finite
  let residual := Measure.subtract finiteReference included
  have comparison := residual.mono (Set.subset_univ event)
  have probability := iterate_isProbability kernel minor.markov steps input
  change ENNReal.le
    ((Measure.subtract finiteReference included) event)
    ((Measure.subtract finiteReference included) Set.univ) at comparison
  rw [Measure.subtract_apply finiteReference included measurable,
    Measure.subtract_apply finiteReference included space.univ,
    Measure.smul_apply_measurable _ _ measurable,
    Measure.smul_apply_measurable _ _ space.univ,
    probability.univ_eq_one, reference.property.univ_eq_one,
    ENNReal.mul_one] at comparison
  exact comparison

/-- The common mass cancels between the integrals of two probability starts. -/
private theorem centered_lintegral_difference_le
    {kernel : Kernel space space} {steps : Nat} {weight : NNReal}
    {reference : Giry.Law space}
    (minor : Minorization kernel steps weight reference)
    (μ η : Giry.Law space) {event : Set α}
    (measurable : space.Measurable event) :
    ENNReal.le
      (ENNReal.sub
        (lintegral μ.val (fun input => (iterate kernel steps input) event))
        (lintegral η.val (fun input => (iterate kernel steps input) event)))
      (ENNReal.mul
        (ENNReal.sub ENNReal.one (ENNReal.finite weight))
        (Giry.Law.totalVariation μ η)) := by
  let common := ENNReal.mul (ENNReal.finite weight) (reference.val event)
  let remainder : α → ENNReal := fun input =>
    ENNReal.sub ((iterate kernel steps input) event) common
  let ceiling := ENNReal.sub ENNReal.one (ENNReal.finite weight)
  have lower (input : α) :
      ENNReal.le common ((iterate kernel steps input) event) := by
    simpa only [common, Measure.smul_apply_measurable _ _ measurable] using
      minor.lower input event measurable
  have split (input : α) :
      (iterate kernel steps input) event = ENNReal.add common (remainder input) := by
    simpa only [remainder, ENNReal.add_comm] using
      (ENNReal.sub_add_cancel (lower input)).symm
  have remainderMeasurable : ENNRealMeasurable space remainder :=
    ENNRealMeasurable.sub
      ((iterate kernel steps).measurable measurable)
      (ENNRealMeasurable.constant space common)
  have remainderBound (input : α) : ENNReal.le (remainder input) ceiling := by
    exact centered_event_le minor input measurable
  have integralSplit (law : Giry.Law space) :
      lintegral law.val (fun input => (iterate kernel steps input) event) =
        ENNReal.add common (lintegral law.val remainder) := by
    calc
      lintegral law.val (fun input => (iterate kernel steps input) event) =
          lintegral law.val (fun input => ENNReal.add common (remainder input)) := by
        apply lintegral_congr
        intro input
        exact split input
      _ = ENNReal.add (lintegral law.val (fun _ => common))
          (lintegral law.val remainder) :=
        lintegral_add law.val
          (ENNRealMeasurable.constant space common) remainderMeasurable
      _ = ENNReal.add common (lintegral law.val remainder) := by
        rw [lintegral_const, law.property.univ_eq_one, ENNReal.mul_one]
  have scaled := Giry.Law.lintegral_sub_le_scaled_totalVariation
    μ η remainderMeasurable ceiling remainderBound
  have shifted := ENNReal.sub_le_iff_le_add.mp scaled
  rw [integralSplit μ, integralSplit η]
  apply ENNReal.sub_le_iff_le_add.mpr
  have withCommon := ENNReal.add_le_add_left shifted common
  simpa only [ENNReal.add_assoc, ENNReal.add_left_comm,
    ENNReal.add_comm] using withCommon

/-- A uniformly minorized block contracts total variation by its unused
probability mass. -/
public theorem minorization_block_contraction
    {kernel : Kernel space space} {steps : Nat} {weight : NNReal}
    {reference : Giry.Law space}
    (minor : Minorization kernel steps weight reference)
    (μ η : Giry.Law space) :
    ENNReal.le
      (Giry.Law.totalVariation
        ⟨μ.val.bind (iterate kernel steps),
          μ.property.bind (iterate kernel steps)
            (iterate_isProbability kernel minor.markov steps)⟩
        ⟨η.val.bind (iterate kernel steps),
          η.property.bind (iterate kernel steps)
            (iterate_isProbability kernel minor.markov steps)⟩)
      (ENNReal.mul
        (ENNReal.sub ENNReal.one (ENNReal.finite weight))
        (Giry.Law.totalVariation μ η)) := by
  unfold Giry.Law.totalVariation
  apply ENNReal.supremum_le
  rintro distance ⟨event, measurable, rfl⟩
  change ENNReal.le
    (ENNReal.max
      (ENNReal.sub
        (μ.val.bind (iterate kernel steps) event)
        (η.val.bind (iterate kernel steps) event))
      (ENNReal.sub
        (η.val.bind (iterate kernel steps) event)
        (μ.val.bind (iterate kernel steps) event)))
    (ENNReal.mul
      (ENNReal.sub ENNReal.one (ENNReal.finite weight))
      (Giry.Law.totalVariation μ η))
  rw [Measure.bind_apply μ.val (iterate kernel steps) measurable,
    Measure.bind_apply η.val (iterate kernel steps) measurable]
  apply ENNReal.max_le
  · exact centered_lintegral_difference_le minor μ η measurable
  · have reverse := centered_lintegral_difference_le minor η μ measurable
    rwa [Giry.Law.totalVariation_symm η μ] at reverse

/-- Repeating the minorized block multiplies its contraction factor. -/
private theorem minorization_block_rate
    {kernel : Kernel space space} {steps : Nat} {weight : NNReal}
    {reference : Giry.Law space}
    (minor : Minorization kernel steps weight reference)
    (π μ : Giry.Law space) (invariant : π.val.bind kernel = π.val)
    (blocks : Nat) :
    ENNReal.le
      (Giry.Law.totalVariation
        (iterateLaw kernel minor.markov μ (blocks * steps)) π)
      (ENNReal.mul
        (ENNReal.pow (ENNReal.sub ENNReal.one (ENNReal.finite weight)) blocks)
        (Giry.Law.totalVariation μ π)) := by
  induction blocks with
  | zero =>
      rw [Nat.zero_mul, iterateLaw_zero, ENNReal.pow_zero, ENNReal.one_mul]
      exact ENNReal.le_refl _
  | succ blocks induction =>
      rw [Nat.succ_mul, iterateLaw_add, ENNReal.pow_succ]
      have contracted := minorization_block_contraction minor
        (iterateLaw kernel minor.markov μ (blocks * steps)) π
      change ENNReal.le
        (Giry.Law.totalVariation
          (iterateLaw kernel minor.markov
            (iterateLaw kernel minor.markov μ (blocks * steps)) steps)
          (iterateLaw kernel minor.markov π steps))
        (ENNReal.mul (ENNReal.sub ENNReal.one (ENNReal.finite weight))
          (Giry.Law.totalVariation
            (iterateLaw kernel minor.markov μ (blocks * steps)) π)) at contracted
      rw [iterateLaw_invariant kernel minor.markov π invariant steps] at contracted
      have scaled := ENNReal.mul_le_mul_left induction
        (ENNReal.sub ENNReal.one (ENNReal.finite weight))
      have chain := ENNReal.le_trans contracted scaled
      simpa only [ENNReal.mul_assoc] using chain

/-- A minorized Markov kernel converges toward any invariant probability law
at the geometric rate set by its block length. -/
public theorem minorization_contraction
    {kernel : Kernel space space} {steps : Nat} {weight : NNReal}
    {reference : Giry.Law space}
    (minor : Minorization kernel steps weight reference)
    (π μ : Giry.Law space) (invariant : π.val.bind kernel = π.val)
    (count : Nat) :
    ENNReal.le
      (Giry.Law.totalVariation
        ⟨μ.val.bind (iterate kernel count),
          μ.property.bind (iterate kernel count)
            (iterate_isProbability kernel minor.markov count)⟩ π)
      (ENNReal.mul
        (ENNReal.pow (ENNReal.sub ENNReal.one (ENNReal.finite weight))
          (count / steps))
        (Giry.Law.totalVariation μ π)) := by
  change ENNReal.le
    (Giry.Law.totalVariation (iterateLaw kernel minor.markov μ count) π)
    (ENNReal.mul
      (ENNReal.pow (ENNReal.sub ENNReal.one (ENNReal.finite weight))
        (count / steps))
      (Giry.Law.totalVariation μ π))
  let blocks := count / steps
  let remainder := count % steps
  have division : blocks * steps + remainder = count := by
    calc
      blocks * steps + remainder = remainder + steps * blocks := by
        rw [Nat.add_comm, Nat.mul_comm]
      _ = count := Nat.mod_add_div count steps
  have nonexpansion := totalVariation_bind
    (iterate kernel remainder)
    (iterate_isProbability kernel minor.markov remainder)
    (iterateLaw kernel minor.markov μ (blocks * steps)) π
  change ENNReal.le
    (Giry.Law.totalVariation
      (iterateLaw kernel minor.markov
        (iterateLaw kernel minor.markov μ (blocks * steps)) remainder)
      (iterateLaw kernel minor.markov π remainder))
    (Giry.Law.totalVariation
      (iterateLaw kernel minor.markov μ (blocks * steps)) π) at nonexpansion
  rw [iterateLaw_invariant kernel minor.markov π invariant remainder] at nonexpansion
  have combined := ENNReal.le_trans nonexpansion
    (minorization_block_rate minor π μ invariant blocks)
  rw [← iterateLaw_add, division] at combined
  exact combined

/-- A positive minorization weight leaves a contraction factor below one. -/
public theorem minorization_decay_base_lt_one
    {kernel : Kernel space space} {steps : Nat} {weight : NNReal}
    {reference : Giry.Law space}
    (minor : Minorization kernel steps weight reference) :
    ENNReal.lt (ENNReal.sub ENNReal.one (ENNReal.finite weight))
      ENNReal.one := by
  have positive := minor.weightPositive
  have strict : NNReal.lt (NNReal.sub NNReal.one weight)
      (NNReal.add (NNReal.sub NNReal.one weight) weight) := by
    have shifted :=
      (NNReal.add_lt_add_left_iff (shift := NNReal.sub NNReal.one weight)).mpr
        positive
    simpa only [NNReal.add_zero] using shifted
  rw [NNReal.sub_add_cancel minor.weightAtMostOne] at strict
  exact strict

/-- Every probability start converges in total variation to an invariant law
under uniform minorization. -/
public theorem minorization_converges
    {kernel : Kernel space space} {steps : Nat} {weight : NNReal}
    {reference : Giry.Law space}
    (minor : Minorization kernel steps weight reference)
    (π μ : Giry.Law space) (invariant : π.val.bind kernel = π.val) :
    Problib.Analysis.Real.ConvergesTo
      (fun count => ENNReal.toReal
        (Giry.Law.totalVariation
          ⟨μ.val.bind (iterate kernel count),
            μ.property.bind (iterate kernel count)
              (iterate_isProbability kernel minor.markov count)⟩ π))
      Problib.Real.Construction.Dedekind.zero := by
  open Problib.Real.Construction.Dedekind in
    intro tolerance tolerancePositive
  have toleranceNonnegative :=
    Problib.Real.Construction.Dedekind.le_of_lt tolerancePositive
  let threshold := ENNReal.ofReal tolerance
  have thresholdPositive : ENNReal.lt ENNReal.zero threshold := by
    rw [← ENNReal.ofReal_zero]
    exact (ENNReal.ofReal_lt_ofReal_iff
      (Problib.Real.Construction.Dedekind.le_refl _)
      toleranceNonnegative).mpr tolerancePositive
  rcases ENNReal.pow_eventually_lt
    (minorization_decay_base_lt_one minor) thresholdPositive with
    ⟨stage, small⟩
  refine ⟨stage * steps, fun index later => ?_⟩
  have quotient : stage ≤ index / steps :=
    (Nat.le_div_iff_mul_le minor.stepsPositive).mpr later
  have rate := minorization_contraction minor π μ invariant index
  have tvOne := Giry.Law.totalVariation_le_one μ π
  have scaled := ENNReal.mul_le_mul_left tvOne
    (ENNReal.pow (ENNReal.sub ENNReal.one (ENNReal.finite weight))
      (index / steps))
  rw [ENNReal.mul_one] at scaled
  have tvPower := ENNReal.le_trans rate scaled
  have powerSmall := small (index / steps) quotient
  have tvSmall : ENNReal.lt
      (Giry.Law.totalVariation (iterateLaw kernel minor.markov μ index) π)
      threshold :=
    ⟨ENNReal.le_trans tvPower powerSmall.left,
      fun reverse => powerSmall.right (ENNReal.le_trans reverse tvPower)⟩
  have tvFinite : ENNReal.Finite
      (Giry.Law.totalVariation (iterateLaw kernel minor.markov μ index) π) :=
    ENNReal.finite_of_le
      (Giry.Law.totalVariation_le_one _ _) True.intro
  have realSmall := (ENNReal.toReal_lt_toReal_iff tvFinite
    (ENNReal.ofReal_finite tolerance)).mpr tvSmall
  rw [ENNReal.toReal_ofReal toleranceNonnegative] at realSmall
  change Problib.Real.Construction.Dedekind.lt
    (Problib.Analysis.Real.abs
      (Problib.Real.Construction.Dedekind.sub
        (ENNReal.toReal
          (Giry.Law.totalVariation (iterateLaw kernel minor.markov μ index) π))
        Problib.Real.Construction.Dedekind.zero)) tolerance
  rw [Problib.Real.Construction.Dedekind.sub_zero,
    Problib.Analysis.Real.abs_of_nonnegative
      (ENNReal.toReal_nonnegative _)]
  exact realSmall

/-- A uniformly minorized Markov kernel has at most one invariant probability
law. -/
public theorem minorization_unique_invariant
    {kernel : Kernel space space} {steps : Nat} {weight : NNReal}
    {reference : Giry.Law space}
    (minor : Minorization kernel steps weight reference)
    (π ρ : Giry.Law space)
    (πInvariant : π.val.bind kernel = π.val)
    (ρInvariant : ρ.val.bind kernel = ρ.val) : π = ρ := by
  have contracted := minorization_block_contraction minor π ρ
  change ENNReal.le
    (Giry.Law.totalVariation
      (iterateLaw kernel minor.markov π steps)
      (iterateLaw kernel minor.markov ρ steps))
    (ENNReal.mul (ENNReal.sub ENNReal.one (ENNReal.finite weight))
      (Giry.Law.totalVariation π ρ)) at contracted
  rw [iterateLaw_invariant kernel minor.markov π πInvariant steps,
    iterateLaw_invariant kernel minor.markov ρ ρInvariant steps] at contracted
  by_cases zero : Giry.Law.totalVariation π ρ = ENNReal.zero
  · exact (Giry.Law.totalVariation_eq_zero_iff π ρ).mp zero
  · have positive := ENNReal.zero_lt_iff_ne_zero.mpr zero
    have finite := ENNReal.finite_of_le
      (Giry.Law.totalVariation_le_one π ρ) True.intro
    have scaled : ENNReal.le
        (ENNReal.mul ENNReal.one (Giry.Law.totalVariation π ρ))
        (ENNReal.mul (ENNReal.sub ENNReal.one (ENNReal.finite weight))
          (Giry.Law.totalVariation π ρ)) := by
      rw [ENNReal.one_mul]
      exact contracted
    have reverse := (ENNReal.mul_le_mul_right_iff finite positive).mp
      scaled
    exact False.elim ((minorization_decay_base_lt_one minor).right reverse)

end Problib.Measure.Kernel
