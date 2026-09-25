module

public import Problib.Measure.Kernel.Iteration.Aperiodicity
public import Problib.Measure.Kernel.Iteration.Minorization
public import Problib.Measure.Kernel.TotalVariation
public import Problib.Analysis.Real.Sequence

set_option autoImplicit false

namespace Problib.Measure.Kernel

open Problib.Real

universe u
variable {α : Type u} {space : Space α}

private theorem toReal_add_finite {left right : ENNReal}
    (leftFinite : ENNReal.Finite left) (rightFinite : ENNReal.Finite right) :
    ENNReal.toReal (ENNReal.add left right) =
      Problib.Real.Construction.Dedekind.add
        (ENNReal.toReal left) (ENNReal.toReal right) := by
  rcases ENNReal.exists_finite_of_finite leftFinite with ⟨leftValue, rfl⟩
  rcases ENNReal.exists_finite_of_finite rightFinite with ⟨rightValue, rfl⟩
  exact NNReal.toReal_add leftValue rightValue

public structure ConvergesFromEveryLaw (kernel : Kernel space space)
    (law : Giry.Law space) : Prop where
  markov : ∀ input, Measure.IsProbability (kernel input)
  converges : ∀ start : Giry.Law space,
    Problib.Analysis.Real.ConvergesTo
      (fun count => ENNReal.toReal (Giry.Law.totalVariation
        (iterateLaw kernel markov start count) law))
      Problib.Real.Construction.Dedekind.zero

public theorem ConvergesFromEveryLaw.invariant
    {kernel : Kernel space space} {law : Giry.Law space}
    (converges : ConvergesFromEveryLaw kernel law) :
    law.val.bind kernel = law.val := by
  let next : Giry.Law space :=
    ⟨law.val.bind kernel, law.property.bind kernel converges.markov⟩
  have original := converges.converges law
  have one (start : Giry.Law space) :
      iterateLaw kernel converges.markov start 1 =
        ⟨start.val.bind kernel,
          start.property.bind kernel converges.markov⟩ := by
    apply Subtype.ext
    change start.val.bind (iterate kernel 1) = start.val.bind kernel
    have once : iterate kernel 1 = kernel := by
      rw [iterate_succ, iterate_zero, comp_deterministic]
      apply Kernel.ext
      intro input
      rw [map_apply, Measure.map_id]
    rw [once]
  have forward (count : Nat) :
      iterateLaw kernel converges.markov law (count + 1) =
        ⟨(iterateLaw kernel converges.markov law count).val.bind kernel,
          (iterateLaw kernel converges.markov law count).property.bind
            kernel converges.markov⟩ := by
    rw [iterateLaw_add, one]
  have distanceBound (count : Nat) : ENNReal.le
      (Giry.Law.totalVariation next law)
      (ENNReal.add
        (Giry.Law.totalVariation
          (iterateLaw kernel converges.markov law count) law)
        (Giry.Law.totalVariation
          (iterateLaw kernel converges.markov law (count + 1)) law)) := by
    have triangle := Giry.Law.totalVariation_triangle next
      (iterateLaw kernel converges.markov law (count + 1)) law
    have contraction := totalVariation_bind kernel converges.markov law
      (iterateLaw kernel converges.markov law count)
    change ENNReal.le
      (Giry.Law.totalVariation next
        ⟨(iterateLaw kernel converges.markov law count).val.bind kernel,
          (iterateLaw kernel converges.markov law count).property.bind
            kernel converges.markov⟩)
      (Giry.Law.totalVariation law
        (iterateLaw kernel converges.markov law count)) at contraction
    rw [← forward count,
      Giry.Law.totalVariation_symm law
        (iterateLaw kernel converges.markov law count)] at contraction
    exact ENNReal.le_trans triangle
      (ENNReal.add_le_add_right contraction _)
  have distanceFinite : ENNReal.Finite
      (Giry.Law.totalVariation next law) :=
    ENNReal.finite_of_le (Giry.Law.totalVariation_le_one next law) True.intro
  have realNonpositive : Problib.Real.Construction.Dedekind.le
      (ENNReal.toReal (Giry.Law.totalVariation next law))
      Problib.Real.Construction.Dedekind.zero := by
    apply Problib.Analysis.Real.le_of_forall_lt_add
    intro epsilon positive
    have halfPositive := Problib.Analysis.Real.half_positive positive
    rcases original _ halfPositive with ⟨stage, close⟩
    have firstClose := close stage (Nat.le_refl stage)
    have secondClose := close (stage + 1) (Nat.le_succ stage)
    rw [Problib.Real.Construction.Dedekind.sub_zero,
      Problib.Analysis.Real.abs_of_nonnegative
        (ENNReal.toReal_nonnegative _)] at firstClose secondClose
    have firstFinite : ENNReal.Finite
        (Giry.Law.totalVariation
          (iterateLaw kernel converges.markov law stage) law) :=
      ENNReal.finite_of_le (Giry.Law.totalVariation_le_one _ _) True.intro
    have secondFinite : ENNReal.Finite
        (Giry.Law.totalVariation
          (iterateLaw kernel converges.markov law (stage + 1)) law) :=
      ENNReal.finite_of_le (Giry.Law.totalVariation_le_one _ _) True.intro
    have realBound := (ENNReal.toReal_le_toReal_iff distanceFinite
      (ENNReal.add_finite firstFinite secondFinite)).mpr
        (distanceBound stage)
    rw [toReal_add_finite firstFinite secondFinite] at realBound
    have small := Problib.Real.Construction.Dedekind.add_lt_add
      firstClose secondClose
    rw [Problib.Analysis.Real.add_half] at small
    rw [Problib.Real.Construction.Dedekind.zero_add]
    exact Problib.Real.Construction.Dedekind.lt_of_le_of_lt
      realBound small
  have zeroReal := Problib.Real.Construction.Dedekind.le_antisymm
    realNonpositive (ENNReal.toReal_nonnegative _)
  have zeroTV : Giry.Law.totalVariation next law = ENNReal.zero := by
    apply ENNReal.le_antisymm
    · apply (ENNReal.toReal_le_toReal_iff distanceFinite
        (show ENNReal.Finite ENNReal.zero from True.intro)).mp
      simpa only [ENNReal.toReal_zero] using
        Problib.Real.Construction.Dedekind.le_of_equal zeroReal
    · exact ENNReal.zero_le _
  have same := (Giry.Law.totalVariation_eq_zero_iff next law).mp zeroTV
  exact congrArg Subtype.val same

public theorem ConvergesFromEveryLaw.invariant_unique
    {kernel : Kernel space space} {law : Giry.Law space}
    (converges : ConvergesFromEveryLaw kernel law) (other : Giry.Law space)
    (invariant : other.val.bind kernel = other.val) : other = law := by
  have stationary : ∀ count,
      iterateLaw kernel converges.markov other count = other :=
    iterateLaw_invariant kernel converges.markov other invariant
  have limit := converges.converges other
  have constant : Problib.Analysis.Real.ConvergesTo
      (fun _ : Nat => ENNReal.toReal (Giry.Law.totalVariation other law))
      Problib.Real.Construction.Dedekind.zero := by
    simpa only [stationary] using limit
  have zeroReal : ENNReal.toReal (Giry.Law.totalVariation other law) =
      Problib.Real.Construction.Dedekind.zero := by
    apply Classical.byContradiction
    intro nonzero
    have nonnegative := ENNReal.toReal_nonnegative
      (Giry.Law.totalVariation other law)
    have positive : Problib.Real.Construction.Dedekind.lt
        Problib.Real.Construction.Dedekind.zero
        (ENNReal.toReal (Giry.Law.totalVariation other law)) :=
      ⟨nonnegative, fun reverse => nonzero
        (Problib.Real.Construction.Dedekind.le_antisymm
          nonnegative reverse).symm⟩
    rcases constant _ positive with ⟨stage, close⟩
    have near := close stage (Nat.le_refl stage)
    rw [Problib.Real.Construction.Dedekind.sub_zero,
      Problib.Analysis.Real.abs_of_nonnegative nonnegative] at near
    exact Problib.Real.Construction.Dedekind.lt_irrefl _ near
  have finite : ENNReal.Finite (Giry.Law.totalVariation other law) :=
    ENNReal.finite_of_le (Giry.Law.totalVariation_le_one other law) True.intro
  have zeroTV : Giry.Law.totalVariation other law = ENNReal.zero := by
    apply ENNReal.le_antisymm
    · apply (ENNReal.toReal_le_toReal_iff finite
        (show ENNReal.Finite ENNReal.zero from True.intro)).mp
      simpa only [ENNReal.toReal_zero] using
        Problib.Real.Construction.Dedekind.le_of_equal zeroReal
    · exact ENNReal.zero_le _
  exact (Giry.Law.totalVariation_eq_zero_iff other law).mp zeroTV

/-- Any every-start TV limit forbids a positive measurable cycle. -/
public theorem measureAperiodic_of_converges
    {kernel : Kernel space space} {law : Giry.Law space}
    (converges : ConvergesFromEveryLaw kernel law) :
    MeasureAperiodic kernel law.val := by
  intro period cell cycle
  apply Classical.byContradiction
  intro tooLong
  have periodAtLeastTwo : 2 ≤ period := by omega
  have zeroRange : 0 < period := by omega
  have oneRange : 1 < period := by omega
  have zeroPositive := cycle.positive 0 zeroRange
  have onePositive := cycle.positive 1 oneRange
  have zeroMember : ∃ value, cell 0 value := by
    apply Classical.byContradiction
    intro empty
    have null : law.val (cell 0) = ENNReal.zero := by
      have same : cell 0 = Set.empty := by
        funext value
        apply propext
        constructor
        · intro member
          exact False.elim (empty ⟨value, member⟩)
        · intro member
          exact False.elim member
      rw [same]
      exact law.val.empty_apply
    exact (ENNReal.zero_lt_iff_ne_zero.mp zeroPositive) null
  rcases zeroMember with ⟨start, startInZero⟩
  let initial : Giry.Law space :=
    ⟨Measure.dirac space start, Measure.IsProbability.dirac space start⟩
  have alongCycles : ∀ blocks,
      iterate kernel (blocks * period) start (cell 0) = ENNReal.one := by
    intro blocks
    have advanced := cycle.iterate_advance converges.markov
      0 zeroRange start startInZero (blocks * period)
    have modZero : (blocks * period) % period = 0 := by
      rw [Nat.mul_comm blocks period, Nat.mul_mod_right]
    simpa only [Nat.zero_add, modZero] using advanced
  let gap := ENNReal.sub ENNReal.one (law.val (cell 0))
  have gapPositive : ENNReal.lt ENNReal.zero gap := by
    have complementPositive : ENNReal.lt ENNReal.zero
        (law.val (Set.complement (cell 0))) := by
      have included : Set.Subset (cell 1)
          (Set.complement (cell 0)) := by
        intro value memberOne memberZero
        exact cycle.disjoint 0 1 zeroRange oneRange (by omega)
          value memberZero memberOne
      have bound := law.val.mono included
      exact ⟨ENNReal.le_trans onePositive.1 bound,
        fun reverse => onePositive.2 (ENNReal.le_trans bound reverse)⟩
    change ENNReal.lt ENNReal.zero
      (ENNReal.sub ENNReal.one (law.val (cell 0)))
    rw [← law.property.apply_complement (cycle.measurable 0 zeroRange)]
    exact complementPositive
  have tvBound : ∀ blocks,
      ENNReal.le gap
        (Giry.Law.totalVariation
          (iterateLaw kernel converges.markov initial (blocks * period)) law) := by
    intro blocks
    have eventBound := Giry.Law.event_sub_le
      (iterateLaw kernel converges.markov initial (blocks * period))
      law (cycle.measurable 0 zeroRange)
    have eventMass : (iterateLaw kernel converges.markov initial
        (blocks * period)).val (cell 0) = ENNReal.one := by
      change ((Measure.dirac space start).bind
        (iterate kernel (blocks * period))) (cell 0) = ENNReal.one
      rw [Measure.dirac_bind]
      exact alongCycles blocks
    rw [eventMass] at eventBound
    exact eventBound
  have gapFinite : ENNReal.Finite gap :=
    ENNReal.finite_of_le (ENNReal.sub_le_self _ _)
      (show ENNReal.Finite ENNReal.one from True.intro)
  have realGapPositive : Problib.Real.Construction.Dedekind.lt
      Problib.Real.Construction.Dedekind.zero (ENNReal.toReal gap) := by
    rw [← ENNReal.toReal_zero]
    exact (ENNReal.toReal_lt_toReal_iff
      (show ENNReal.Finite ENNReal.zero from True.intro)
      gapFinite).mpr gapPositive
  rcases converges.converges initial (ENNReal.toReal gap) realGapPositive with
    ⟨stage, close⟩
  let blocks := stage
  have later : stage ≤ blocks * period := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left stage
      (show 1 ≤ period by omega)
  have near := close (blocks * period) later
  have lowerReal : Problib.Real.Construction.Dedekind.le
      (ENNReal.toReal gap)
      (ENNReal.toReal (Giry.Law.totalVariation
        (iterateLaw kernel converges.markov initial (blocks * period)) law)) := by
    exact (ENNReal.toReal_le_toReal_iff gapFinite
      (ENNReal.finite_of_le
        (Giry.Law.totalVariation_le_one _ _)
        (show ENNReal.Finite ENNReal.one from True.intro))).mpr
      (tvBound blocks)
  have realSmall : Problib.Real.Construction.Dedekind.lt
      (ENNReal.toReal (Giry.Law.totalVariation
        (iterateLaw kernel converges.markov initial (blocks * period)) law))
      (ENNReal.toReal gap) := by
    simpa only [Problib.Real.Construction.Dedekind.sub_zero,
      Problib.Analysis.Real.abs_of_nonnegative
        (ENNReal.toReal_nonnegative _)] using near
  exact False.elim (Problib.Real.Construction.Dedekind.lt_irrefl _
    (Problib.Real.Construction.Dedekind.lt_of_le_of_lt
      lowerReal realSmall))

public theorem minorization_convergesFromEveryLaw
    {kernel : Kernel space space} {steps : Nat} {weight : NNReal}
    {reference : Giry.Law space}
    (minor : Minorization kernel steps weight reference)
    (law : Giry.Law space) (invariant : law.val.bind kernel = law.val) :
    ConvergesFromEveryLaw kernel law := by
  refine ⟨minor.markov, ?_⟩
  intro start
  exact minorization_converges minor law start invariant

end Problib.Measure.Kernel
