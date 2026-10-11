module

public import Problib.Measure.Kernel.Iteration.SmallSet
public import Problib.Measure.Kernel.Iteration.Irreducibility
public import Problib.Measure.Kernel.Iteration.Aperiodicity
public import Problib.Measure.Kernel.Iteration.Semigroup
import Problib.Measure.Integral.Lebesgue.Measure
import Problib.Measure.Integral.Lebesgue.Zero

set_option autoImplicit false

/-!
# Minorized step counts and periods

A region carries a minorant at a set of step counts. Once the minorant charges
the region, that set is closed under addition. Under an invariant law that
charges the region, a common divisor of at least two of those counts splits the
space into a measurable cycle, so an aperiodic kernel is minorized on the region
at every large enough count.
-/

namespace Problib.Measure.Kernel

open Problib.Real

universe u
variable {α : Type u} {space : Space α}

/-- The region is minorized by the law after `steps` steps, at some weight. -/
@[expose] public def MinorizedAt (kernel : Kernel space space) (region : Set α)
    (minorant : Giry.Law space) (steps : Nat) : Prop :=
  ∃ weight, MinorizationOn kernel region steps weight minorant

/-! ### Integral bounds -/

/-- A probability measure that leaves a measurable set null charges its
complement fully. -/
private theorem full_of_complement_null {measure : Measure space}
    (probability : Measure.IsProbability measure) {region : Set α}
    (null : measure (Set.complement region) = ENNReal.zero) :
    measure region = ENNReal.one := by
  apply ENNReal.le_antisymm (probability.apply_le_one region)
  have whole := measure.union_le region (Set.complement region)
  have covers : Set.union region (Set.complement region) = Set.univ := by
    funext value
    apply propext
    exact ⟨fun _ => trivial, fun _ => Classical.em (region value)⟩
  rw [covers, probability.univ_eq_one, null, ENNReal.add_zero] at whole
  exact whole

private theorem MinorizationOn.lintegral_lower {kernel : Kernel space space}
    {region : Set α} {steps : Nat} {weight : NNReal} {minorant : Giry.Law space}
    (minor : MinorizationOn kernel region steps weight minorant)
    {input : α} (member : region input) (function : α → ENNReal) :
    ENNReal.le
      (ENNReal.mul (ENNReal.finite weight) (lintegral minorant.val function))
      (lintegral (iterate kernel steps input) function) := by
  have bound := lintegral_mono_measure function
    (Measure.smul (ENNReal.finite weight) minorant.val)
    (iterate kernel steps input) (minor.lower input member)
  rw [lintegral_smul_measure] at bound
  exact bound

/-- A lower bound at a weight on an inhabited region is a minorization: the
weight is at most one because the iterate is a probability. -/
private theorem minorizedAt_of_lower {kernel : Kernel space space}
    {region : Set α} {minorant : Giry.Law space} {steps : Nat} {weight : NNReal}
    (markov : ∀ input, Measure.IsProbability (kernel input))
    (stepsPositive : 0 < steps) (weightPositive : NNReal.lt NNReal.zero weight)
    (inhabited : ∃ input, region input)
    (lower : ∀ input, region input → ∀ event, space.Measurable event →
      ENNReal.le (ENNReal.mul (ENNReal.finite weight) (minorant.val event))
        (iterate kernel steps input event)) :
    MinorizedAt kernel region minorant steps := by
  rcases inhabited with ⟨point, member⟩
  have whole := lower point member Set.univ space.univ
  rw [minorant.property.univ_eq_one, ENNReal.mul_one,
    (iterate_isProbability kernel markov steps point).univ_eq_one] at whole
  refine ⟨weight, markov, stepsPositive, weightPositive, whole, ?_⟩
  intro input inside event measurable
  rw [Measure.smul_apply_measurable _ _ measurable]
  exact lower input inside event measurable

private theorem finite_of_probability {measure : Measure space}
    (probability : Measure.IsProbability measure) (region : Set α) :
    ∃ mass, measure region = ENNReal.finite mass ∧ NNReal.le mass NNReal.one := by
  have bounded := probability.apply_le_one region
  rcases ENNReal.exists_finite_of_finite
      (ENNReal.finite_of_le bounded True.intro) with ⟨mass, equal⟩
  refine ⟨mass, equal, ?_⟩
  rw [equal] at bounded
  exact bounded

/-! ### Additivity -/

/-- Minorized counts add once the minorant charges the region. -/
public theorem minorizedAt_add {kernel : Kernel space space} {region : Set α}
    {minorant : Giry.Law space} {first second : Nat}
    (measurable : space.Measurable region)
    (selfCharge : ENNReal.lt ENNReal.zero (minorant.val region))
    (left : MinorizedAt kernel region minorant first)
    (right : MinorizedAt kernel region minorant second) :
    MinorizedAt kernel region minorant (first + second) := by
  rcases left with ⟨firstWeight, firstMinor⟩
  rcases right with ⟨secondWeight, secondMinor⟩
  rcases finite_of_probability minorant.property region with
    ⟨charge, chargeEqual, _⟩
  have chargePositive : NNReal.lt NNReal.zero charge := by
    rw [chargeEqual] at selfCharge
    exact selfCharge
  apply minorizedAt_of_lower (weight := NNReal.mul
      (NNReal.mul firstWeight secondWeight) charge) firstMinor.markov
    (Nat.lt_of_lt_of_le firstMinor.stepsPositive (Nat.le_add_right _ _))
    (NNReal.mul_positive (NNReal.mul_positive firstMinor.weightPositive
      secondMinor.weightPositive) chargePositive)
    (Measure.exists_mem_of_positive minorant.val selfCharge)
  intro input member event eventMeasurable
  have inner : ∀ value, region value → ENNReal.le
      (ENNReal.mul (ENNReal.finite secondWeight) (minorant.val event))
      (iterate kernel second value event) := by
    intro value inside
    have bound := secondMinor.lower value inside event eventMeasurable
    rw [Measure.smul_apply_measurable _ _ eventMeasurable] at bound
    exact bound
  have middle := lintegral_lower_on minorant.val measurable inner
  have outer := firstMinor.lintegral_lower member
    (fun value => iterate kernel second value event)
  rw [iterate_add, comp_apply_measurable _ _ _ eventMeasurable]
  refine ENNReal.le_trans ?_ outer
  have arranged : ENNReal.mul
      (ENNReal.finite (NNReal.mul (NNReal.mul firstWeight secondWeight) charge))
      (minorant.val event) =
      ENNReal.mul (ENNReal.finite firstWeight)
        (ENNReal.mul (ENNReal.mul (ENNReal.finite secondWeight)
          (minorant.val event)) (minorant.val region)) := by
    rw [chargeEqual, ← ENNReal.finite_mul_finite, ← ENNReal.finite_mul_finite,
      ENNReal.mul_assoc, ENNReal.mul_assoc, ENNReal.mul_assoc,
      ENNReal.mul_comm (ENNReal.finite charge)]
  rw [arranged]
  exact ENNReal.mul_le_mul_left middle _

/-! ### Cycles from a common divisor -/

/-- States from which the region is charged after `count` steps. -/
private def charges (kernel : Kernel space space) (region : Set α)
    (count : Nat) : Set α :=
  fun input => ENNReal.lt ENNReal.zero (iterate kernel count input region)

private theorem charges_measurable (kernel : Kernel space space)
    {region : Set α} (measurable : space.Measurable region) (count : Nat) :
    space.Measurable (charges kernel region count) :=
  (iterate kernel count).measurable measurable ENNReal.zero

private theorem guard_measurable (condition : Prop) {region : Set α}
    (measurable : space.Measurable region) :
    space.Measurable (fun input => condition ∧ region input) := by
  classical
  by_cases holds : condition
  · have same : (fun input => condition ∧ region input) = region := by
      funext input
      apply propext
      exact ⟨fun both => both.2, fun inside => ⟨holds, inside⟩⟩
    rw [same]
    exact measurable
  · have same : (fun input => condition ∧ region input) = Set.empty := by
      funext input
      apply propext
      exact ⟨fun both => holds both.1, fun absent => absent.elim⟩
    rw [same]
    exact space.empty

/-- States that charge the region at some count `c` with `divisor ∣ c + residue`. -/
private def residueCell (kernel : Kernel space space) (region : Set α)
    (divisor residue : Nat) : Set α :=
  Set.iUnion fun count => fun input =>
    divisor ∣ count + residue ∧ charges kernel region count input

private theorem residueCell_measurable (kernel : Kernel space space)
    {region : Set α} (measurable : space.Measurable region)
    (divisor residue : Nat) :
    space.Measurable (residueCell kernel region divisor residue) :=
  space.iUnion fun count =>
    guard_measurable _ (charges_measurable kernel measurable count)

/-- Two counts are coherent when one offset makes both divisible. -/
private def Coherent (divisor first second : Nat) : Prop :=
  ∃ offset, divisor ∣ offset + first ∧ divisor ∣ offset + second

/-- States that charge the region at two incoherent counts. -/
private def overlap (kernel : Kernel space space) (region : Set α)
    (divisor : Nat) : Set α :=
  Set.iUnion fun first => Set.iUnion fun second => fun input =>
    ¬Coherent divisor first second ∧
      Set.inter (charges kernel region first) (charges kernel region second)
        input

private theorem overlap_measurable (kernel : Kernel space space)
    {region : Set α} (measurable : space.Measurable region) (divisor : Nat) :
    space.Measurable (overlap kernel region divisor) :=
  space.iUnion fun first => space.iUnion fun second =>
    guard_measurable _ (space.inter (charges_measurable kernel measurable first)
      (charges_measurable kernel measurable second))

/-- States from which the overlap is never charged. -/
private def avoids (kernel : Kernel space space) (region : Set α)
    (divisor : Nat) : Set α :=
  Set.complement (Set.iUnion
    (charges kernel (overlap kernel region divisor)))

private theorem avoids_measurable (kernel : Kernel space space)
    {region : Set α} (measurable : space.Measurable region) (divisor : Nat) :
    space.Measurable (avoids kernel region divisor) :=
  space.complement (space.iUnion
    (charges_measurable kernel (overlap_measurable kernel measurable divisor)))

private theorem residue_eq {divisor count first second : Nat}
    (firstDivides : divisor ∣ count + first)
    (secondDivides : divisor ∣ count + second)
    (firstSmall : first < divisor) (secondSmall : second < divisor) :
    first = second := by
  have oneWay : ∀ {lower upper : Nat}, divisor ∣ count + lower →
      divisor ∣ count + upper → upper < divisor → lower ≤ upper →
        upper - lower = 0 := by
    intro lower upper lowerDivides upperDivides upperSmall ordered
    have difference := Nat.dvd_sub upperDivides lowerDivides
    rw [show count + upper - (count + lower) = upper - lower by omega]
      at difference
    exact Nat.eq_zero_of_dvd_of_lt difference (by omega)
  rcases Nat.le_total first second with ordered | ordered
  · have := oneWay firstDivides secondDivides secondSmall ordered
    omega
  · have := oneWay secondDivides firstDivides firstSmall ordered
    omega

private theorem exists_residue {divisor : Nat} (positive : 0 < divisor)
    (count : Nat) : ∃ residue, residue < divisor ∧ divisor ∣ count + residue := by
  induction count with
  | zero => exact ⟨0, positive, Nat.dvd_zero divisor⟩
  | succ count induction =>
      rcases induction with ⟨residue, small, divides⟩
      by_cases vanishes : residue = 0
      · refine ⟨divisor - 1, by omega, ?_⟩
        subst residue
        rw [show count + 1 + (divisor - 1) = count + 0 + divisor by omega]
        exact Nat.dvd_add divides (Nat.dvd_refl divisor)
      · refine ⟨residue - 1, by omega, ?_⟩
        rw [show count + 1 + (residue - 1) = count + residue by omega]
        exact divides

private theorem dvd_add_mod_iff {divisor count residue : Nat} :
    divisor ∣ count + residue % divisor ↔ divisor ∣ count + residue := by
  have split : count + residue =
      (count + residue % divisor) + divisor * (residue / divisor) := by
    have := Nat.mod_add_div residue divisor
    omega
  rw [split]
  exact (Nat.dvd_add_left (Nat.dvd_mul_right divisor _)).symm

section Cycle

variable {kernel : Kernel space space} {law : Giry.Law space}
  {region : Set α} {steps : Nat} {weight : NNReal} {minorant : Giry.Law space}

/-- A count past a charged hub and back into the region is minorized. -/
private theorem minorizedAt_through
    (minor : MinorizationOn kernel region steps weight minorant)
    (measurable : space.Measurable region) (inhabited : ∃ input, region input)
    {hub : Set α} {reach : Nat}
    (reached : ENNReal.lt ENNReal.zero
      (minorant.val.bind (iterate kernel (reach + 1)) hub))
    {count : Nat} (charged : ∀ input, hub input →
      charges kernel region count input) :
    MinorizedAt kernel region minorant (steps + (reach + 1) + count + steps) := by
  let markov := minor.markov
  let spread := minorant.val.bind (iterate kernel (reach + 1))
  have spreadProbability : Measure.IsProbability spread :=
    minorant.property.bind _ (iterate_isProbability kernel markov (reach + 1))
  let returns : α → ENNReal := fun input => iterate kernel count input region
  have returnsMeasurable : ENNRealMeasurable space returns :=
    (iterate kernel count).measurable measurable
  have mass := lintegral_positive spread reached returnsMeasurable charged
  have massBounded : ENNReal.le (lintegral spread returns) ENNReal.one := by
    have bound := lintegral_mono spread (fun input =>
      (iterate_isProbability kernel markov count input).apply_le_one region)
    rw [lintegral_const, spreadProbability.univ_eq_one, ENNReal.one_mul] at bound
    exact bound
  rcases ENNReal.exists_finite_of_finite
      (ENNReal.finite_of_le massBounded True.intro) with ⟨total, totalEqual⟩
  have totalPositive : NNReal.lt NNReal.zero total := by
    rw [totalEqual] at mass
    exact mass
  apply minorizedAt_of_lower
    (weight := NNReal.mul (NNReal.mul weight weight) total) markov
    (by have := minor.stepsPositive; omega)
    (NNReal.mul_positive (NNReal.mul_positive minor.weightPositive
      minor.weightPositive) totalPositive) inhabited
  intro input member event eventMeasurable
  -- Back into the region, the last `steps` steps give weight times the event.
  have entry : ∀ value, ENNReal.le
      (ENNReal.mul (ENNReal.mul (ENNReal.finite weight) (minorant.val event))
        (returns value))
      (iterate kernel (count + steps) value event) := by
    intro value
    have inner : ∀ state, region state → ENNReal.le
        (ENNReal.mul (ENNReal.finite weight) (minorant.val event))
        (iterate kernel steps state event) := by
      intro state inside
      have bound := minor.lower state inside event eventMeasurable
      rw [Measure.smul_apply_measurable _ _ eventMeasurable] at bound
      exact bound
    rw [iterate_add, comp_apply_measurable _ _ _ eventMeasurable]
    exact lintegral_lower_on (iterate kernel count value) measurable inner
  -- Through the hub, the spread law carries the return mass.
  have through : ENNReal.le
      (ENNReal.mul (ENNReal.mul (ENNReal.finite weight) (minorant.val event))
        (lintegral spread returns))
      (minorant.val.bind (iterate kernel ((reach + 1) + (count + steps))) event) := by
    rw [iterate_add, ← Measure.bind_assoc, Measure.bind_apply _ _ eventMeasurable,
      ← lintegral_smul spread _ returnsMeasurable]
    exact lintegral_mono spread entry
  have outer := minor.lintegral_lower member
    (fun value => iterate kernel ((reach + 1) + (count + steps)) value event)
  rw [← Measure.bind_apply _ _ eventMeasurable] at outer
  rw [show steps + (reach + 1) + count + steps =
      steps + ((reach + 1) + (count + steps)) by omega,
    iterate_add, comp_apply_measurable _ _ _ eventMeasurable]
  refine ENNReal.le_trans ?_ outer
  have arranged : ENNReal.mul
      (ENNReal.finite (NNReal.mul (NNReal.mul weight weight) total))
      (minorant.val event) =
      ENNReal.mul (ENNReal.finite weight)
        (ENNReal.mul (ENNReal.mul (ENNReal.finite weight) (minorant.val event))
          (lintegral spread returns)) := by
    rw [totalEqual, ← ENNReal.finite_mul_finite, ← ENNReal.finite_mul_finite,
      ENNReal.mul_assoc, ENNReal.mul_assoc, ENNReal.mul_assoc,
      ENNReal.mul_comm (ENNReal.finite total)]
  rw [arranged]
  exact ENNReal.mul_le_mul_left through _

/-- Under a common divisor, incoherent counts are never charged together on a
set of positive invariant mass. -/
private theorem overlap_null
    (irreducible : MeasureIrreducible kernel law.val)
    (measurable : space.Measurable region) (inhabited : ∃ input, region input)
    (minor : MinorizationOn kernel region steps weight minorant)
    {divisor : Nat}
    (divides : ∀ count, MinorizedAt kernel region minorant count →
      divisor ∣ count) :
    law.val.NullSet (overlap kernel region divisor) := by
  apply Measure.NullSet.iUnion
  intro first
  apply Measure.NullSet.iUnion
  intro second
  let hub := Set.inter (charges kernel region first) (charges kernel region second)
  have hubMeasurable : space.Measurable hub :=
    space.inter (charges_measurable kernel measurable first)
      (charges_measurable kernel measurable second)
  apply Classical.byContradiction
  intro charged
  have hubPositive : ENNReal.lt ENNReal.zero (law.val hub) := by
    apply ENNReal.zero_lt_iff_ne_zero.mpr
    intro vanished
    exact charged (Measure.NullSet.mono vanished (fun {_} member => member.2))
  rcases irreducible.reaches_from minor.markov minorant hubMeasurable hubPositive
    with ⟨reach, reached⟩
  have firstCount := divides _ (minorizedAt_through minor measurable inhabited
    reached (fun _ member => member.1))
  have secondCount := divides _ (minorizedAt_through minor measurable inhabited
    reached (fun _ member => member.2))
  have coherent : Coherent divisor first second := by
    refine ⟨steps + (reach + 1) + steps, ?_, ?_⟩
    · rw [show steps + (reach + 1) + steps + first =
          steps + (reach + 1) + first + steps by omega]
      exact firstCount
    · rw [show steps + (reach + 1) + steps + second =
          steps + (reach + 1) + second + steps by omega]
      exact secondCount
  apply charged
  apply (law.val.null_empty).mono
  intro input member
  exact member.1 coherent

private theorem not_mem_overlap_of_avoids
    {region : Set α} (measurable : space.Measurable region) {divisor : Nat}
    {input : α} (member : avoids kernel region divisor input) :
    ¬overlap kernel region divisor input := by
  intro inside
  apply member
  refine ⟨0, ?_⟩
  change ENNReal.lt ENNReal.zero
    (iterate kernel 0 input (overlap kernel region divisor))
  rw [iterate_zero, Kernel.deterministic_apply,
    Measure.dirac_apply_of_mem space input
      (overlap_measurable kernel measurable divisor) inside]
  exact ENNReal.zero_lt_iff_ne_zero.mpr ENNReal.one_ne_zero

/-- A state charges the region one step later than the states it reaches. -/
private theorem charges_succ {target : Set α}
    (measurable : space.Measurable target) {count : Nat} {input : α}
    (reached : ENNReal.lt ENNReal.zero
      (kernel input (charges kernel target count))) :
    charges kernel target (1 + count) input := by
  change ENNReal.lt ENNReal.zero (iterate kernel (1 + count) input target)
  rw [iterate_add, comp_apply_measurable _ _ _ measurable, iterate_one]
  exact lintegral_positive (kernel input) reached
    ((iterate kernel count).measurable measurable) (fun _ member => member)

/-- From a state that avoids the overlap, the next state avoids it surely. -/
private theorem avoids_absorbing (measurable : space.Measurable region)
    {divisor : Nat} {input : α} (member : avoids kernel region divisor input) :
    kernel input (Set.complement (avoids kernel region divisor)) =
      ENNReal.zero := by
  have null : (kernel input).NullSet
      (Set.iUnion (charges kernel (overlap kernel region divisor))) := by
    apply Measure.NullSet.iUnion
    intro count
    apply Classical.byContradiction
    intro charged
    apply member
    exact ⟨1 + count, charges_succ (overlap_measurable kernel measurable divisor)
      (ENNReal.zero_lt_iff_ne_zero.mpr charged)⟩
  exact Measure.NullSet.mono null (fun {_} outside =>
    Classical.byContradiction outside)

private theorem avoids_full
    (invariant : law.val.bind kernel = law.val)
    (irreducible : MeasureIrreducible kernel law.val)
    (measurable : space.Measurable region) (inhabited : ∃ input, region input)
    (minor : MinorizationOn kernel region steps weight minorant)
    {divisor : Nat}
    (divides : ∀ count, MinorizedAt kernel region minorant count →
      divisor ∣ count) :
    law.val (avoids kernel region divisor) = ENNReal.one := by
  have overlapNull := overlap_null irreducible measurable inhabited minor divides
  have null : law.val.NullSet
      (Set.iUnion (charges kernel (overlap kernel region divisor))) := by
    apply Measure.NullSet.iUnion
    intro count
    have integral : lintegral law.val (fun input =>
        iterate kernel count input (overlap kernel region divisor)) =
        ENNReal.zero := by
      rw [← Measure.bind_apply _ _ (overlap_measurable kernel measurable divisor),
        invariant_iterate kernel law invariant count]
      exact overlapNull
    exact positive_null_of_lintegral_zero law.val
      ((iterate kernel count).measurable (overlap_measurable kernel measurable divisor))
      integral
  apply full_of_complement_null law.property
  exact Measure.NullSet.mono null (fun {_} outside =>
    Classical.byContradiction outside)

/-- The cycle cells: residue cells restricted to the avoiding states. -/
private def cycleCell (kernel : Kernel space space) (region : Set α)
    (divisor residue : Nat) : Set α :=
  Set.inter (residueCell kernel region divisor residue) (avoids kernel region divisor)

private theorem covered
    (irreducible : MeasureIrreducible kernel law.val)
    (measurable : space.Measurable region)
    (positive : ENNReal.lt ENNReal.zero (law.val region))
    {divisor : Nat} (divisorPositive : 0 < divisor) (input : α) :
    ∃ residue, residue < divisor ∧
      residueCell kernel region divisor residue input := by
  rcases irreducible.reaches region measurable positive input with ⟨count, reached⟩
  rcases exists_residue divisorPositive (count + 1) with ⟨residue, small, divides⟩
  exact ⟨residue, small, count + 1, divides, reached⟩

private theorem cycleCell_disjoint (measurable : space.Measurable region)
    {divisor first second : Nat} (firstSmall : first < divisor)
    (secondSmall : second < divisor)
    {input : α} (firstMember : cycleCell kernel region divisor first input)
    (secondMember : cycleCell kernel region divisor second input) : first = second := by
  rcases firstMember with ⟨⟨firstCount, firstDivides, firstCharged⟩, avoiding⟩
  rcases secondMember with ⟨⟨secondCount, secondDivides, secondCharged⟩, _⟩
  have coherent : Coherent divisor firstCount secondCount := by
    apply Classical.byContradiction
    intro incoherent
    exact not_mem_overlap_of_avoids measurable avoiding
      ⟨firstCount, secondCount, incoherent, firstCharged, secondCharged⟩
  rcases coherent with ⟨offset, firstOffset, secondOffset⟩
  have shifted : divisor ∣ firstCount + second := by
    have sum := Nat.dvd_add firstOffset secondDivides
    rw [show offset + firstCount + (secondCount + second) =
        (offset + secondCount) + (firstCount + second) by omega] at sum
    exact (Nat.dvd_add_right secondOffset).mp sum
  exact residue_eq firstDivides shifted firstSmall secondSmall

private theorem cycleCell_advance
    (irreducible : MeasureIrreducible kernel law.val)
    (measurable : space.Measurable region)
    (positive : ENNReal.lt ENNReal.zero (law.val region))
    (markov : ∀ input, Measure.IsProbability (kernel input))
    {divisor : Nat} (divisorPositive : 0 < divisor) {residue : Nat}
    {input : α} (member : cycleCell kernel region divisor residue input) :
    kernel input (cycleCell kernel region divisor ((residue + 1) % divisor)) =
      ENNReal.one := by
  rcases member with ⟨⟨start, startDivides, startCharged⟩, avoiding⟩
  let next := (residue + 1) % divisor
  let stray : Set α := Set.iUnion fun count => fun state =>
    ¬divisor ∣ count + (residue + 1) ∧ charges kernel region count state
  have strayNull : (kernel input).NullSet stray := by
    apply Measure.NullSet.iUnion
    intro count
    by_cases aligned : divisor ∣ count + (residue + 1)
    · exact Measure.NullSet.mono ((kernel input).null_empty)
        (fun {_} member => member.1 aligned)
    apply Classical.byContradiction
    intro charged
    have later : charges kernel region (1 + count) input := by
      apply charges_succ measurable
      apply ENNReal.zero_lt_iff_ne_zero.mpr
      intro vanished
      exact charged (Measure.NullSet.mono vanished (fun {_} member => member.2))
    have coherent : Coherent divisor start (1 + count) := by
      apply Classical.byContradiction
      intro incoherent
      exact not_mem_overlap_of_avoids measurable avoiding
        ⟨start, 1 + count, incoherent, startCharged, later⟩
    rcases coherent with ⟨offset, startOffset, laterOffset⟩
    apply aligned
    have sum := Nat.dvd_add laterOffset startDivides
    rw [show offset + (1 + count) + (start + residue) =
        (offset + start) + (count + (residue + 1)) by omega] at sum
    exact (Nat.dvd_add_right startOffset).mp sum
  have escapeNull : (kernel input).NullSet
      (Set.complement (cycleCell kernel region divisor next)) := by
    have leaves := avoids_absorbing (kernel := kernel) measurable avoiding
    apply Measure.NullSet.mono (Measure.NullSet.union leaves strayNull)
    intro state outside
    by_cases staying : avoids kernel region divisor state
    · right
      rcases covered irreducible measurable positive divisorPositive state with
        ⟨_, _, count, _, charged⟩
      refine ⟨count, ?_, charged⟩
      intro aligned
      exact outside ⟨⟨count, dvd_add_mod_iff.mpr aligned, charged⟩, staying⟩
    · left
      exact staying
  exact full_of_complement_null (markov input) escapeNull

/-- Under an invariant law charging the region, a common divisor of at least two
of the minorized counts gives a measurable cycle of that period. -/
public theorem cycle_of_common_divisor
    (invariant : law.val.bind kernel = law.val)
    (irreducible : MeasureIrreducible kernel law.val)
    (measurable : space.Measurable region)
    (positive : ENNReal.lt ENNReal.zero (law.val region))
    (minor : MinorizationOn kernel region steps weight minorant)
    (divisor : Nat) (large : 2 ≤ divisor)
    (divides : ∀ count, MinorizedAt kernel region minorant count →
      divisor ∣ count) :
    ∃ cell, MeasureCycle kernel law.val divisor cell := by
  let markov := minor.markov
  have divisorPositive : 0 < divisor := by omega
  have inhabited := Measure.exists_mem_of_positive law.val positive
  let cell := cycleCell kernel region divisor
  have cellMeasurable : ∀ residue, space.Measurable (cell residue) := fun residue =>
    space.inter (residueCell_measurable kernel measurable divisor residue)
      (avoids_measurable kernel measurable divisor)
  have advance : ∀ residue input, cell residue input →
      kernel input (cell ((residue + 1) % divisor)) = ENNReal.one :=
    fun _ _ member => cycleCell_advance irreducible measurable positive markov
      divisorPositive member
  -- Some cell carries invariant mass.
  have somewhere : ∃ residue, ENNReal.lt ENNReal.zero
      (law.val (cell (residue % divisor))) := by
    apply Classical.byContradiction
    intro nowhere
    have null : law.val.NullSet
        (Set.iUnion fun residue => cell (residue % divisor)) := by
      apply Measure.NullSet.iUnion
      intro residue
      apply Classical.byContradiction
      intro charged
      exact nowhere ⟨residue, ENNReal.zero_lt_iff_ne_zero.mpr charged⟩
    have covers : Set.Subset (avoids kernel region divisor)
        (Set.iUnion fun residue => cell (residue % divisor)) := by
      intro state staying
      rcases covered irreducible measurable positive divisorPositive state with
        ⟨residue, small, inside⟩
      refine ⟨residue, ?_, staying⟩
      rw [Nat.mod_eq_of_lt small]
      exact inside
    have full := avoids_full invariant irreducible measurable inhabited minor divides
    have vanished : law.val (avoids kernel region divisor) = ENNReal.zero :=
      Measure.NullSet.mono null covers
    rw [full] at vanished
    exact ENNReal.one_ne_zero vanished
  rcases somewhere with ⟨origin, originPositive⟩
  -- Invariance carries mass from each cell to the next.
  have forward : ∀ residue, ENNReal.lt ENNReal.zero (law.val (cell residue)) →
      ENNReal.lt ENNReal.zero (law.val (cell ((residue + 1) % divisor))) := by
    intro residue charged
    have bound := lintegral_lower_on law.val (cellMeasurable residue)
      (function := fun input => kernel input (cell ((residue + 1) % divisor)))
      (bound := ENNReal.one)
      (fun input member => by
        rw [advance residue input member]
        exact ENNReal.le_refl _)
    rw [ENNReal.one_mul, ← Measure.bind_apply _ _ (cellMeasurable _),
      invariant] at bound
    apply ENNReal.zero_lt_iff_ne_zero.mpr
    intro vanished
    rw [vanished] at bound
    exact (ENNReal.zero_lt_iff_ne_zero.mp charged)
      (ENNReal.eq_zero_of_le_zero bound)
  have reached : ∀ count, ENNReal.lt ENNReal.zero
      (law.val (cell ((origin + count) % divisor))) := by
    intro count
    induction count with
    | zero => exact originPositive
    | succ count induction =>
        have step := forward _ induction
        rwa [Nat.mod_add_mod, Nat.add_assoc] at step
  refine ⟨cell, fun index _ => cellMeasurable index, ?_, ?_,
    fun index _ input member => advance index input member⟩
  · intro first second firstSmall secondSmall different input firstMember
      secondMember
    exact different (cycleCell_disjoint (kernel := kernel) measurable firstSmall
      secondSmall firstMember secondMember)
  · intro index small
    have enough : origin ≤ divisor * origin :=
      Nat.le_mul_of_pos_left origin divisorPositive
    have landed := reached (index + divisor * origin - origin)
    rw [show origin + (index + divisor * origin - origin) =
        index + divisor * origin by omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt small] at landed
    exact landed

/-- Under an invariant law charging the region, an aperiodic kernel whose
minorant charges the region is minorized there at every large enough count. -/
public theorem minorizedAt_eventually
    (invariant : law.val.bind kernel = law.val)
    (irreducible : MeasureIrreducible kernel law.val)
    (aperiodic : MeasureAperiodic kernel law.val)
    (measurable : space.Measurable region)
    (positive : ENNReal.lt ENNReal.zero (law.val region))
    (minor : MinorizationOn kernel region steps weight minorant)
    (selfCharge : ENNReal.lt ENNReal.zero (minorant.val region)) :
    ∃ threshold, ∀ count, threshold ≤ count →
      MinorizedAt kernel region minorant count := by
  let members : Nat → Prop := fun count =>
    count = 0 ∨ MinorizedAt kernel region minorant count
  have add : ∀ left right, members left → members right →
      members (left + right) := by
    rintro left right (rfl | leftMinor) (rfl | rightMinor)
    · exact Or.inl rfl
    · rw [Nat.zero_add]
      exact Or.inr rightMinor
    · exact Or.inr leftMinor
    · exact Or.inr (minorizedAt_add measurable selfCharge leftMinor rightMinor)
  have coprime : ∀ divisor : Nat,
      (∀ count, members count → divisor ∣ count) → divisor = 1 := by
    intro divisor divides
    have stepsDivisible := divides steps (Or.inr ⟨weight, minor⟩)
    have nonzero : divisor ≠ 0 := by
      intro vanished
      subst divisor
      have := Nat.eq_zero_of_zero_dvd stepsDivisible
      have := minor.stepsPositive
      omega
    apply Classical.byContradiction
    intro notOne
    rcases cycle_of_common_divisor invariant irreducible measurable positive minor
        divisor (by omega) (fun count minorized => divides count (Or.inr minorized))
      with ⟨cell, cycle⟩
    have := aperiodic divisor cell cycle
    omega
  rcases numerical_semigroup_eventually members steps minor.stepsPositive
      (Or.inr ⟨weight, minor⟩) (Or.inl rfl) add coprime with ⟨threshold, large⟩
  refine ⟨threshold + 1, fun count past => ?_⟩
  rcases large count (by omega) with vanished | minorized
  · omega
  · exact minorized

end Cycle

end Problib.Measure.Kernel
