import Problib.Measure.Kernel.Iteration.Finite
import Problib.Measure.Kernel.Iteration.Harris

set_option autoImplicit false

/-!
# Finite chain conditions and their measure forms

`Finite.lean` states irreducibility and aperiodicity through positive paths
between states. The Harris theorems state them through events and measurable
cycles. On an enumerated discrete space, a state every state reaches makes the
chain irreducible against the unit mass at that state
(`measureIrreducible_of_accessible`). If that state is also aperiodic, no
measurable cycle of period two or more exists against any reference
(`measureAperiodic_of_aperiodicAt`), and each invariant law makes the chain
positive Harris (`positiveHarris_of_accessible`). Conversely, an invariant law
that charges the state and admits no cycle makes the state aperiodic
(`aperiodicAt_of_measureAperiodic`): the states reached from it at each residue
of a common divisor of its return times form a cycle.
-/

namespace Problib.Measure.Kernel

open Problib.Real Problib.Probability

universe u
variable {α : Type u} [DecidableEq α]

omit [DecidableEq α] in
private theorem singleton_positive (point : α) :
    ENNReal.lt ENNReal.zero
      (Measure.dirac (Space.discrete α) point (Set.singleton point)) := by
  rw [Measure.dirac_apply_of_mem _ _ (Space.discrete_measurable _)
    (show Set.singleton point point from rfl)]
  exact ENNReal.one_positive

omit [DecidableEq α] in
private theorem lt_of_lt_of_le {low middle high : ENNReal}
    (first : ENNReal.lt low middle) (second : ENNReal.le middle high) :
    ENNReal.lt low high :=
  ⟨ENNReal.le_trans first.left second,
    fun reverse => first.right (ENNReal.le_trans second reverse)⟩

omit [DecidableEq α] in
/-- A probability that charges only states of an event gives it full mass. -/
private theorem full_of_successors
    (enumeration : List α) (listed : FiniteEnumeration enumeration)
    (measure : Measure (Space.discrete α))
    (probability : Measure.IsProbability measure) (event : Set α)
    (covers : ∀ point, ENNReal.lt ENNReal.zero (measure (Set.singleton point)) →
      event point) :
    measure event = ENNReal.one := by
  have restricted : measure.restrict (Set.complement event) =
      Measure.zero (Space.discrete α) := by
    apply finite_singletons_determine_measure enumeration listed
    intro point
    rw [Measure.restrict_apply _ _ (Space.discrete_measurable _), Measure.zero_apply]
    by_cases member : event point
    · have empty : Set.inter (Set.singleton point) (Set.complement event) =
          Set.empty := by
        apply Set.ext
        intro value
        constructor
        · rintro ⟨equal, outside⟩
          subst equal
          exact outside member
        · intro nothing
          exact False.elim nothing
      rw [empty, measure.empty_apply]
    · have zero : measure (Set.singleton point) = ENNReal.zero := by
        apply Classical.byContradiction
        intro nonzero
        exact member (covers point (ENNReal.zero_lt_iff_ne_zero.mpr nonzero))
      apply ENNReal.eq_zero_of_le_zero
      rw [← zero]
      exact Measure.mono measure (fun _ inside => inside.left)
  have outsideNull : measure (Set.complement event) = ENNReal.zero := by
    rw [← Measure.restrict_apply_univ, restricted, Measure.zero_apply]
  have complement := probability.apply_complement (Space.discrete_measurable event)
  rw [outsideNull] at complement
  exact ENNReal.le_antisymm (probability.apply_le_one event)
    (ENNReal.sub_eq_zero_iff_le.mp complement.symm)

/-- On an enumerated discrete space, a state every state reaches makes the chain
irreducible against the unit mass at that state. -/
theorem measureIrreducible_of_accessible
    (enumeration : List α) (listed : FiniteEnumeration enumeration)
    (kernel : Kernel (Space.discrete α) (Space.discrete α))
    (markov : ∀ input, Measure.IsProbability (kernel input))
    (target : α) (accessible : ∀ input, Reaches kernel input target) :
    MeasureIrreducible kernel (Measure.dirac (Space.discrete α) target) := by
  refine ⟨?_, ?_⟩
  · rw [Measure.dirac_apply_univ]
    exact ENNReal.one_positive
  · intro event measurable positive input
    have member : event target := by
      apply Classical.byContradiction
      intro outside
      rw [Measure.dirac_apply_of_not_mem _ _ measurable outside] at positive
      exact (ENNReal.zero_lt_iff_ne_zero.mp positive) rfl
    rcases probability_positive_singleton enumeration listed (kernel input)
        (markov input) with ⟨middle, firstPositive⟩
    rcases accessible middle with ⟨later, secondPositive⟩
    have onePositive : ENNReal.lt ENNReal.zero
        ((iterate kernel 1 input) (Set.singleton middle)) := by
      rw [iterate_one]
      exact firstPositive
    have path := positive_path_comp kernel input middle target 1 later
      onePositive secondPositive
    refine ⟨later, ?_⟩
    rw [Nat.add_comm later 1]
    exact lt_of_lt_of_le path (Measure.mono _ (fun value equal => by
      subst equal
      exact member))

private theorem mod_of_lt_double {value divisor : Nat} (small : value < divisor + divisor) :
    (value % divisor = value ∧ value < divisor) ∨
      (value % divisor = value - divisor ∧ divisor ≤ value) := by
  by_cases low : value < divisor
  · exact Or.inl ⟨Nat.mod_eq_of_lt low, low⟩
  · right
    refine ⟨?_, by omega⟩
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

private theorem dvd_of_mod_shift {divisor residue steps : Nat} (small : residue < divisor)
    (same : (residue + steps) % divisor = residue) : divisor ∣ steps := by
  have split := Nat.add_mod residue steps divisor
  rw [Nat.mod_eq_of_lt small] at split
  have stepsSmall : steps % divisor < divisor := Nat.mod_lt _ (by omega)
  apply Nat.dvd_of_mod_eq_zero
  rcases mod_of_lt_double (value := residue + steps % divisor) (divisor := divisor)
    (by omega) with low | high <;> omega

omit [DecidableEq α] in
/-- On a discrete space, a state every state reaches and that is aperiodic rules
out every measurable cycle of period two or more, against any reference.
Accessibility is needed: without it a two-cycle away from the state is a cycle
its return times never see. -/
theorem measureAperiodic_of_aperiodicAt
    (kernel : Kernel (Space.discrete α) (Space.discrete α))
    (markov : ∀ input, Measure.IsProbability (kernel input))
    {target : α} (accessible : ∀ input, Reaches kernel input target)
    (aperiodic : AperiodicAt kernel target) (reference : Measure (Space.discrete α)) :
    MeasureAperiodic kernel reference := by
  intro period cell cycle
  apply Classical.byContradiction
  intro tooLong
  have periodPositive : 0 < period := by omega
  -- A state the chain occupies surely after `count` steps lies in that cell.
  have landed : ∀ index count input, index < period → cell index input →
      ENNReal.lt ENNReal.zero (iterate kernel count input (Set.singleton target)) →
      cell ((index + count) % period) target := by
    intro index count input small member positive
    apply Classical.byContradiction
    intro outside
    have full := cycle.iterate_advance markov index small input member count
    have complement := (iterate_isProbability kernel markov count input).apply_complement
      (cycle.measurable ((index + count) % period) (Nat.mod_lt _ periodPositive))
    rw [full, ENNReal.sub_self] at complement
    have below := Measure.mono (iterate kernel count input)
      (left := Set.singleton target)
      (right := Set.complement (cell ((index + count) % period)))
      (fun value equal => by
        subst equal
        exact outside)
    rw [complement] at below
    exact positive.right below
  rcases Measure.exists_mem_of_positive reference (cycle.positive 0 periodPositive) with
    ⟨start, startMember⟩
  rcases accessible start with ⟨entry, entryPositive⟩
  have home := landed 0 entry start periodPositive startMember entryPositive
  have residueSmall : (0 + entry) % period < period := Nat.mod_lt _ periodPositive
  have divides : ∀ steps, ENNReal.lt ENNReal.zero
      ((iterate kernel steps target) (Set.singleton target)) → period ∣ steps := by
    intro steps positive
    have next := landed _ steps target residueSmall home positive
    apply dvd_of_mod_shift residueSmall
    apply Classical.byContradiction
    intro different
    exact cycle.disjoint _ _ (Nat.mod_lt _ periodPositive) residueSmall different target
      next home
  have one := aperiodic period divides
  omega

/-- The states the chain reaches from `target` at a number of steps with the
given residue. -/
private def returnCell (kernel : Kernel (Space.discrete α) (Space.discrete α))
    (target : α) (divisor index : Nat) : Set α := fun state =>
  ∃ steps, steps % divisor = index ∧
    ENNReal.lt ENNReal.zero ((iterate kernel steps target) (Set.singleton state))

private theorem returnCell_advance
    (enumeration : List α) (listed : FiniteEnumeration enumeration)
    (kernel : Kernel (Space.discrete α) (Space.discrete α))
    (markov : ∀ input, Measure.IsProbability (kernel input))
    (target : α) {divisor index : Nat} (large : 2 ≤ divisor) {input : α}
    (member : returnCell kernel target divisor index input) :
    kernel input (returnCell kernel target divisor ((index + 1) % divisor)) =
      ENNReal.one := by
  rcases member with ⟨steps, stepsMod, reached⟩
  apply full_of_successors enumeration listed (kernel input) (markov input)
  intro next positive
  refine ⟨steps + 1, ?_, ?_⟩
  · rw [← stepsMod, Nat.add_mod steps 1 divisor,
      Nat.mod_eq_of_lt (show 1 < divisor by omega)]
  · have once : ENNReal.lt ENNReal.zero
        ((iterate kernel 1 input) (Set.singleton next)) := by
      rw [iterate_one]
      exact positive
    exact positive_path_comp kernel target input next steps 1 reached once

private theorem returnCell_disjoint
    (kernel : Kernel (Space.discrete α) (Space.discrete α))
    {target : α} (accessible : ∀ input, Reaches kernel input target)
    {divisor : Nat} (divisorPositive : 0 < divisor)
    (divides : ∀ steps, ENNReal.lt ENNReal.zero
      ((iterate kernel steps target) (Set.singleton target)) → divisor ∣ steps)
    {first second : Nat} {state : α}
    (inFirst : returnCell kernel target divisor first state)
    (inSecond : returnCell kernel target divisor second state) :
    first = second := by
  rcases inFirst with ⟨before, beforeMod, beforeReached⟩
  rcases inSecond with ⟨after, afterMod, afterReached⟩
  rcases accessible state with ⟨back, backReached⟩
  have beforeZero := Nat.mod_eq_zero_of_dvd (divides _
    (positive_path_comp kernel target state target before back beforeReached backReached))
  have afterZero := Nat.mod_eq_zero_of_dvd (divides _
    (positive_path_comp kernel target state target after back afterReached backReached))
  rw [Nat.add_mod] at beforeZero afterZero
  have backSmall := Nat.mod_lt back divisorPositive
  have beforeSmall := Nat.mod_lt before divisorPositive
  have afterSmall := Nat.mod_lt after divisorPositive
  rcases mod_of_lt_double (value := before % divisor + back % divisor)
    (divisor := divisor) (by omega) with beforeLow | beforeHigh <;>
  rcases mod_of_lt_double (value := after % divisor + back % divisor)
    (divisor := divisor) (by omega) with afterLow | afterHigh <;> omega

private theorem returnCell_positive
    (enumeration : List α) (listed : FiniteEnumeration enumeration)
    (kernel : Kernel (Space.discrete α) (Space.discrete α))
    (markov : ∀ input, Measure.IsProbability (kernel input))
    (target : α) (law : Giry.Law (Space.discrete α))
    (invariant : law.val.bind kernel = law.val)
    (positive : ENNReal.lt ENNReal.zero (law.val (Set.singleton target)))
    {divisor : Nat} (large : 2 ≤ divisor) :
    ∀ index, index < divisor →
      ENNReal.lt ENNReal.zero (law.val (returnCell kernel target divisor index)) := by
  intro index
  induction index with
  | zero =>
      intro _
      apply lt_of_lt_of_le positive
      apply Measure.mono
      intro state equal
      subst equal
      refine ⟨0, Nat.zero_mod _, ?_⟩
      rw [iterate_zero]
      exact singleton_positive _
  | succ index induction =>
      intro small
      apply lt_of_lt_of_le (induction (by omega))
      have measurable := Space.discrete_measurable
        (returnCell kernel target divisor (index + 1))
      conv => rhs; rw [← invariant, Measure.bind_apply _ _ measurable]
      rw [apply_eq_lintegral_indicator law.val (Space.discrete_measurable _)]
      apply lintegral_mono
      intro state
      by_cases member : returnCell kernel target divisor index state
      · rw [ennrealIndicator, ennrealPiecewise, ite_eq_left member]
        have full := returnCell_advance enumeration listed kernel markov target large member
        rw [Nat.mod_eq_of_lt small] at full
        rw [full]
        exact ENNReal.le_refl _
      · rw [ennrealIndicator, ennrealPiecewise, ite_eq_right member]
        exact ENNReal.zero_le _

/-- On an enumerated discrete space, if every state reaches `target`, an
invariant law that charges `target` and admits no measurable cycle makes
`target` aperiodic. A common divisor of two or more of its return times would
sort the states reached from it by residue into such a cycle. -/
theorem aperiodicAt_of_measureAperiodic
    (enumeration : List α) (listed : FiniteEnumeration enumeration)
    (kernel : Kernel (Space.discrete α) (Space.discrete α))
    (markov : ∀ input, Measure.IsProbability (kernel input))
    {target : α} (accessible : ∀ input, Reaches kernel input target)
    (law : Giry.Law (Space.discrete α)) (invariant : law.val.bind kernel = law.val)
    (positive : ENNReal.lt ENNReal.zero (law.val (Set.singleton target)))
    (aperiodic : MeasureAperiodic kernel law.val) :
    AperiodicAt kernel target := by
  intro divisor divides
  rcases (measureIrreducible_of_accessible enumeration listed kernel markov target
      accessible).reaches _ (Space.discrete_measurable _) (singleton_positive target)
      target with ⟨count, returned⟩
  have returnDivides := divides (count + 1) returned
  by_cases large : 2 ≤ divisor
  · exfalso
    have cycle : MeasureCycle kernel law.val divisor (returnCell kernel target divisor) :=
      ⟨fun _ _ => Space.discrete_measurable _,
        fun _ _ _ _ different _ inFirst inSecond => different
          (returnCell_disjoint kernel accessible (by omega) divides inFirst inSecond),
        returnCell_positive enumeration listed kernel markov target law invariant
          positive large,
        fun _ _ _ member =>
          returnCell_advance enumeration listed kernel markov target large member⟩
    have short := aperiodic divisor _ cycle
    omega
  · have nonzero : divisor ≠ 0 := by
      intro zero
      subst zero
      have vanished := Nat.eq_zero_of_zero_dvd returnDivides
      omega
    omega

/-- On an enumerated discrete space, a state every state reaches and that is
aperiodic makes the chain positive Harris for each of its invariant laws. -/
theorem positiveHarris_of_accessible
    (enumeration : List α) (listed : FiniteEnumeration enumeration)
    (kernel : Kernel (Space.discrete α) (Space.discrete α))
    (markov : ∀ input, Measure.IsProbability (kernel input))
    (target : α) (accessible : ∀ input, Reaches kernel input target)
    (aperiodic : AperiodicAt kernel target)
    (law : Giry.Law (Space.discrete α)) (invariant : law.val.bind kernel = law.val) :
    PositiveHarris kernel law := by
  rcases finite_accessible_aperiodic_minorization enumeration listed kernel markov target
      accessible aperiodic with ⟨_, _, _, minor⟩
  exact ⟨markov, invariant, harrisRecurrent_of_minorization minor law invariant⟩

end Problib.Measure.Kernel
