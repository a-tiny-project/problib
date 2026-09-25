module

public import Problib.Measure.Kernel.Iteration.Hitting
public import Problib.Measure.Integral.Lebesgue.Zero

set_option autoImplicit false

namespace Problib.Measure.Kernel

open Problib.Real

universe u
variable {α : Type u} {space : Space α}

/-- Every reference-positive event is reachable in positive time from every state. -/
public structure MeasureIrreducible (kernel : Kernel space space)
    (reference : Measure space) : Prop where
  nonzero : ENNReal.lt ENNReal.zero (reference Set.univ)
  reaches : ∀ event, space.Measurable event →
    ENNReal.lt ENNReal.zero (reference event) → ∀ input, ∃ count,
      ENNReal.lt ENNReal.zero (iterate kernel (count + 1) input event)

public theorem MeasureIrreducible.mono {kernel : Kernel space space}
    {reference smaller : Measure space}
    (irreducible : MeasureIrreducible kernel reference)
    (nonzero : ENNReal.lt ENNReal.zero (smaller Set.univ))
    (charged : ∀ event, space.Measurable event →
      ENNReal.lt ENNReal.zero (smaller event) →
        ENNReal.lt ENNReal.zero (reference event)) :
    MeasureIrreducible kernel smaller :=
  ⟨nonzero, fun event measurable positive input =>
    irreducible.reaches event measurable (charged event measurable positive) input⟩

public theorem MeasureIrreducible.reaches_from
    {kernel : Kernel space space} {reference : Measure space}
    {event : Set α}
    (_markov : ∀ input, Measure.IsProbability (kernel input))
    (irreducible : MeasureIrreducible kernel reference)
    (start : Giry.Law space) (measurable : space.Measurable event)
    (positive : ENNReal.lt ENNReal.zero (reference event)) :
    ∃ count, ENNReal.lt ENNReal.zero
      (start.val.bind (iterate kernel (count + 1)) event) := by
  have reaches : ∀ input, ∃ count,
      ENNReal.lt ENNReal.zero (iterate kernel (count + 1) input event) :=
    irreducible.reaches event measurable positive
  -- If every bind mass vanishes, lintegral_eq_zero_iff makes each
  -- measurable iterate-event function zero start-a.e. Countable AE
  -- intersection then contradicts reaches and start.property.univ_eq_one.
  apply Classical.byContradiction
  intro absent
  have absentCount : ∀ count, ¬ ENNReal.lt ENNReal.zero
      (start.val.bind (iterate kernel (count + 1)) event) := by
    intro count reached
    exact absent ⟨count, reached⟩
  have zeroIntegral : ∀ count,
      lintegral start.val (fun input => iterate kernel (count + 1) input event) =
        ENNReal.zero := by
    intro count
    have bind := Measure.bind_apply start.val (iterate kernel (count + 1)) measurable
    rw [← bind]
    exact Classical.byContradiction (fun nonzero =>
      absentCount count (ENNReal.zero_lt_iff_ne_zero.mpr nonzero))
  have zeroAE : ∀ count, start.val.AE (fun input =>
      iterate kernel (count + 1) input event = ENNReal.zero) := by
    intro count
    exact (lintegral_eq_zero_iff
      ((iterate kernel (count + 1)).measurable measurable)).mp
        (zeroIntegral count)
  have allZero := Measure.ae_all_iff.mpr zeroAE
  have impossible : start.val.AE (fun _ => False) :=
    allZero.mono (fun input all => by
      rcases reaches input with ⟨count, positiveAtCount⟩
      exact (ENNReal.zero_lt_iff_ne_zero.mp positiveAtCount) (all count))
  have emptyMass : start.val Set.univ = ENNReal.zero := by
    have same : Set.complement (fun _ : α => False) = Set.univ := by
      funext input
      apply propext
      constructor
      · intro _
        trivial
      · intro _ absent
        exact absent.elim
    exact same ▸ impossible
  rw [start.property.univ_eq_one] at emptyMass
  exact ENNReal.one_ne_zero emptyMass

end Problib.Measure.Kernel
