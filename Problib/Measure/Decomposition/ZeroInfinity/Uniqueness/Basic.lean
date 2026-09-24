module

public import Problib.Measure.Decomposition.ZeroInfinity.Properties
public import Problib.Measure.AlmostEverywhere.Transport

/-!
# Almost-everywhere-infinity equality

This module defines the almost-everywhere-infinity equivalence relation for
extended-nonnegative functions over a greatest zero-infinity certificate.
The relation requires ordinary almost-everywhere equality outside the greatest
zero-infinity set and almost-everywhere agreement on zero versus nonzero values
inside it.
-/

set_option autoImplicit false

namespace Problib.Measure.Measure

open Problib.Real

universe u

variable {alpha : Type u} {space : Space alpha}

/-- Almost-everywhere-infinity equality requires ordinary almost-everywhere
equality outside a greatest zero-infinity set and almost-everywhere agreement
on zero versus nonzero values inside it. -/
@[expose] public def TopZeroInfinitySet.AEInfinityEq {measure : Measure space}
    (top : TopZeroInfinitySet measure)
    (left right : alpha → ENNReal) : Prop :=
  (measure.restrict (Set.complement top.set)).AEEq left right ∧
  (measure.restrict top.set).AE (fun value => left value = ENNReal.zero ↔ right value = ENNReal.zero)

/-- Almost-everywhere-infinity equality is independent of the chosen greatest
zero-infinity certificate. -/
public theorem TopZeroInfinitySet.aeInfinityEq_iff {measure : Measure space}
    (first second : TopZeroInfinitySet measure) (left right : alpha → ENNReal) :
    first.AEInfinityEq left right ↔ second.AEInfinityEq left right := by
  unfold TopZeroInfinitySet.AEInfinityEq
  rw [first.restrict_complement_eq second, first.restrict_eq second]

/-- Almost-everywhere-infinity equality is reflexive. -/
public theorem TopZeroInfinitySet.AEInfinityEq.refl {measure : Measure space}
    (top : TopZeroInfinitySet measure) (function : alpha → ENNReal) :
    top.AEInfinityEq function function :=
  ⟨Measure.AEEq.refl _, Measure.ae_of_forall (fun _ => Iff.rfl)⟩

/-- Almost-everywhere-infinity equality is symmetric. -/
public theorem TopZeroInfinitySet.AEInfinityEq.symm {measure : Measure space}
    {top : TopZeroInfinitySet measure} {left right : alpha → ENNReal}
    (equal : top.AEInfinityEq left right) : top.AEInfinityEq right left :=
  ⟨equal.1.symm, equal.2.mono (fun _ agree => agree.symm)⟩

/-- Almost-everywhere-infinity equality is transitive. -/
public theorem TopZeroInfinitySet.AEInfinityEq.trans {measure : Measure space}
    {top : TopZeroInfinitySet measure}
    {left middle right : alpha → ENNReal}
    (first : top.AEInfinityEq left middle) (second : top.AEInfinityEq middle right) :
    top.AEInfinityEq left right :=
  ⟨first.1.trans second.1, (first.2.and second.2).mono (fun _ agree => agree.1.trans agree.2)⟩

/-- Ordinary almost-everywhere equality implies almost-everywhere-infinity
equality without finiteness or measurability premises. -/
public theorem TopZeroInfinitySet.AEInfinityEq.of_aeEq {measure : Measure space}
    {top : TopZeroInfinitySet measure} {left right : alpha → ENNReal}
    (equal : measure.AEEq left right) : top.AEInfinityEq left right := by
  refine ⟨equal.restrict _, ?_⟩
  exact (equal.restrict top.set).mono (fun _ equality => by rw [equality])

/-- Under a sigma-finite reference measure, almost-everywhere-infinity
equality reduces to ordinary almost-everywhere equality without density
measurability. -/
public theorem TopZeroInfinitySet.AEInfinityEq.iff_aeEq_of_sigmaFinite {measure : Measure space}
    (finite : SigmaFinite measure) (top : TopZeroInfinitySet measure)
    (left right : alpha → ENNReal) : top.AEInfinityEq left right ↔ measure.AEEq left right := by
  have nullComplement : measure.NullSet (Set.complement (Set.complement top.set)) := by
    rw [Set.complement_complement]
    exact top.zero_infinity.null_of_sigmaFinite finite
  have full := measure.restrict_eq_self_of_complement_null nullComplement
  constructor
  · intro agree
    have outside := agree.1
    rw [full] at outside
    exact outside
  · exact TopZeroInfinitySet.AEInfinityEq.of_aeEq

end Problib.Measure.Measure
