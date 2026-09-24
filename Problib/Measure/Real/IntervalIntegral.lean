module

public import Problib.Measure.Real.Lebesgue
public import Problib.Measure.Integral.Lebesgue.AlmostEverywhere
public import Problib.Measure.AlmostEverywhere.Transport

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Sébastien Gouëzel, Yury Kudryashov

The open-interval volume statement is adapted from Real.volume_Ioo in
Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35. Tiny proves the endpoint change
from singleton nullity and exposes equality of restricted measures before
passing to arbitrary lower integrands. No Mathlib import is used.
-/

set_option autoImplicit false

namespace Problib.Measure.Real

open Problib.Real
open Problib.Real.Construction.Dedekind

/-- An open and closed upper ray differ only at their null endpoint. -/
public theorem ioi_aeEq_ici (endpoint : Carrier) : volume.AEEq (Ioi endpoint) (Ici endpoint) := by
  apply Measure.NullSet.mono (show volume.NullSet (Set.singleton endpoint) from volume_singleton endpoint)
  intro value differs
  change value = endpoint
  apply Classical.byContradiction
  intro unequal
  apply differs
  apply propext
  exact ⟨fun member => member.1,
    fun member => ⟨member, fun reverse => unequal (le_antisymm reverse member)⟩⟩

public theorem restrict_volume_ioi (endpoint : Carrier) :
    volume.restrict (Ioi endpoint) = volume.restrict (Ici endpoint) :=
  Measure.restrict_congr_ae (ioi_aeEq_ici endpoint)

/-- The open and half-open intervals differ only at the null upper endpoint. -/
public theorem ioo_aeEq_ioc (a b : Carrier) : volume.AEEq (Ioo a b) (Ioc a b) := by
  apply Measure.NullSet.mono (show volume.NullSet (Set.singleton b) from volume_singleton b)
  intro x differs
  change x = b
  apply Classical.byContradiction
  intro unequal
  apply differs
  apply propext
  constructor
  · intro member
    exact ⟨member.1, member.2.1⟩
  · intro member
    exact ⟨member.1, member.2, fun reverse => unequal (le_antisymm member.2 reverse)⟩

public theorem restrict_volume_ioo (a b : Carrier) :
    volume.restrict (Ioo a b) = volume.restrict (Ioc a b) :=
  Measure.restrict_congr_ae (ioo_aeEq_ioc a b)

/-- An open interval has its endpoint difference as volume, including reversed endpoints. -/
public theorem volume_ioo (a b : Carrier) :
    volume (Ioo a b) = ENNReal.ofReal (sub b a) := by
  rw [← volume_ioc a b]
  exact Measure.measure_eq_of_null_difference
    (Measure.NullSet.mono (ioo_aeEq_ioc a b)
      (fun {_} member equal => member.2 (Eq.mp equal member.1)))
    (Measure.NullSet.mono (ioo_aeEq_ioc a b)
      (fun {_} member equal => member.2 (Eq.mpr equal member.1)))

/-- Null endpoints can be removed for any nonnegative lower integrand. -/
public theorem lintegral_restrict_ioo (a b : Carrier) (f : Carrier → ENNReal) :
    lintegral (volume.restrict (Ioo a b)) f =
      lintegral (volume.restrict (Ioc a b)) f := by
  rw [restrict_volume_ioo]

/-- Agreement on the interval suffices, without measurability of either integrand. -/
public theorem lintegral_restrict_ioc_congr (a b : Carrier) (f g : Carrier → ENNReal)
    (same : ∀ x, Ioc a b x → f x = g x) :
    lintegral (volume.restrict (Ioc a b)) f =
      lintegral (volume.restrict (Ioc a b)) g :=
  lintegral_congr_ae ((volume.ae_restrict_mem (measurable_ioc a b)).mono same)

end Problib.Measure.Real
