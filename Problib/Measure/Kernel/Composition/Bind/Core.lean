module

public import Problib.Measure.Kernel.Basic
public import Problib.Measure.Integral.Lebesgue.Basic
import Problib.Measure.Integral.Lebesgue.Algebra

set_option autoImplicit false

/-
Copyright (c) 2017 Johannes Hölzl, Mario Carneiro.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Adapted from Mathlib/MeasureTheory/Measure/GiryMonad.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny uses a genuinely measurable kernel, so bind needs no separate
almost-everywhere measurability or s-finiteness premise.
-/

namespace Problib.Measure

open Problib.Real

universe u v

namespace Measure

variable {alpha : Type u} {beta : Type v}
  {source : Space alpha} {target : Space beta}

/-- Integrate a measurable family of measures against a measure. -/
@[expose] public noncomputable def bind (measure : Measure source)
    (kernel : Kernel source target) : Measure target where
  content := fun set setMeasurable =>
    lintegral measure (fun input => kernel input set)
  empty := by
    change lintegral measure (fun input => kernel input Set.empty) =
      ENNReal.zero
    calc
      lintegral measure (fun input => kernel input Set.empty) =
          lintegral measure (fun _ => ENNReal.zero) := by
        apply lintegral_congr
        intro input
        exact (kernel input).empty_apply
      _ = ENNReal.zero := lintegral_zero measure
  content_iUnion_disjoint := by
    intro sets setsMeasurable disjoint
    change lintegral measure
        (fun input => kernel input (Set.iUnion sets)) =
      ENNReal.tsum (fun index =>
        lintegral measure (fun input => kernel input (sets index)))
    calc
      lintegral measure (fun input => kernel input (Set.iUnion sets)) =
          lintegral measure (fun input => ENNReal.tsum
            (fun index => kernel input (sets index))) := by
        apply lintegral_congr
        intro input
        exact (kernel input).iUnion_disjoint
          sets setsMeasurable disjoint
      _ = ENNReal.tsum (fun index =>
          lintegral measure (fun input => kernel input (sets index))) :=
        lintegral_tsum measure
          (fun index input => kernel input (sets index))
          (fun index => kernel.measurable (setsMeasurable index))

@[simp] public theorem bind_apply (measure : Measure source)
    (kernel : Kernel source target) {set : Set beta}
    (setMeasurable : target.Measurable set) :
    measure.bind kernel set =
      lintegral measure (fun input => kernel input set) := by
  rw [(measure.bind kernel).apply_measurable setMeasurable]
  rfl

end Measure

end Problib.Measure
