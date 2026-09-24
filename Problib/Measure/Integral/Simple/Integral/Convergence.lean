module

public import Problib.Measure.Integral.Simple.Approximation
public import Problib.Measure.Integral.Simple.Integral.Partition
import Problib.Measure.Additive.Continuity
public import Problib.Measure.Additive.Restrict

set_option autoImplicit false

/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl

Adapted from Mathlib/MeasureTheory/Function/SimpleFunc.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny exchanges monotone suprema with the finite sum defining a simple
integral.
-/

namespace Problib.Measure

open Problib.Real

universe u

namespace SimpleFunction

variable {alpha : Type u} {source : Space alpha}

noncomputable section

/-- Restricting a simple integral to an increasing union is the supremum of
the restricted integrals. -/
public theorem integral_restrict_iSup (function : SimpleFunction source)
    (measure : Measure source) (regions : Nat → Set alpha)
    (measurable : ∀ index, source.Measurable (regions index))
    (monotone : Set.MonotoneFamily regions) :
    integral function (measure.restrict (Set.iUnion regions)) =
      ENNReal.iSup (fun index =>
        integral function (measure.restrict (regions index))) := by
  let terms : Nat → ENNReal → ENNReal := fun index value =>
    ENNReal.mul value
      (measure (Set.inter (function.fiber value) (regions index)))
  have fiberContinuous (value : ENNReal) :
      measure (Set.inter (function.fiber value) (Set.iUnion regions)) =
        ENNReal.iSup (fun index =>
          measure (Set.inter (function.fiber value) (regions index))) := by
    rw [Set.inter_iUnion]
    exact measure.continuity_from_below
      (fun index => Set.inter (function.fiber value) (regions index))
      (fun index => source.inter (function.fiber_measurable value)
        (measurable index))
      (by
        intro first second included input member
        exact ⟨member.1, monotone included member.2⟩)
  have termLimit (value : ENNReal) :
      ENNReal.mul value
          ((measure.restrict (Set.iUnion regions))
            (function.fiber value)) =
        ENNReal.iSup (fun index => terms index value) := by
    rw [measure.restrict_apply (Set.iUnion regions)
      (function.fiber_measurable value), fiberContinuous value,
      ENNReal.mul_iSup]
  calc
    integral function (measure.restrict (Set.iUnion regions)) =
        finiteSum (function.values.map fun value =>
          ENNReal.iSup (fun index => terms index value)) := by
      unfold integral
      apply congrArg finiteSum
      apply List.map_congr_left
      intro value _
      exact termLimit value
    _ = ENNReal.iSup (fun index =>
        finiteSum (function.values.map (terms index))) := by
      apply finiteSum_map_iSup
      intro index value
      exact ENNReal.mul_le_mul_left
        (measure.mono fun input member =>
          ⟨member.1, monotone (Nat.le_succ index) member.2⟩)
        value
    _ = ENNReal.iSup (fun index =>
        integral function (measure.restrict (regions index))) := by
      apply congrArg ENNReal.iSup
      funext index
      unfold integral
      apply congrArg finiteSum
      apply List.map_congr_left
      intro value _
      exact congrArg (ENNReal.mul value)
        (measure.restrict_apply (regions index)
          (function.fiber_measurable value)).symm

/-- The integral of a simple function is reconstructed by the integrals of
its canonical finite rational approximations. -/
public theorem integral_iSup_approximation
    (function : SimpleFunction source) (measure : Measure source) :
    integral function measure =
      ENNReal.iSup (fun index =>
        integral (approximation function function.measurable index)
          measure) := by
  let terms : Nat → ENNReal → ENNReal := fun index value =>
    ENNReal.mul (ENNReal.approximation value index)
      (measure (function.fiber value))
  have approximationIntegral (index : Nat) :
      integral (approximation function function.measurable index) measure =
        finiteSum (function.values.map (terms index)) := by
    exact integral_eq_partition
      (approximation function function.measurable index) measure
      function.values function.values_nodup function.fiber
      (fun value => ENNReal.approximation value index)
      (fun value _ => function.fiber_measurable value)
      (fun first _ second _ different =>
        function.levelSet_disjoint different)
      function.mem_some_levelSet
      (fun value _ input member => by
        rw [approximation_apply,
          (function.mem_fiber_iff value input).mp member])
  have termLimit (value : ENNReal) :
      ENNReal.iSup (fun index => terms index value) =
        ENNReal.mul value (measure (function.fiber value)) := by
    calc
      ENNReal.iSup (fun index => terms index value) =
          ENNReal.iSup (fun index => ENNReal.mul
            (measure (function.fiber value))
            (ENNReal.approximation value index)) := by
        apply congrArg ENNReal.iSup
        funext index
        exact ENNReal.mul_comm _ _
      _ = ENNReal.mul (measure (function.fiber value))
          (ENNReal.iSup (ENNReal.approximation value)) :=
        (ENNReal.mul_iSup (measure (function.fiber value))
          (ENNReal.approximation value)).symm
      _ = ENNReal.mul (measure (function.fiber value)) value := by
        rw [ENNReal.iSup_approximation]
      _ = ENNReal.mul value (measure (function.fiber value)) :=
        ENNReal.mul_comm _ _
  calc
    integral function measure =
        finiteSum (function.values.map fun value =>
          ENNReal.iSup (fun index => terms index value)) := by
      unfold integral
      apply congrArg finiteSum
      apply List.map_congr_left
      intro value _
      exact (termLimit value).symm
    _ = ENNReal.iSup (fun index =>
        finiteSum (function.values.map (terms index))) := by
      apply finiteSum_map_iSup
      intro index value
      exact ENNReal.mul_le_mul_right
        (ENNReal.approximation_step value index)
        (measure (function.fiber value))
    _ = ENNReal.iSup (fun index =>
        integral (approximation function function.measurable index)
          measure) := by
      apply congrArg ENNReal.iSup
      funext index
      exact (approximationIntegral index).symm

end

end SimpleFunction

end Problib.Measure
