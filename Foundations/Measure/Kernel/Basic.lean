module

public import Foundations.Measure.Additive.SFinite
public import Foundations.Measure.Extended.Limit

set_option autoImplicit false

/-
Copyright (c) 2018 Johannes Hölzl, Jason Gross, Alexander Bentkamp.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jason Gross, Alexander Bentkamp, Jeremy Avigad,
  Leonardo de Moura

Adapted from Mathlib/Probability/Kernel/Defs.lean and
Mathlib/Probability/Kernel/Basic.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35.

Tiny uses explicit measurable spaces and constructive s-finite
decompositions instead of a typeclass hierarchy.
-/

namespace Foundations.Measure
open Foundations.Real
universe u v w

/-- A measurable family of measures. -/
public structure Kernel {alpha : Type u} {beta : Type v}
    (source : Space alpha) (target : Space beta) where
  toFun : alpha → Measure target
  measurable : ∀ {set}, target.Measurable set →
    ENNRealMeasurable source (fun input => toFun input set)

namespace Kernel
variable {alpha : Type u} {beta : Type v} {gamma : Type w}
  {source : Space alpha} {target : Space beta} {result : Space gamma}

public noncomputable instance :
    CoeFun (Kernel source target) (fun _ => alpha → Measure target) where
  coe kernel := kernel.toFun

@[ext] public theorem ext {left right : Kernel source target}
    (equal : ∀ input, left input = right input) : left = right := by
  cases left with
  | mk leftFunction leftMeasurable =>
      cases right with
      | mk rightFunction rightMeasurable =>
          have functionEqual : leftFunction = rightFunction := funext equal
          subst rightFunction
          rfl

public theorem ext_measurable {left right : Kernel source target}
    (equal : ∀ input set, target.Measurable set →
      left input set = right input set) : left = right := by
  apply Kernel.ext
  intro input
  apply Measure.ext
  intro set setMeasurable
  exact equal input set setMeasurable

/-- The constant family with the same measure at every input. -/
@[expose] public noncomputable def const (source : Space alpha)
    (measure : Measure target) : Kernel source target where
  toFun := fun _ => measure
  measurable := fun _ => ENNRealMeasurable.constant source _

@[simp] public theorem const_apply (source : Space alpha)
    (measure : Measure target) (input : alpha) :
    const source measure input = measure := rfl

/-- The Dirac family induced by a measurable function. -/
@[expose] public noncomputable def deterministic (function : alpha → beta)
    (functionMeasurable : MeasurableMap source target function) :
    Kernel source target where
  toFun := fun input => Measure.dirac target (function input)
  measurable := by
    intro set setMeasurable
    let region := Set.preimage function set
    have regionMeasurable : source.Measurable region :=
      functionMeasurable setMeasurable
    have indicatorMeasurable := ENNRealMeasurable.indicator regionMeasurable
      (ENNRealMeasurable.constant source ENNReal.one)
    have equal : (fun input => Measure.dirac target (function input) set) =
        ennrealIndicator region (fun _ => ENNReal.one) := by
      classical
      funext input
      rw [Measure.dirac_apply target (function input) setMeasurable]
      unfold ennrealIndicator ennrealPiecewise region Set.preimage
      rfl
    rw [equal]
    exact indicatorMeasurable

@[simp] public theorem deterministic_apply (function : alpha → beta)
    (functionMeasurable : MeasurableMap source target function)
    (input : alpha) :
    deterministic function functionMeasurable input =
      Measure.dirac target (function input) := rfl

/-- Push every measure in a kernel forward along a measurable map. -/
@[expose] public noncomputable def map (kernel : Kernel source target)
    (function : beta → gamma)
    (functionMeasurable : MeasurableMap target result function) :
    Kernel source result where
  toFun := fun input => (kernel input).map function functionMeasurable
  measurable := by
    intro set setMeasurable
    have originalMeasurable := kernel.measurable
      (functionMeasurable setMeasurable)
    have equal : (fun input =>
        (kernel input).map function functionMeasurable set) =
        (fun input => kernel input (Set.preimage function set)) := by
      funext input
      exact (kernel input).map_apply function functionMeasurable setMeasurable
    rw [equal]
    exact originalMeasurable

@[simp] public theorem map_apply (kernel : Kernel source target)
    (function : beta → gamma)
    (functionMeasurable : MeasurableMap target result function)
    (input : alpha) :
    kernel.map function functionMeasurable input =
      (kernel input).map function functionMeasurable := rfl

/-- The zero measure at every input. -/
@[expose] public noncomputable def zero (source : Space alpha)
    (target : Space beta) : Kernel source target :=
  const source (Measure.zero target)

@[simp] public theorem zero_apply (source : Space alpha)
    (target : Space beta) (input : alpha) :
    zero source target input = Measure.zero target := rfl

/-- Pointwise addition of kernels. -/
@[expose] public noncomputable def add (left right : Kernel source target) :
    Kernel source target where
  toFun := fun input => Measure.add (left input) (right input)
  measurable := by
    intro set setMeasurable
    have leftMeasurable := left.measurable setMeasurable
    have rightMeasurable := right.measurable setMeasurable
    have sumMeasurable := ENNRealMeasurable.add leftMeasurable rightMeasurable
    have equal : (fun input => Measure.add (left input) (right input) set) =
        (fun input => ENNReal.add (left input set) (right input set)) := by
      funext input
      exact Measure.add_apply_measurable
        (left input) (right input) setMeasurable
    rw [equal]
    exact sumMeasurable

@[simp] public theorem add_apply (left right : Kernel source target)
    (input : alpha) :
    add left right input = Measure.add (left input) (right input) := rfl

/-- Pointwise countable sum of kernels. -/
@[expose] public noncomputable def sum
    (kernels : Nat → Kernel source target) : Kernel source target where
  toFun := fun input => Measure.sum (fun index => kernels index input)
  measurable := by
    intro set setMeasurable
    have termsMeasurable : ∀ index, ENNRealMeasurable source
        (fun input => kernels index input set) :=
      fun index => (kernels index).measurable setMeasurable
    have seriesMeasurable := ENNRealMeasurable.tsum termsMeasurable
    have equal : (fun input =>
        Measure.sum (fun index => kernels index input) set) =
        (fun input => ENNReal.tsum
          (fun index => kernels index input set)) := by
      funext input
      exact Measure.sum_apply
        (fun index => kernels index input) setMeasurable
    rw [equal]
    exact seriesMeasurable

@[simp] public theorem sum_apply (kernels : Nat → Kernel source target)
    (input : alpha) :
    sum kernels input = Measure.sum (fun index => kernels index input) := rfl

public theorem sum_add (left right : Nat → Kernel source target) :
    sum (fun index => add (left index) (right index)) =
      add (sum left) (sum right) := by
  apply Kernel.ext
  intro input
  exact Measure.sum_add
    (fun index => left index input) (fun index => right index input)

@[expose] public def flatten
    (kernels : Nat → Nat → Kernel source target) :
    Nat → Kernel source target :=
  fun index =>
    let pair := Countable.Pair.decode index
    kernels pair.1 pair.2

public theorem sum_double
    (kernels : Nat → Nat → Kernel source target) :
    sum (flatten kernels) = sum (fun row => sum (kernels row)) := by
  apply Kernel.ext
  intro input
  exact Measure.sum_double
    (fun row column => kernels row column input)

public theorem map_sum (kernels : Nat → Kernel source target)
    (function : beta → gamma)
    (functionMeasurable : MeasurableMap target result function) :
    (sum kernels).map function functionMeasurable =
      sum (fun index => (kernels index).map function functionMeasurable) := by
  apply Kernel.ext
  intro input
  exact Measure.map_sum (fun index => kernels index input)
    function functionMeasurable

/-- A finite kernel has one finite bound valid at every input. -/
public structure IsFinite (kernel : Kernel source target) : Prop where
  exists_bound : ∃ bound : ENNReal, ENNReal.Finite bound ∧
    ∀ input, ENNReal.le (kernel input Set.univ) bound

namespace IsFinite

public theorem measure {kernel : Kernel source target}
    (finite : IsFinite kernel) (input : alpha) :
    Measure.IsFinite (kernel input) := by
  rcases finite.exists_bound with ⟨bound, boundFinite, bounded⟩
  exact ⟨ENNReal.finiteOfLe (bounded input) boundFinite⟩

public theorem const (source : Space alpha) {measure : Measure target}
    (finite : Measure.IsFinite measure) : IsFinite (Kernel.const source measure) :=
  ⟨⟨measure Set.univ, finite.univFinite,
    fun _ => ENNReal.leRefl _⟩⟩

public theorem deterministic (function : alpha → beta)
    (functionMeasurable : MeasurableMap source target function) :
    IsFinite (Kernel.deterministic function functionMeasurable) := by
  refine ⟨⟨ENNReal.one, True.intro, ?_⟩⟩
  intro input
  rw [Kernel.deterministic_apply, Measure.dirac_apply_univ]
  exact ENNReal.leRefl _

public theorem zero (source : Space alpha) (target : Space beta) :
    IsFinite (Kernel.zero source target) :=
  const source (Measure.IsFinite.zero target)

public theorem add {left right : Kernel source target}
    (leftFinite : IsFinite left) (rightFinite : IsFinite right) :
    IsFinite (Kernel.add left right) := by
  rcases leftFinite.exists_bound with
    ⟨leftBound, leftBoundFinite, leftBounded⟩
  rcases rightFinite.exists_bound with
    ⟨rightBound, rightBoundFinite, rightBounded⟩
  refine ⟨⟨ENNReal.add leftBound rightBound,
    ENNReal.addFinite leftBoundFinite rightBoundFinite, ?_⟩⟩
  intro input
  rw [Kernel.add_apply,
    Measure.add_apply_measurable (left input) (right input) target.univ]
  exact ENNReal.addLeAdd (leftBounded input) (rightBounded input)

public theorem map {kernel : Kernel source target} (finite : IsFinite kernel)
    (function : beta → gamma)
    (functionMeasurable : MeasurableMap target result function) :
    IsFinite (kernel.map function functionMeasurable) := by
  rcases finite.exists_bound with ⟨bound, boundFinite, bounded⟩
  refine ⟨⟨bound, boundFinite, ?_⟩⟩
  intro input
  rw [Kernel.map_apply,
    (kernel input).map_apply function functionMeasurable result.univ,
    Set.preimage_univ]
  exact bounded input

end IsFinite
/-- A kernel presented as a countable sum of finite kernels. -/
public structure IsSFinite (kernel : Kernel source target) :
    Type (max u v) where
  components : Nat → Kernel source target
  finite : ∀ index, IsFinite (components index)
  sum_eq : Kernel.sum components = kernel

namespace IsFinite

public noncomputable def toSFinite {kernel : Kernel source target}
    (finite : IsFinite kernel) : IsSFinite kernel where
  components := fun index =>
    match index with
    | 0 => kernel
    | _ + 1 => Kernel.zero source target
  finite := by
    intro index
    cases index with
    | zero => exact finite
    | succ index => exact IsFinite.zero source target
  sum_eq := by
    apply Kernel.ext
    intro input
    apply Measure.ext
    intro set setMeasurable
    rw [Kernel.sum_apply,
      Measure.sum_apply _ setMeasurable]
    exact ENNReal.tsumEqOfAtMostOneNonzero
      (fun index => (match index with
        | 0 => kernel
        | _ + 1 => Kernel.zero source target) input set) 0 (by
          intro index different
          cases index with
          | zero => exact False.elim (different rfl)
          | succ index => exact Measure.zero_apply set)

end IsFinite

namespace IsSFinite

public noncomputable def ofFinite {kernel : Kernel source target}
    (finite : IsFinite kernel) : IsSFinite kernel := finite.toSFinite

public noncomputable def zero (source : Space alpha) (target : Space beta) :
    IsSFinite (Kernel.zero source target) :=
  (IsFinite.zero source target).toSFinite

public noncomputable def deterministic (function : alpha → beta)
    (functionMeasurable : MeasurableMap source target function) :
    IsSFinite (Kernel.deterministic function functionMeasurable) :=
  (IsFinite.deterministic function functionMeasurable).toSFinite

public noncomputable def add {left right : Kernel source target}
    (leftFinite : IsSFinite left) (rightFinite : IsSFinite right) :
    IsSFinite (Kernel.add left right) where
  components := fun index => Kernel.add
    (leftFinite.components index) (rightFinite.components index)
  finite := fun index => IsFinite.add
    (leftFinite.finite index) (rightFinite.finite index)
  sum_eq := by
    rw [Kernel.sum_add, leftFinite.sum_eq, rightFinite.sum_eq]

public noncomputable def sum (kernels : Nat → Kernel source target)
    (finite : ∀ index, IsSFinite (kernels index)) :
    IsSFinite (Kernel.sum kernels) where
  components := Kernel.flatten
    (fun row column => (finite row).components column)
  finite := by
    intro index
    exact (finite (Countable.Pair.decode index).1).finite
      (Countable.Pair.decode index).2
  sum_eq := by
    rw [Kernel.sum_double]
    apply congrArg Kernel.sum
    funext row
    exact (finite row).sum_eq

public noncomputable def map {kernel : Kernel source target}
    (finite : IsSFinite kernel) (function : beta → gamma)
    (functionMeasurable : MeasurableMap target result function) :
    IsSFinite (kernel.map function functionMeasurable) where
  components := fun index =>
    (finite.components index).map function functionMeasurable
  finite := fun index => IsFinite.map
    (finite.finite index) function functionMeasurable
  sum_eq := by
    rw [← Kernel.map_sum, finite.sum_eq]

public noncomputable def const (source : Space alpha)
    {measure : Measure target} (finite : Measure.SFinite measure) :
    IsSFinite (Kernel.const source measure) where
  components := fun index => Kernel.const source (finite.components index)
  finite := fun index => IsFinite.const source (finite.finite index)
  sum_eq := by
    apply Kernel.ext
    intro input
    simpa only [Kernel.sum_apply, Kernel.const_apply] using finite.sum_eq

public noncomputable def measure {kernel : Kernel source target}
    (finite : IsSFinite kernel) (input : alpha) :
    Measure.SFinite (kernel input) where
  components := fun index => finite.components index input
  finite := fun index => (finite.finite index).measure input
  sum_eq := by
    simpa only [Kernel.sum_apply] using
      congrArg (fun current => current input) finite.sum_eq

end IsSFinite

end Kernel

end Foundations.Measure
