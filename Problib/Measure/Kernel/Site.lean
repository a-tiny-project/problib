module

public import Problib.Measure.Pi
public import Problib.Measure.Kernel.Product
public import Problib.Measure.Kernel.Product.Finite
public import Problib.Measure.Kernel.Composition
public import Problib.Measure.Kernel.Precomp
import Problib.Measure.Kernel.Composition.Bind.Transport
import Problib.Measure.Measurability

/-! Site updates on dependent products.

A site update resamples one coordinate of a point in `∀ index, α index` from a
kernel of the whole point and keeps every other coordinate. `Reads` states
which coordinates a function of the point depends on, pointwise. Two updates at
distinct sites commute when neither kernel reads the other's site, and both
orders then equal one draw of the two coordinates from the product of the two
kernels. A sweep runs a list of updates in order, and a sweep of pairwise
independent updates is the same kernel in every order.
-/

set_option autoImplicit false

namespace Problib.Measure.Kernel.Site

open Problib.Real

universe u v w

variable {ι : Type u} {α : ι → Type v} {spaces : ∀ index, Space (α index)}

/-- `function` depends on a point only through the coordinates in `sites`, so
it factors through restriction to `sites`. -/
@[expose] public def Reads {γ : Sort w} (function : (∀ index, α index) → γ) (sites : Set ι) :
    Prop :=
  ∀ first second : ∀ index, α index,
    (∀ index, sites index → first index = second index) → function first = function second

variable [DecidableEq ι]

/-- The point with coordinate `site` replaced by `value`. -/
@[expose] public def replace (point : ∀ index, α index) (site : ι) (value : α site) :
    ∀ index, α index :=
  fun index => if equal : index = site then equal ▸ value else point index

@[simp] public theorem replace_same (point : ∀ index, α index) (site : ι) (value : α site) :
    replace point site value site = value := by
  unfold replace
  rw [dite_eq_left rfl]

public theorem replace_of_ne (point : ∀ index, α index) {site index : ι} (value : α site)
    (distinct : index ≠ site) : replace point site value index = point index := by
  unfold replace
  rw [dite_eq_right distinct]

/-- Replacing two distinct sites commutes. -/
public theorem replace_comm (point : ∀ index, α index) {first second : ι}
    (distinct : first ≠ second) (firstValue : α first) (secondValue : α second) :
    replace (replace point first firstValue) second secondValue =
      replace (replace point second secondValue) first firstValue := by
  funext index
  by_cases atSecond : index = second
  · subst atSecond
    rw [replace_same, replace_of_ne _ _ (Ne.symm distinct), replace_same]
  · by_cases atFirst : index = first
    · subst atFirst
      rw [replace_of_ne _ _ atSecond, replace_same, replace_same]
    · rw [replace_of_ne _ _ atSecond, replace_of_ne _ _ atFirst, replace_of_ne _ _ atFirst,
        replace_of_ne _ _ atSecond]

/-- Replacing one site twice keeps the second value. -/
public theorem replace_replace_same (point : ∀ index, α index) (site : ι)
    (first second : α site) :
    replace (replace point site first) site second = replace point site second := by
  funext index
  by_cases equal : index = site
  · subst equal
    rw [replace_same, replace_same]
  · rw [replace_of_ne _ _ equal, replace_of_ne _ _ equal, replace_of_ne _ _ equal]

/-- Replacement is jointly measurable in the point and the new value. -/
public theorem replace_measurable (site : ι) :
    MeasurableMap (Space.product (Space.pi spaces) (spaces site)) (Space.pi spaces)
      (fun pair => replace pair.1 site pair.2) := by
  apply Space.pi_measurable
  intro index
  by_cases equal : index = site
  · subst equal
    have same : (fun pair : (∀ index, α index) × α index => replace pair.1 index pair.2 index) =
        (fun pair => pair.2) := funext (fun pair => replace_same pair.1 index pair.2)
    rw [same]
    exact Space.second_measurable _ _
  · have same : (fun pair : (∀ index, α index) × α site => replace pair.1 site pair.2 index) =
        (fun pair => pair.1 index) := funext (fun pair => replace_of_ne pair.1 pair.2 equal)
    rw [same]
    exact MeasurableMap.comp (Space.coordinate_measurable spaces index)
      (Space.first_measurable _ _)

public theorem replace_value_measurable (point : ∀ index, α index) (site : ι) :
    MeasurableMap (spaces site) (Space.pi spaces) (replace point site) :=
  MeasurableMap.comp (replace_measurable site) (pair_left_measurable point)

/-- Resample coordinate `site` from `kernel` and keep every other coordinate. -/
@[expose] public noncomputable def update (site : ι)
    (kernel : Kernel (Space.pi spaces) (spaces site)) (finite : IsSFinite kernel) :
    Kernel (Space.pi spaces) (Space.pi spaces) :=
  (kernel.attach finite).map (fun pair => replace pair.1 site pair.2) (replace_measurable site)

public theorem update_apply (site : ι) (kernel : Kernel (Space.pi spaces) (spaces site))
    (finite : IsSFinite kernel) (point : ∀ index, α index) :
    update site kernel finite point =
      (kernel point).map (replace point site) (replace_value_measurable point site) := by
  unfold update
  rw [Kernel.map_apply, Kernel.attach_apply, Measure.map_comp]

/-- An update by a probability kernel is a probability kernel. -/
public theorem update_isProbability (site : ι) {kernel : Kernel (Space.pi spaces) (spaces site)}
    (finite : IsSFinite kernel) {point : ∀ index, α index}
    (probability : Measure.IsProbability (kernel point)) :
    Measure.IsProbability (update site kernel finite point) := by
  rw [update_apply]
  exact probability.map _ _

/-- `function` does not read coordinate `site`. -/
@[expose] public def Ignores {γ : Sort w} (function : (∀ index, α index) → γ) (site : ι) :
    Prop :=
  ∀ (point : ∀ index, α index) (value : α site), function (replace point site value) = function point

/-- A function ignores every site outside the coordinates it reads. -/
public theorem ignores_of_reads {γ : Sort w} {function : (∀ index, α index) → γ}
    {sites : Set ι} (reads : Reads function sites) {site : ι} (outside : ¬sites site) :
    Ignores function site := by
  intro point value
  apply reads
  intro index member
  have distinct : index ≠ site := fun equal => outside (equal ▸ member)
  exact replace_of_ne point value distinct

public theorem replace_replace_measurable (first second : ι) :
    MeasurableMap
      (Space.product (Space.pi spaces) (Space.product (spaces first) (spaces second)))
      (Space.pi spaces)
      (fun triple => replace (replace triple.1 first triple.2.1) second triple.2.2) := by
  measurability [replace_measurable (spaces := spaces) first,
    replace_measurable (spaces := spaces) second]

public theorem replace_replace_value_measurable (point : ∀ index, α index) (first second : ι) :
    MeasurableMap (Space.product (spaces first) (spaces second)) (Space.pi spaces)
      (fun pair => replace (replace point first pair.1) second pair.2) :=
  MeasurableMap.comp (replace_replace_measurable first second) (pair_left_measurable point)

/-- Draw both sites independently from their kernels at the same point and
write both values. -/
@[expose] public noncomputable def parallel (first second : ι)
    (firstKernel : Kernel (Space.pi spaces) (spaces first)) (firstFinite : IsSFinite firstKernel)
    (secondKernel : Kernel (Space.pi spaces) (spaces second))
    (secondFinite : IsSFinite secondKernel) :
    Kernel (Space.pi spaces) (Space.pi spaces) :=
  ((Kernel.pair firstKernel firstFinite secondKernel secondFinite).attach
      (IsSFinite.pair firstFinite secondFinite)).map
    (fun triple => replace (replace triple.1 first triple.2.1) second triple.2.2)
    (replace_replace_measurable first second)

public theorem parallel_apply (first second : ι)
    (firstKernel : Kernel (Space.pi spaces) (spaces first)) (firstFinite : IsSFinite firstKernel)
    (secondKernel : Kernel (Space.pi spaces) (spaces second))
    (secondFinite : IsSFinite secondKernel) (point : ∀ index, α index) :
    parallel first second firstKernel firstFinite secondKernel secondFinite point =
      (Measure.prod (firstKernel point) (secondKernel point) (secondFinite.measure point)).map
        (fun pair => replace (replace point first pair.1) second pair.2)
        (replace_replace_value_measurable point first second) := by
  unfold parallel
  rw [Kernel.map_apply, Kernel.attach_apply, Measure.map_comp, Kernel.pair_apply]

/-- Updating `first` and then `second` is the parallel update when the second
kernel does not read the first site. -/
public theorem update_comp_update {first second : ι}
    {firstKernel : Kernel (Space.pi spaces) (spaces first)} (firstFinite : IsSFinite firstKernel)
    {secondKernel : Kernel (Space.pi spaces) (spaces second)}
    (secondFinite : IsSFinite secondKernel) (secondIgnores : Ignores secondKernel first) :
    (update first firstKernel firstFinite).comp (update second secondKernel secondFinite) =
      parallel first second firstKernel firstFinite secondKernel secondFinite := by
  apply Kernel.ext_measurable
  intro point set setMeasurable
  rw [Kernel.comp_apply, update_apply, Measure.bind_map, Measure.bind_apply _ _ setMeasurable,
    parallel_apply, Measure.map_apply _ _ _ setMeasurable,
    Measure.prod_apply _ _ _ (replace_replace_value_measurable point first second setMeasurable)]
  apply lintegral_congr
  intro value
  rw [Kernel.precomp_apply, update_apply, secondIgnores point value,
    Measure.map_apply _ _ _ setMeasurable]
  rfl

/-- Swapping the roles of two distinct sites leaves the parallel update unchanged. -/
public theorem parallel_comm {first second : ι} (distinct : first ≠ second)
    (firstKernel : Kernel (Space.pi spaces) (spaces first)) (firstFinite : IsSFinite firstKernel)
    (secondKernel : Kernel (Space.pi spaces) (spaces second))
    (secondFinite : IsSFinite secondKernel) :
    parallel first second firstKernel firstFinite secondKernel secondFinite =
      parallel second first secondKernel secondFinite firstKernel firstFinite := by
  apply Kernel.ext
  intro point
  rw [parallel_apply, parallel_apply,
    ← Measure.prod_swap (firstFinite.measure point) (secondFinite.measure point),
    Measure.map_comp]
  congr 1
  funext pair
  exact replace_comm point distinct pair.1 pair.2

/-- Updates at distinct sites commute when neither kernel reads the other's
site. -/
public theorem update_comm {first second : ι} (distinct : first ≠ second)
    {firstKernel : Kernel (Space.pi spaces) (spaces first)} (firstFinite : IsSFinite firstKernel)
    {secondKernel : Kernel (Space.pi spaces) (spaces second)}
    (secondFinite : IsSFinite secondKernel) (firstIgnores : Ignores firstKernel second)
    (secondIgnores : Ignores secondKernel first) :
    (update first firstKernel firstFinite).comp (update second secondKernel secondFinite) =
      (update second secondKernel secondFinite).comp (update first firstKernel firstFinite) := by
  rw [update_comp_update firstFinite secondFinite secondIgnores,
    update_comp_update secondFinite firstFinite firstIgnores,
    parallel_comm distinct]

omit [DecidableEq ι] in
/-- One site update: a site and an s-finite kernel for its coordinate. -/
public structure Step (spaces : ∀ index, Space (α index)) where
  site : ι
  kernel : Kernel (Space.pi spaces) (spaces site)
  finite : IsSFinite kernel

/-- The update kernel of one step. -/
@[expose] public noncomputable def Step.run (step : Step spaces) :
    Kernel (Space.pi spaces) (Space.pi spaces) :=
  update step.site step.kernel step.finite

/-- Two steps update distinct sites, and neither kernel reads the other's site. -/
@[expose] public def Independent (first second : Step spaces) : Prop :=
  first.site ≠ second.site ∧ Ignores first.kernel second.site ∧ Ignores second.kernel first.site

public theorem Independent.symm {first second : Step spaces}
    (independent : Independent first second) : Independent second first :=
  ⟨Ne.symm independent.1, independent.2.2, independent.2.1⟩

/-- Independent steps commute. -/
public theorem Step.run_comm {first second : Step spaces}
    (independent : Independent first second) :
    first.run.comp second.run = second.run.comp first.run :=
  update_comm independent.1 first.finite second.finite independent.2.1 independent.2.2

/-- Run a list of steps in order. The empty sweep is the identity kernel. -/
@[expose] public noncomputable def sweep :
    List (Step spaces) → Kernel (Space.pi spaces) (Space.pi spaces)
  | [] => Kernel.deterministic (fun point => point) (MeasurableMap.identity (Space.pi spaces))
  | step :: rest => step.run.comp (sweep rest)

public theorem sweep_nil :
    sweep ([] : List (Step spaces)) =
      Kernel.deterministic (fun point => point) (MeasurableMap.identity (Space.pi spaces)) :=
  rfl

public theorem sweep_cons (step : Step spaces) (rest : List (Step spaces)) :
    sweep (step :: rest) = step.run.comp (sweep rest) :=
  rfl

public theorem sweep_singleton (step : Step spaces) : sweep [step] = step.run := by
  rw [sweep_cons, sweep_nil, comp_deterministic]
  apply Kernel.ext
  intro point
  rw [Kernel.map_apply, Measure.map_id]

/-- Running one sweep and then another is the sweep of the joined list. -/
public theorem sweep_append (first second : List (Step spaces)) :
    sweep (first ++ second) = (sweep first).comp (sweep second) := by
  induction first with
  | nil =>
      apply Kernel.ext
      intro point
      rw [List.nil_append, sweep_nil, Kernel.deterministic_comp_apply]
  | cons step rest induction =>
      rw [List.cons_append, sweep_cons, sweep_cons, induction, comp_assoc]

/-- A sweep of probability updates is a probability kernel. -/
public theorem sweep_isProbability {steps : List (Step spaces)}
    (probability : ∀ step, step ∈ steps → ∀ point, Measure.IsProbability (step.kernel point))
    (point : ∀ index, α index) : Measure.IsProbability (sweep steps point) := by
  induction steps generalizing point with
  | nil =>
      rw [sweep_nil, Kernel.deterministic_apply]
      exact Measure.IsProbability.dirac _ point
  | cons step rest induction =>
      rw [sweep_cons, Kernel.comp_apply]
      exact (update_isProbability step.site step.finite
        (probability step List.mem_cons_self point)).bind (sweep rest)
        (induction (fun other member => probability other (List.mem_cons_of_mem step member)))

/-- A measure that every step of a sweep leaves unchanged is left unchanged by
the sweep. -/
public theorem sweep_invariant {steps : List (Step spaces)} {measure : Measure (Space.pi spaces)}
    (invariant : ∀ step, step ∈ steps → measure.bind step.run = measure) :
    measure.bind (sweep steps) = measure := by
  induction steps with
  | nil => rw [sweep_nil, Measure.bind_deterministic, Measure.map_id]
  | cons step rest induction =>
      rw [sweep_cons, ← Measure.bind_assoc, invariant step List.mem_cons_self,
        induction (fun other member => invariant other (List.mem_cons_of_mem step member))]

/-- A sweep of pairwise independent steps is the same kernel in every order. -/
public theorem sweep_perm {first second : List (Step spaces)} (perm : first.Perm second)
    (independent : first.Pairwise Independent) : sweep first = sweep second := by
  revert independent
  induction perm with
  | nil => intro _; rfl
  | cons step _ induction =>
      intro independent
      rw [sweep_cons, sweep_cons, induction independent.of_cons]
  | swap head next rest =>
      intro independent
      have pair : Independent next head :=
        List.rel_of_pairwise_cons independent List.mem_cons_self
      rw [sweep_cons, sweep_cons, sweep_cons, sweep_cons, ← comp_assoc, ← comp_assoc,
        Step.run_comm pair]
  | trans firstPerm _ firstInduction secondInduction =>
      intro independent
      exact (firstInduction independent).trans
        (secondInduction (firstPerm.pairwise independent Independent.symm))

/-- `update_comm` needs each kernel to ignore the other site. On two bits, the
update `x ← y` reads `y` and the update `y ← 1` reads nothing. From `(0, 0)`
the order `x` then `y` reaches `(0, 1)`, and the order `y` then `x` reaches
`(1, 1)`. -/
public theorem reading_update_does_not_commute :
    (update (spaces := fun _ : Bool => Space.discrete Bool) false
        (Kernel.deterministic (fun point : Bool → Bool => point true)
          (Space.coordinate_measurable (fun _ : Bool => Space.discrete Bool) true))
        (IsSFinite.deterministic _ _)).comp
      (update true
        (Kernel.deterministic (fun _ : Bool → Bool => true)
          (MeasurableMap.constant _ _ true))
        (IsSFinite.deterministic _ _)) ≠
    (update true
        (Kernel.deterministic (fun _ : Bool → Bool => true)
          (MeasurableMap.constant _ _ true))
        (IsSFinite.deterministic _ _)).comp
      (update (spaces := fun _ : Bool => Space.discrete Bool) false
        (Kernel.deterministic (fun point : Bool → Bool => point true)
          (Space.coordinate_measurable (fun _ : Bool => Space.discrete Bool) true))
        (IsSFinite.deterministic _ _)) := by
  intro equal
  have setMeasurable : (Space.pi (fun _ : Bool => Space.discrete Bool)).Measurable
      (fun point : Bool → Bool => point false = true) :=
    Space.coordinate_measurable (fun _ : Bool => Space.discrete Bool) false
      (set := fun value : Bool => value = true) True.intro
  have atStart := congrArg
    (fun kernel : Kernel (Space.pi (fun _ : Bool => Space.discrete Bool))
        (Space.pi (fun _ : Bool => Space.discrete Bool)) =>
      kernel (fun _ => false) (fun point : Bool → Bool => point false = true)) equal
  simp only [Kernel.comp_apply, update_apply, Kernel.deterministic_apply, Measure.map_dirac,
    Measure.dirac_bind] at atStart
  rw [Measure.dirac_apply_of_not_mem _ _ setMeasurable (by decide),
    Measure.dirac_apply_of_mem _ _ setMeasurable (by decide)] at atStart
  exact ENNReal.one_ne_zero atStart.symm

end Problib.Measure.Kernel.Site
