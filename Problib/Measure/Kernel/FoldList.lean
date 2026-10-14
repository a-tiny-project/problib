module

public import Problib.Measure.Kernel.Iteration.Basic
public import Problib.Measure.Kernel.Composition.Bind.Transport
public import Problib.Measure.AlmostEverywhere.Transport

set_option autoImplicit false

/-!
# The ordered kernel of a list

A list of elements and a step kernel at each element give one kernel: the step
at the first element, then the step at the next, to the end of the list
(`foldList`). The empty list is the identity kernel, and appending lists
composes their kernels.

`foldList_map_of_lumpsOn` reads the ordered kernel through a map. When each
step, followed by the map, is one fixed step on the image from the mapped
state, the ordered kernel followed by the map is that image step iterated once
per element. The image step need only match on a set of good image states that
it keeps almost surely, so the starting law need only be good almost surely.
This is the list form of `Lumps` (Iteration/Lumping.lean), restricted to a good
set.

`foldList_bind_of_summarizes` reads the ordered kernel through a statistic.
When each step sends the law at a statistic to a weight times the law at the
moved statistic (`Summarizes`), the ordered kernel sends it to the product of
the weights times the law at the final statistic. `bind_of_summarizes` states
the same for any kernel that runs the step once per element.
-/

namespace Problib.Measure.Kernel

open Problib.Real

public section

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {space : Space α} {output : Space γ}

/-- The step at each element of the list in turn, first element first. -/
@[expose] noncomputable def foldList (step : β → Kernel space space) :
    List β → Kernel space space
  | [] => Kernel.deterministic (fun value => value) (MeasurableMap.identity space)
  | y :: ys => (step y).comp (foldList step ys)

theorem foldList_nil (step : β → Kernel space space) :
    foldList step [] =
      Kernel.deterministic (fun value => value) (MeasurableMap.identity space) :=
  rfl

theorem foldList_cons (step : β → Kernel space space) (y : β) (ys : List β) :
    foldList step (y :: ys) = (step y).comp (foldList step ys) :=
  rfl

/-- The kernel of an appended list runs the first list's kernel, then the
second's. -/
theorem foldList_append (step : β → Kernel space space) (xs ys : List β) :
    foldList step (xs ++ ys) = (foldList step xs).comp (foldList step ys) := by
  induction xs with
  | nil =>
      apply Kernel.ext
      intro input
      rw [List.nil_append, foldList_nil, comp_apply, deterministic_apply, Measure.dirac_bind]
  | cons x xs induction =>
      rw [List.cons_append, foldList_cons, foldList_cons, induction, comp_assoc]

/-- The ordered kernel of a list, followed by a map, is the image step iterated
once per element, from the mapped starting law. Each step must match the image
step at every state whose image is good, and the image step must keep good
states good almost surely. -/
theorem foldList_map_of_lumpsOn {step : β → Kernel space space} {reduce : α → γ}
    (reduceMeasurable : MeasurableMap space output reduce) {outputStep : Kernel output output}
    {good : γ → Prop} (goodMeasurable : output.Measurable good)
    (lumps : ∀ y state, good (reduce state) →
      (step y state).map reduce reduceMeasurable = outputStep (reduce state))
    (keeps : ∀ image, good image → (outputStep image).AE good)
    (ys : List β) (start : Measure space) (startGood : start.AE fun state => good (reduce state)) :
    (start.bind (foldList step ys)).map reduce reduceMeasurable =
      (start.map reduce reduceMeasurable).bind (iterate outputStep ys.length) := by
  induction ys generalizing start with
  | nil =>
      rw [foldList_nil, Measure.bind_deterministic, Measure.map_id, List.length_nil, iterate_zero,
        Measure.bind_deterministic, Measure.map_id]
  | cons y ys induction =>
      have stepGood : ∀ state, good (reduce state) →
          (step y state).AE fun next => good (reduce next) := fun state holds =>
        Measure.AE.of_map reduce reduceMeasurable
          (lumps y state holds ▸ keeps (reduce state) holds)
      have nextGood : (start.bind (step y)).AE fun state => good (reduce state) :=
        Measure.ae_bind (space.complement (reduceMeasurable goodMeasurable)) startGood stepGood
      have imaged : (start.bind (step y)).map reduce reduceMeasurable =
          (start.map reduce reduceMeasurable).bind outputStep := by
        rw [Measure.map_bind, Measure.bind_map]
        apply Measure.bind_congr_ae
        exact startGood.mono fun state holds => lumps y state holds
      rw [foldList_cons, ← Measure.bind_assoc, induction (start.bind (step y)) nextGood, imaged,
        Measure.bind_assoc, List.length_cons, iterate_succ]

/-- Each step sends the law at a valid statistic to a weight times the law at
the moved statistic, and moving keeps a statistic valid. -/
structure Summarizes {σ : Type x} (relate : σ → Measure space) (valid : σ → Prop)
    (step : β → Kernel space space) (move : σ → β → σ) (weight : σ → β → ENNReal) : Prop where
  keeps : ∀ s y, valid s → valid (move s y)
  law : ∀ s y, valid s →
    (relate s).bind (step y) = Measure.smul (weight s y) (relate (move s y))

variable {σ : Type x} {relate : σ → Measure space} {valid : σ → Prop}
  {step : β → Kernel space space} {move : σ → β → σ} {weight : σ → β → ENNReal}

/-- A kernel that runs a summarized step once per element sends the law at a
valid statistic to the product of the weights times the law at the final
statistic. The run, the product and the final statistic are given by their
equations, so a caller's own definitions are used as written. -/
theorem bind_of_summarizes (summarizes : Summarizes relate valid step move weight)
    {run : List β → Kernel space space}
    (run_nil : run [] = Kernel.deterministic (fun value => value) (MeasurableMap.identity space))
    (run_cons : ∀ y ys, run (y :: ys) = (step y).comp (run ys))
    {along : σ → List β → ENNReal} (along_nil : ∀ s, along s [] = ENNReal.one)
    (along_cons : ∀ s y ys, along s (y :: ys) = ENNReal.mul (weight s y) (along (move s y) ys))
    {final : σ → List β → σ} (final_nil : ∀ s, final s [] = s)
    (final_cons : ∀ s y ys, final s (y :: ys) = final (move s y) ys) :
    ∀ ys {s}, valid s →
      (relate s).bind (run ys) = Measure.smul (along s ys) (relate (final s ys)) := by
  intro ys
  induction ys with
  | nil =>
      intro s _
      rw [run_nil, Measure.bind_deterministic, Measure.map_id, along_nil, final_nil,
        Measure.one_smul]
  | cons y ys induction =>
      intro s holds
      rw [run_cons, ← Measure.bind_assoc, summarizes.law s y holds, Measure.smul_bind,
        induction (summarizes.keeps s y holds), Measure.smul_smul, along_cons, final_cons]

/-- The ordered kernel of a list sends the law at a valid statistic to the
product of the weights times the law at the final statistic. -/
theorem foldList_bind_of_summarizes (summarizes : Summarizes relate valid step move weight)
    {along : σ → List β → ENNReal} (along_nil : ∀ s, along s [] = ENNReal.one)
    (along_cons : ∀ s y ys, along s (y :: ys) = ENNReal.mul (weight s y) (along (move s y) ys))
    {final : σ → List β → σ} (final_nil : ∀ s, final s [] = s)
    (final_cons : ∀ s y ys, final s (y :: ys) = final (move s y) ys) :
    ∀ ys {s}, valid s →
      (relate s).bind (foldList step ys) = Measure.smul (along s ys) (relate (final s ys)) :=
  bind_of_summarizes summarizes (foldList_nil step) (foldList_cons step) along_nil along_cons
    final_nil final_cons

end

end Problib.Measure.Kernel
