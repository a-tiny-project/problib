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
-/

namespace Problib.Measure.Kernel

open Problib.Real

public section

universe u v w

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

end

end Problib.Measure.Kernel
