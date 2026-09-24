module

public import Problib.Measure.Kernel.Iteration.Basic
public import Problib.Measure.Kernel.Composition.Bind.Transport
import Problib.Measure.Additive.Dirac

set_option autoImplicit false

/-!
# Lumping an iterated kernel along a map

A step lumps along a map when one step followed by the map depends on the state
only through the map's value. Then every iterate lumps, so the image of an
iterated chain is itself an iterated chain on the image space.
-/

namespace Problib.Measure.Kernel

open Problib.Real

universe u v

variable {α : Type u} {β : Type v} {space : Space α} {output : Space β}

/-- A step lumps along a map when one step followed by the map depends on the
state only through the map's value. -/
@[expose] public def Lumps (step : Kernel space space) (lump : α → β)
    (lumpMeasurable : MeasurableMap space output lump) (outputStep : Kernel output output) : Prop :=
  ∀ state, (step state).map lump lumpMeasurable = outputStep (lump state)

/-- Lumping commutes with iteration: `count` steps followed by the map equal
`count` output steps from the mapped state. -/
public theorem iterate_map_of_lumps {step : Kernel space space} {lump : α → β}
    {lumpMeasurable : MeasurableMap space output lump} {outputStep : Kernel output output}
    (lumps : Lumps step lump lumpMeasurable outputStep) (count : Nat) (state : α) :
    (iterate step count state).map lump lumpMeasurable = iterate outputStep count (lump state) := by
  induction count generalizing state with
  | zero =>
      rw [iterate_zero, iterate_zero, deterministic_apply, deterministic_apply, Measure.map_dirac]
  | succ count induction =>
      have kernels : (iterate step count).map lump lumpMeasurable =
          (iterate outputStep count).precomp lump lumpMeasurable := by
        apply Kernel.ext
        intro other
        rw [map_apply, precomp_apply, induction other]
      rw [iterate_succ, iterate_succ, comp_apply, comp_apply, Measure.map_bind, kernels,
        ← Measure.bind_map, lumps state]

end Problib.Measure.Kernel
