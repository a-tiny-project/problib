module

public import Problib.Measure.Kernel.Chart.Fibre
public import Problib.Measure.Kernel.Piecewise.Countable

/-! # A family per piece of the parameter space

The charts that describe a law can change at exceptional parameters: scaling a
draw by `θ` spreads it over a line when `θ ≠ 0` and collapses it to a point when
`θ = 0`. A split cuts the parameter space into countably many measurable pieces
and gives each piece its own chart family. Its reference reads, at each
parameter, the reference of that parameter's piece.

The split is an input. Nothing here constructs one from a program.
-/

set_option autoImplicit false

namespace Problib.Measure.Kernel.Chart

open Problib.Real
open Problib.Measure.Real (borel Carrier)

public section

universe u

variable {Θ : Type u} {parameter : Space Θ} {ambient : Nat}

/-- A measurable partition of the parameters into countably many pieces, with a
chart family for each piece. -/
public structure Split (parameter : Space Θ) (ambient : Nat) where
  piece : Θ → Nat
  piece_measurable : ∀ index, parameter.Measurable (fun θ => piece θ = index)
  family : Nat → Family parameter ambient

namespace Split

variable (split : Split parameter ambient)

/-- At each parameter, the reference of that parameter's piece. -/
@[expose] public noncomputable def reference : Kernel parameter (Space.pi fun _ : Fin ambient => borel) :=
  Kernel.countablePiecewise split.piece split.piece_measurable
    (fun index => (split.family index).reference)

public theorem reference_apply (θ : Θ) :
    split.reference θ = (split.family (split.piece θ)).reference θ := rfl

/-- The reference is globally s-finite, through each piece's shells. -/
public noncomputable def referenceSFinite : IsSFinite split.reference :=
  IsSFinite.countablePiecewise split.piece split.piece_measurable _
    (fun index => (split.family index).referenceSFinite)

/-- Every fiber of the reference is sigma-finite. -/
public noncomputable def referenceSigmaFinite (θ : Θ) : Measure.SigmaFinite (split.reference θ) :=
  (split.family (split.piece θ)).referenceSigmaFinite θ

/-- A law that each piece's reference covers on that piece has a jointly
measurable density against the split's reference. -/
public noncomputable def derivative (law : Kernel parameter (Space.pi fun _ : Fin ambient => borel))
    (lawFinite : IsSFinite law)
    (covers : ∀ θ, Measure.AbsolutelyContinuous (law θ) ((split.family (split.piece θ)).reference θ)) :
    RadonNikodymDerivative law split.reference :=
  RadonNikodymDerivative.ofStandardBorelSigmaFinite (ambientStandardBorel ambient) lawFinite
    split.referenceSFinite split.referenceSigmaFinite covers

end Split

end

end Problib.Measure.Kernel.Chart
