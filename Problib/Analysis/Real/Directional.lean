module

public import Problib.Analysis.Real.Calculus

/-! Directional derivatives over a runtime parameter space.

A model's parameters are a product of reals, often cut down by a subtype
carrying positivity. Differentiating in one of them is differentiating the
restriction of the function to a line through the parameter point, at zero.
Stating it that way keeps the parameter space an arbitrary type: only the line
has to land in it, and the line is built by the same three constructors for
every space in the tree, a real coordinate, a pair, and a subtype.
-/

set_option autoImplicit false

namespace Problib.Analysis.Real

open Problib.Real.Construction.Dedekind

noncomputable section

/-- The derivative at zero of the restriction of `function` to `curve`. -/
@[expose] public def HasDirectionalDerivative {Parameter : Type}
    (function : Parameter → selection.Carrier)
    (curve : selection.Carrier → Parameter)
    (derivative : selection.Carrier) : Prop :=
  HasDerivative (fun step => function (curve step)) zero derivative

/-! ### Lines -/

/-- The line through `base` in `direction`. -/
@[expose] public def line (base direction : selection.Carrier) :
    selection.Carrier → selection.Carrier :=
  fun step => add base (mul direction step)

/-- A line passes through its base at step zero. -/
public theorem line_at_zero (base direction : selection.Carrier) :
    line base direction zero = base := by
  simp only [line, mul_zero, add_zero]

/-- A curve that never moves. -/
@[expose] public def lineConst {Parameter : Type} (value : Parameter) :
    selection.Carrier → Parameter :=
  fun _ => value

/-- A line in a product space is a pair of lines. -/
@[expose] public def lineProduct {Left Right : Type}
    (leftCurve : selection.Carrier → Left)
    (rightCurve : selection.Carrier → Right) :
    selection.Carrier → Left × Right :=
  fun step => (leftCurve step, rightCurve step)

/-- A line in a subtype is a line in the carrier that stays inside it. -/
@[expose] public def lineSubtype {Parameter : Type} {property : Parameter → Prop}
    (curve : selection.Carrier → Parameter)
    (member : ∀ step : selection.Carrier, property (curve step)) :
    selection.Carrier → Subtype property :=
  fun step => ⟨curve step, member step⟩

/-! ### Reading a directional derivative -/

/-- Shifting the argument and differentiating at zero is differentiating at the
point. -/
public theorem secant_shift
    (function : selection.Carrier → selection.Carrier)
    (point displacement : selection.Carrier) :
    secant (fun step => function (add point step)) zero displacement =
      secant function point displacement := by
  simp only [secant]
  rw [add_comm zero displacement, add_zero, add_zero]

/-- The directional derivative along the unit line is the derivative. -/
public theorem hasDirectionalDerivative_line
    {function : selection.Carrier → selection.Carrier}
    {point derivative : selection.Carrier} :
    HasDirectionalDerivative function (line point one) derivative ↔
      HasDerivative function point derivative := by
  have restrict : (fun step => function (line point one step)) =
      fun step => function (add point step) := by
    funext step
    simp only [line]
    rw [one_mul]
  simp only [HasDirectionalDerivative, restrict, HasDerivative, secant_shift]

/-- A function that ignores the moving parameter has directional derivative
zero. -/
public theorem hasDirectionalDerivative_const {Parameter : Type}
    (function : Parameter → selection.Carrier) (value : Parameter) :
    HasDirectionalDerivative function (lineConst value) zero := by
  simp only [HasDirectionalDerivative, lineConst]
  exact hasDerivative_const (function value) zero

/-- Reading the left component of a product line reads its left curve. -/
public theorem hasDirectionalDerivative_first {Left Right : Type}
    (function : Left → selection.Carrier)
    (leftCurve : selection.Carrier → Left)
    (rightCurve : selection.Carrier → Right)
    (derivative : selection.Carrier) :
    HasDirectionalDerivative (fun pair : Left × Right => function pair.1)
        (lineProduct leftCurve rightCurve) derivative ↔
      HasDirectionalDerivative function leftCurve derivative :=
  Iff.rfl

/-- Reading the right component of a product line reads its right curve. -/
public theorem hasDirectionalDerivative_second {Left Right : Type}
    (function : Right → selection.Carrier)
    (leftCurve : selection.Carrier → Left)
    (rightCurve : selection.Carrier → Right)
    (derivative : selection.Carrier) :
    HasDirectionalDerivative (fun pair : Left × Right => function pair.2)
        (lineProduct leftCurve rightCurve) derivative ↔
      HasDirectionalDerivative function rightCurve derivative :=
  Iff.rfl

/-- A subtype parameter space differentiates through its underlying value. -/
public theorem hasDirectionalDerivative_subtype {Parameter : Type}
    {property : Parameter → Prop}
    (function : Parameter → selection.Carrier)
    (curve : selection.Carrier → Parameter)
    (member : ∀ step : selection.Carrier, property (curve step))
    (derivative : selection.Carrier) :
    HasDirectionalDerivative
        (fun parameter : Subtype property => function parameter.val)
        (lineSubtype curve member) derivative ↔
      HasDirectionalDerivative function curve derivative :=
  Iff.rfl

end

end Problib.Analysis.Real
