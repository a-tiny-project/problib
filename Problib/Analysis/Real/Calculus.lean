module

public import Problib.Analysis.Real.Derivative

/-! Algebraic calculus on the sealed real carrier.

One theorem per operation. Each proof is the same two steps: rewrite the
difference quotient of the combined function as the corresponding combination
of the difference quotients, then read the limit off
`Problib.Analysis.Real.Limit`. No rule repeats an epsilon-delta argument,
because the limit layer already closed under the field operations. The
transcendental derivatives are not here: `exp` and `log` need their own series
evidence and belong with the interchange discharge, not with the algebra.
-/

set_option autoImplicit false

namespace Problib.Analysis.Real

open Problib.Real.Construction.Dedekind

noncomputable section

private instance : Std.Associative (α := selection.Carrier) mul :=
  ⟨fun left middle right => mul_assoc left middle right⟩
private instance : Std.Commutative (α := selection.Carrier) mul := ⟨mul_comm⟩
private instance : Std.Associative (α := selection.Carrier) add :=
  ⟨fun left middle right => add_assoc left middle right⟩
private instance : Std.Commutative (α := selection.Carrier) add := ⟨add_comm⟩

/-- A constant has derivative zero. -/
public theorem hasDerivative_const (value point : selection.Carrier) :
    HasDerivative (fun _ => value) point zero := by
  refine approaches_congr_near one_positive ?_ (approaches_const zero)
  intro displacement _ _
  simp only [secant, sub_self, zero_div]

/-- The identity has derivative one. -/
public theorem hasDerivative_identity (point : selection.Carrier) :
    HasDerivative (fun value => value) point one := by
  refine approaches_congr_near one_positive ?_ (approaches_const one)
  intro displacement nonzero _
  simp only [secant, add_sub_self]
  exact (div_self nonzero).symm

/-- Derivatives add. -/
public theorem hasDerivative_add
    {first second : selection.Carrier → selection.Carrier}
    {point firstDerivative secondDerivative : selection.Carrier}
    (firstDifferentiable : HasDerivative first point firstDerivative)
    (secondDifferentiable : HasDerivative second point secondDerivative) :
    HasDerivative (fun value => add (first value) (second value)) point
      (add firstDerivative secondDerivative) := by
  refine approaches_congr_near one_positive ?_
    (approaches_add firstDifferentiable secondDifferentiable)
  intro displacement _ _
  simp only [secant]
  rw [← add_div]
  congr 1
  simp only [sub_eq_add_neg, neg_add]
  ac_rfl

/-- Derivatives negate. -/
public theorem hasDerivative_neg
    {function : selection.Carrier → selection.Carrier}
    {point derivative : selection.Carrier}
    (differentiable : HasDerivative function point derivative) :
    HasDerivative (fun value => neg (function value)) point (neg derivative) := by
  refine approaches_congr_near one_positive ?_ (approaches_neg differentiable)
  intro displacement _ _
  simp only [secant]
  rw [← neg_div]
  congr 1
  exact neg_sub_distrib _ _

/-- Derivatives subtract. -/
public theorem hasDerivative_sub
    {first second : selection.Carrier → selection.Carrier}
    {point firstDerivative secondDerivative : selection.Carrier}
    (firstDifferentiable : HasDerivative first point firstDerivative)
    (secondDifferentiable : HasDerivative second point secondDerivative) :
    HasDerivative (fun value => sub (first value) (second value)) point
      (sub firstDerivative secondDerivative) := by
  have combined := hasDerivative_add firstDifferentiable
    (hasDerivative_neg secondDifferentiable)
  simpa only [sub_eq_add_neg] using combined

/-- A constant scales through a derivative. -/
public theorem hasDerivative_smul
    {function : selection.Carrier → selection.Carrier}
    {point derivative : selection.Carrier} (scalar : selection.Carrier)
    (differentiable : HasDerivative function point derivative) :
    HasDerivative (fun value => mul scalar (function value)) point
      (mul scalar derivative) := by
  refine approaches_congr_near one_positive ?_
    (approaches_mul (approaches_const scalar) differentiable)
  intro displacement _ _
  simp only [secant]
  rw [← mul_div_assoc]
  congr 1
  exact mul_sub scalar _ _

/-- The product rule. -/
public theorem hasDerivative_mul
    {first second : selection.Carrier → selection.Carrier}
    {point firstDerivative secondDerivative : selection.Carrier}
    (firstDifferentiable : HasDerivative first point firstDerivative)
    (secondDifferentiable : HasDerivative second point secondDerivative) :
    HasDerivative (fun value => mul (first value) (second value)) point
      (add (mul firstDerivative (second point))
        (mul (first point) secondDerivative)) := by
  have continuity := hasDerivative_continuous firstDifferentiable
  have shiftedPart := approaches_mul continuity secondDifferentiable
  have basePart := approaches_mul firstDifferentiable
    (approaches_const (second point))
  refine approaches_congr_near one_positive ?_ (approaches_add basePart shiftedPart)
  intro displacement _ _
  simp only [secant]
  rw [← div_mul_right, ← mul_div_assoc, ← add_div]
  congr 1
  rw [sub_mul, mul_sub, add_comm]
  exact sub_add_sub _ _ _

/-- The reciprocal rule, at a point where the function does not vanish. -/
public theorem hasDerivative_inverse
    {function : selection.Carrier → selection.Carrier}
    {point derivative : selection.Carrier}
    (differentiable : HasDerivative function point derivative)
    (nonzero : function point ≠ zero) :
    HasDerivative (fun value => inverse (function value)) point
      (neg (div derivative (mul (function point) (function point)))) := by
  have continuity := hasDerivative_continuous differentiable
  rcases approaches_nonzero_near continuity nonzero with
    ⟨radius, radiusPositive, awayFromZero⟩
  have reciprocal := approaches_inverse continuity nonzero
  have product := approaches_mul differentiable
    (approaches_mul reciprocal (approaches_const (inverse (function point))))
  have negated := approaches_neg product
  have limitForm : neg (mul derivative
      (mul (inverse (function point)) (inverse (function point)))) =
      neg (div derivative (mul (function point) (function point))) := by
    rw [div_eq_mul_inverse, inverse_mul nonzero nonzero]
  rw [limitForm] at negated
  refine approaches_congr_near radiusPositive ?_ negated
  intro displacement displacementNonzero small
  have shiftedNonzero := awayFromZero displacement displacementNonzero small
  simp only [secant]
  rw [← div_mul_right, ← neg_div]
  congr 1
  rw [sub_mul, ← mul_assoc (function (add point displacement)),
    mul_inverse_cancel shiftedNonzero, one_mul,
    mul_comm (inverse (function (add point displacement))) (inverse (function point)),
    ← mul_assoc (function point), mul_inverse_cancel nonzero, one_mul]
  exact neg_sub _ _

/-- The quotient rule, at a point where the denominator does not vanish. -/
public theorem hasDerivative_div
    {first second : selection.Carrier → selection.Carrier}
    {point firstDerivative secondDerivative : selection.Carrier}
    (firstDifferentiable : HasDerivative first point firstDerivative)
    (secondDifferentiable : HasDerivative second point secondDerivative)
    (nonzero : second point ≠ zero) :
    HasDerivative (fun value => div (first value) (second value)) point
      (div (sub (mul firstDerivative (second point))
          (mul (first point) secondDerivative))
        (mul (second point) (second point))) := by
  have squareNonzero : mul (second point) (second point) ≠ zero := by
    intro vanished
    rcases mul_eq_zero_iff.mp vanished with left | right
    · exact nonzero left
    · exact nonzero right
  have composed := hasDerivative_mul firstDifferentiable
    (hasDerivative_inverse secondDifferentiable nonzero)
  have limitForm :
      add (mul firstDerivative (inverse (second point)))
          (mul (first point)
            (neg (div secondDerivative (mul (second point) (second point))))) =
        div (sub (mul firstDerivative (second point))
            (mul (first point) secondDerivative))
          (mul (second point) (second point)) := by
    apply mul_right_cancel_of_nonzero squareNonzero
    rw [div_mul_cancel _ squareNonzero, add_mul, sub_eq_add_neg]
    congr 1
    · calc mul (mul firstDerivative (inverse (second point)))
            (mul (second point) (second point))
          = mul firstDerivative
              (mul (mul (inverse (second point)) (second point)) (second point)) := by
            ac_rfl
        _ = mul firstDerivative (second point) := by
            rw [inverse_mul_cancel nonzero, one_mul]
    · calc mul (mul (first point)
              (neg (div secondDerivative (mul (second point) (second point)))))
            (mul (second point) (second point))
          = neg (mul (first point)
              (mul (div secondDerivative (mul (second point) (second point)))
                (mul (second point) (second point)))) := by
            rw [mul_neg, neg_mul, mul_assoc]
        _ = neg (mul (first point) secondDerivative) := by
            rw [div_mul_cancel _ squareNonzero]
  rw [limitForm] at composed
  exact composed

end

end Problib.Analysis.Real
