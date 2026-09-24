module

public import Problib.Analysis.Exponential
public import Problib.Analysis.Real.Composition

/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Yury Kudryashov

The square-injectivity argument for sqrtMul follows NNReal.sqrt_mul in
Mathlib/Analysis/Real/Sqrt.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35. Tiny constructs the root from the
integral logarithm and its order inverse, then proves square injectivity
and the totalized division law with explicit Dedekind operations.
No Mathlib import or independent square-root construction is used.
-/

set_option autoImplicit false

namespace Problib.Analysis

open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind
open Logarithm

noncomputable section

private theorem half_add_half (x : Carrier) : add (div x (add one one)) (div x (add one one)) = x := by
  calc
    add (div x (add one one)) (div x (add one one)) = mul (add one one) (div x (add one one)) := by
      rw [mul_comm (add one one), mul_add, mul_one]
    _ = x := mul_div_cancel _
      (positive_iff_nonnegative_and_nonzero.mp (add_positive one_positive one_positive)).2

/-- The nonnegative square root, with the logarithmic formula on positive inputs. -/
@[expose] public def sqrt (x : NNReal) : NNReal := by
  classical
  exact if x = NNReal.zero then NNReal.zero
    else NNReal.ofReal (exp (div (logIntegral x.val) (add one one)))

public theorem sqrt_zero : sqrt NNReal.zero = NNReal.zero := by
  simp [sqrt]

public theorem sqrt_of_positive (x : NNReal) (hx : NNReal.lt NNReal.zero x) :
    sqrt x = NNReal.ofReal (exp (div (logIntegral x.val) (add one one))) := by
  simp only [sqrt, if_neg ((NNReal.zero_lt_iff_ne_zero x).mp hx)]

public theorem sqrt_square (x : NNReal) : NNReal.mul (sqrt x) (sqrt x) = x := by
  rcases NNReal.eq_zero_or_zero_lt x with rfl | hx
  · rw [sqrt_zero, NNReal.mul_zero]
  · rw [sqrt_of_positive x hx]
    apply NNReal.ext
    rw [NNReal.toReal_mul, NNReal.toReal_ofReal (exp_positive _).1, ← exp_add,
      half_add_half (logIntegral x.val)]
    exact exp_log x.val hx

private theorem square_strict {x y : NNReal} (hxy : NNReal.lt x y) :
    NNReal.lt (NNReal.mul x x) (NNReal.mul y y) := by
  have hyp : lt zero y.val := lt_of_le_of_lt x.property hxy
  exact lt_of_le_of_lt (mul_le_mul_nonnegative_right hxy.1 x.property)
    (mul_lt_mul_positive_left hxy hyp)

/-- Squaring reflects order on nonnegative inputs. -/
public theorem square_le_iff (x y : NNReal) :
    NNReal.le (NNReal.mul x x) (NNReal.mul y y) ↔ NNReal.le x y := by
  constructor
  · intro h
    apply not_lt_iff_le.mp
    intro hyx
    exact (square_strict hyx).2 h
  · intro h
    exact NNReal.mul_le_mul h h

public theorem sqrt_unique (x r : NNReal) (hr : NNReal.mul r r = x) : r = sqrt x := by
  apply NNReal.le_antisymm
  · apply (square_le_iff r (sqrt x)).mp
    rw [hr, sqrt_square]
    exact NNReal.le_refl x
  · apply (square_le_iff (sqrt x) r).mp
    rw [hr, sqrt_square]
    exact NNReal.le_refl x

public theorem sqrt_positive (x : NNReal) (hx : NNReal.lt NNReal.zero x) :
    NNReal.lt NNReal.zero (sqrt x) := by
  rw [sqrt_of_positive x hx]
  change lt zero (NNReal.toReal (NNReal.ofReal _))
  rw [NNReal.toReal_ofReal (exp_positive _).1]
  exact exp_positive _

public theorem sqrt_monotone {x y : NNReal} (hxy : NNReal.le x y) :
    NNReal.le (sqrt x) (sqrt y) := by
  apply (square_le_iff (sqrt x) (sqrt y)).mp
  rw [sqrt_square, sqrt_square]
  exact hxy

private theorem square_mul (x y : NNReal) :
    NNReal.mul (NNReal.mul x y) (NNReal.mul x y) =
      NNReal.mul (NNReal.mul x x) (NNReal.mul y y) := by
  rw [NNReal.mul_assoc, ← NNReal.mul_assoc y x, NNReal.mul_comm y x,
    NNReal.mul_assoc x y y, ← NNReal.mul_assoc]

public theorem sqrt_mul (x y : NNReal) :
    sqrt (NNReal.mul x y) = NNReal.mul (sqrt x) (sqrt y) := by
  symm
  apply sqrt_unique
  rw [square_mul, sqrt_square, sqrt_square]

private theorem div_zero (x : NNReal) : NNReal.div x NNReal.zero = NNReal.zero := by
  apply NNReal.ext
  exact Construction.Dedekind.div_zero x.val

public theorem sqrt_div (x y : NNReal) :
    sqrt (NNReal.div x y) = NNReal.div (sqrt x) (sqrt y) := by
  rcases NNReal.eq_zero_or_zero_lt y with rfl | hy
  · rw [div_zero, sqrt_zero, div_zero]
  · apply NNReal.mul_right_cancel
      ((NNReal.zero_lt_iff_ne_zero (sqrt y)).mp (sqrt_positive y hy))
    rw [← sqrt_mul, NNReal.div_mul_cancel _ ((NNReal.zero_lt_iff_ne_zero y).mp hy),
      NNReal.div_mul_cancel _ ((NNReal.zero_lt_iff_ne_zero (sqrt y)).mp (sqrt_positive y hy))]

/-- The zero-extended real root is monotone, so its restriction is measurable
for the existing nonnegative-real pullback Borel space. -/
public theorem sqrt_measurable :
    MeasurableMap (Space.comap ENNReal.finite ennrealBorel)
      (Space.comap ENNReal.finite ennrealBorel) sqrt := by
  have hm : MeasurableMap borel borel (fun x => (sqrt (NNReal.ofReal x)).val) :=
    monotone_measurable (fun _ _ h => sqrt_monotone (NNReal.ofReal_monotone h))
  have val_measurable : MeasurableMap (Space.comap ENNReal.finite ennrealBorel)
      borel NNReal.toReal :=
    MeasurableMap.comp toReal_measurable (Space.comap_map ENNReal.finite ennrealBorel)
  have he : MeasurableMap (Space.comap ENNReal.finite ennrealBorel) ennrealBorel
      (fun x : NNReal => ENNReal.ofReal ((sqrt (NNReal.ofReal x.val)).val)) :=
    (ofReal_measurable.comp (MeasurableMap.comp hm val_measurable)).measurableMap
  have restore (x : NNReal) : NNReal.ofReal x.val = x :=
    NNReal.ext (NNReal.toReal_ofReal x.property)
  have equal : (fun x : NNReal => ENNReal.ofReal ((sqrt (NNReal.ofReal x.val)).val)) =
      (fun x => ENNReal.finite (sqrt x)) := by
    funext x
    rw [restore]
    exact ENNReal.ofReal_toReal_finite (sqrt x)
  rw [equal] at he
  intro region hr
  rcases (Space.comap_measurable_iff ENNReal.finite ennrealBorel region).mp hr with
    ⟨target, ht, rfl⟩
  exact he ht

/-! ### Continuity and the derivative

The root of a positive `a` moves by at most `|x - a| / √a`, because
`√x - √a` times `√x + √a` is `x - a` and the sum is at least `√a`. That bound
gives continuity at every positive point, and the inverse-function rule, with
squaring as the forward map, gives the derivative `1 / (2 √a)`.
-/

open Problib.Analysis.Real

/-- The root moves by at most the argument's move divided by the root of a
positive base point. -/
public theorem sqrt_sub_le (x a : NNReal) (positive : NNReal.lt NNReal.zero a) :
    le (abs (sub (sqrt x).val (sqrt a).val)) (div (abs (sub x.val a.val)) (sqrt a).val) := by
  have rootPositive : lt zero (sqrt a).val := sqrt_positive a positive
  have sumPositive : lt zero (add (sqrt x).val (sqrt a).val) := by
    have raised := (add_le_add_right_iff (shift := (sqrt a).val)).mpr (sqrt x).property
    rw [add_comm zero, add_zero] at raised
    exact lt_of_lt_of_le rootPositive raised
  have sumNonzero := (positive_iff_nonnegative_and_nonzero.mp sumPositive).2
  have square (y : NNReal) : y.val = mul (sqrt y).val (sqrt y).val := by
    have squared := congrArg NNReal.toReal (sqrt_square y)
    rw [NNReal.toReal_mul] at squared
    exact squared.symm
  have factored : sub x.val a.val =
      mul (sub (sqrt x).val (sqrt a).val) (add (sqrt x).val (sqrt a).val) := by
    rw [mul_add, sub_mul, sub_mul, mul_comm (sqrt a).val (sqrt x).val, add_comm,
      add_comm (sub _ _) (sub _ _), sub_add_sub, ← square, ← square]
  have quotient : sub (sqrt x).val (sqrt a).val =
      div (sub x.val a.val) (add (sqrt x).val (sqrt a).val) := by
    rw [factored, div_eq_mul_inverse, mul_assoc, mul_inverse_cancel sumNonzero, mul_one]
  rw [quotient, abs_div, abs_of_nonnegative (positive_iff_nonnegative_and_nonzero.mp sumPositive).1]
  apply div_le_div_of_positive (abs_nonnegative _) rootPositive
  have raised := (add_le_add_left_iff (shift := (sqrt a).val)).mpr (sqrt x).property
  rwa [add_zero, add_comm] at raised

/-- The real root is continuous at every positive point. -/
public theorem sqrt_continuous (point : selection.Carrier) (positive : lt zero point) :
    Approaches (fun displacement => (sqrt (NNReal.ofReal (add point displacement))).val)
      (sqrt (NNReal.ofReal point)).val := by
  let base := NNReal.ofReal point
  have baseValue : base.val = point := NNReal.toReal_ofReal positive.1
  have basePositive : NNReal.lt NNReal.zero base := by
    change lt zero base.val
    rw [baseValue]
    exact positive
  let root := (sqrt base).val
  have rootPositive : lt zero root := sqrt_positive base basePositive
  have line : Approaches (fun displacement => add root (mul (inverse root) displacement)) root := by
    have sum := approaches_add (approaches_const root)
      (approaches_mul (approaches_const (inverse root)) approaches_displacement)
    rwa [mul_zero, add_zero] at sum
  refine approaches_of_closer positive (fun displacement _ inside => ?_) line
  have shiftedPositive : lt zero (add point displacement) := by
    have lower := (abs_lt.mp inside).1
    have raised := add_lt_add_left point lower
    rwa [add_neg] at raised
  have bound := sqrt_sub_le (NNReal.ofReal (add point displacement)) base basePositive
  have shiftedValue : (NNReal.ofReal (add point displacement)).val = add point displacement :=
    NNReal.toReal_ofReal shiftedPositive.1
  rw [shiftedValue, baseValue, add_sub_self] at bound
  show le _ (abs (sub (add root (mul (inverse root) displacement)) root))
  refine le_trans bound ?_
  rw [add_sub_self, abs_mul,
    abs_of_nonnegative (inverse_of_positive_positive rootPositive).1, mul_comm, ← div_eq_mul_inverse]
  exact le_refl _

/-- The real root differentiates to `1 / (2 √point)` at every positive point. -/
public theorem sqrt_hasDerivative (point : selection.Carrier) (positive : lt zero point) :
    HasDerivative (fun value => (sqrt (NNReal.ofReal value)).val) point
      (inverse (mul (add one one) (sqrt (NNReal.ofReal point)).val)) := by
  have basePositive : NNReal.lt NNReal.zero (NNReal.ofReal point) := by
    change lt zero (NNReal.toReal (NNReal.ofReal point))
    rw [NNReal.toReal_ofReal positive.1]
    exact positive
  have rootPositive : lt zero (sqrt (NNReal.ofReal point)).val := sqrt_positive _ basePositive
  have square := hasDerivative_mul (hasDerivative_identity (sqrt (NNReal.ofReal point)).val)
    (hasDerivative_identity (sqrt (NNReal.ofReal point)).val)
  have doubled : add (mul one (sqrt (NNReal.ofReal point)).val)
      (mul (sqrt (NNReal.ofReal point)).val one) =
      mul (add one one) (sqrt (NNReal.ofReal point)).val := by
    rw [mul_comm _ one, add_mul]
  rw [doubled] at square
  refine hasDerivative_of_right_inverse (forward := fun value => mul value value) positive
    (fun displacement inside => ?_) (sqrt_continuous point positive) square
    (positive_iff_nonnegative_and_nonzero.mp
      (mul_positive (add_positive one_positive one_positive) rootPositive)).2
  have shiftedPositive : lt zero (add point displacement) := by
    have raised := add_lt_add_left point (abs_lt.mp inside).1
    rwa [add_neg] at raised
  change (NNReal.mul (sqrt _) (sqrt _)).val = _
  rw [sqrt_square]
  exact NNReal.toReal_ofReal shiftedPositive.1

/-- Omitting the positive/zero branch gives a nonzero square at zero. -/
public theorem sqrt_without_guard_fails :
    NNReal.mul
      (NNReal.ofReal (exp (div (logIntegral zero) (add one one))))
      (NNReal.ofReal (exp (div (logIntegral zero) (add one one)))) ≠ NNReal.zero := by
  have positive : NNReal.lt NNReal.zero
      (NNReal.ofReal (exp (div (logIntegral zero) (add one one)))) := by
    change lt zero (NNReal.toReal (NNReal.ofReal _))
    rw [NNReal.toReal_ofReal (exp_positive _).1]
    exact exp_positive _
  exact (NNReal.zero_lt_iff_ne_zero _).mp (NNReal.mul_positive positive positive)

end
end Problib.Analysis
