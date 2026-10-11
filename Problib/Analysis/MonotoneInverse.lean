module

public import Problib.Measure.Real.Borel
public import Problib.Real.Inverse

set_option autoImplicit false
open Problib.Real Problib.Measure Problib.Measure.Real
open Problib.Real.Construction.Dedekind

namespace Problib.Analysis

public section

noncomputable section

/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Alistair Tucker, Wen Yang

The supremum argument follows the continuous-induction proof
IsClosed.mem_of_ge_of_forall_exists_gt in
Mathlib/Topology/Order/IntermediateValue.lean at commit
15fe1e4eb92a37c66db923a0fa96596d7b504a35. Tiny replaces topological
closedness and neighborhood arguments with the explicit left/right order
witnesses below, using the sealed Dedekind carrier. No Mathlib import is used.
-/

/-- Order data ensuring that a strictly increasing function on the positive ray
attains every real value. The local witnesses rule out jumps at positive inputs.
No condition is imposed on the function at nonpositive inputs. -/
structure PositiveOrderData (f : Carrier → Carrier) : Prop where
  strict : ∀ x y, lt zero x → lt zero y → lt x y → lt (f x) (f y)
  lower : ∀ r, ∃ x, lt zero x ∧ lt (f x) r
  upper : ∀ r, ∃ x, lt zero x ∧ lt r (f x)
  right : ∀ x, lt zero x → ∀ r, lt (f x) r →
    ∃ y, lt x y ∧ lt (f y) r
  left : ∀ x, lt zero x → ∀ r, lt r (f x) →
    ∃ y, lt zero y ∧ lt y x ∧ lt r (f y)

/-- Completeness supplies a positive preimage of every real target. -/
theorem surjective_of_order (f : Carrier → Carrier) (h : PositiveOrderData f) :
    ∀ r, ∃ x, lt zero x ∧ f x = r := by
  intro r
  let S := fun x => lt zero x ∧ le (f x) r
  rcases h.lower r with ⟨l, hl, hfl⟩
  rcases h.upper r with ⟨u, hu, hfu⟩
  have bounded : IsUpperBound le S u := by
    intro x hx
    apply not_lt_iff_le.mp
    intro hux
    have less := h.strict u x hu hx.1 hux
    exact less.2 (le_trans hx.2 hfu.1)
  rcases exists_lub S ⟨l, hl, hfl.1⟩ ⟨u, bounded⟩ with ⟨s, hs, hleast⟩
  have hsp : lt zero s := lt_of_lt_of_le hl (hs l ⟨hl, hfl.1⟩)
  refine ⟨s, hsp, le_antisymm ?_ ?_⟩
  · apply not_lt_iff_le.mp
    intro hrs
    rcases h.left s hsp r hrs with ⟨y, hy, hys, hry⟩
    apply hys.2
    apply hleast y
    intro x hx
    apply not_lt_iff_le.mp
    intro hyx
    have less := h.strict y x hy hx.1 hyx
    exact less.2 (le_trans hx.2 hry.1)
  · apply not_lt_iff_le.mp
    intro hsr
    rcases h.right s hsp r hsr with ⟨y, hsy, hyr⟩
    have hyp : lt zero y := lt_trans hsp hsy
    exact hsy.2 (hs y ⟨hyp, hyr.1⟩)

/-- The unique positive preimage, selected from proved surjectivity. -/
@[expose] def inverseOfOrder (f : Carrier → Carrier) (h : PositiveOrderData f)
    (r : Carrier) : Carrier := Classical.choose (surjective_of_order f h r)

theorem inverse_positive (f : Carrier → Carrier) (h : PositiveOrderData f) (r : Carrier) :
    lt zero (inverseOfOrder f h r) := (Classical.choose_spec (surjective_of_order f h r)).1

theorem inverse_right (f : Carrier → Carrier) (h : PositiveOrderData f) (r : Carrier) :
    f (inverseOfOrder f h r) = r := (Classical.choose_spec (surjective_of_order f h r)).2

theorem injective_positive (f : Carrier → Carrier) (h : PositiveOrderData f)
    {x y : Carrier} (hx : lt zero x) (hy : lt zero y) (heq : f x = f y) : x = y := by
  apply le_antisymm
  · apply not_lt_iff_le.mp
    intro hyx
    have hf := h.strict y x hy hx hyx
    rw [heq] at hf
    exact lt_irrefl _ hf
  · apply not_lt_iff_le.mp
    intro hxy
    have hf := h.strict x y hx hy hxy
    rw [heq] at hf
    exact lt_irrefl _ hf

/-- The inverse recovers the original input on the positive ray. -/
theorem inverse_left (f : Carrier → Carrier) (h : PositiveOrderData f)
    {x : Carrier} (hx : lt zero x) : inverseOfOrder f h (f x) = x :=
  injective_positive f h (inverse_positive f h _) hx (inverse_right f h _)

/-- Multiplication in the original domain becomes addition in the inverse domain. -/
theorem inverse_add (f : Carrier → Carrier) (h : PositiveOrderData f)
    (hmul : ∀ x y, lt zero x → lt zero y → f (mul x y) = add (f x) (f y))
    (a b : Carrier) :
    inverseOfOrder f h (add a b) = mul (inverseOfOrder f h a) (inverseOfOrder f h b) := by
  apply injective_positive f h (inverse_positive f h _)
    (mul_positive (inverse_positive f h _) (inverse_positive f h _))
  rw [inverse_right f h, hmul _ _ (inverse_positive f h _) (inverse_positive f h _),
    inverse_right f h, inverse_right f h]

theorem inverse_monotone (f : Carrier → Carrier) (h : PositiveOrderData f) :
    Monotone (inverseOfOrder f h) := by
  intro a b hab
  apply not_lt_iff_le.mp
  intro hba
  have hf := h.strict _ _ (inverse_positive f h b) (inverse_positive f h a) hba
  rw [inverse_right f h, inverse_right f h] at hf
  exact hf.2 hab

/-- The inverse is strictly increasing on the entire real line. -/
theorem inverse_strict (f : Carrier → Carrier) (h : PositiveOrderData f)
    {a b : Carrier} (hab : lt a b) :
    lt (inverseOfOrder f h a) (inverseOfOrder f h b) := by
  refine ⟨inverse_monotone f h hab.1, ?_⟩
  intro hba
  have equal := le_antisymm (inverse_monotone f h hab.1) hba
  have images := congrArg f equal
  rw [inverse_right f h, inverse_right f h] at images
  exact hab.2 (images ▸ le_refl a)

/-- The positive-domain restriction of the left inverse law is necessary. -/
theorem inverse_left_zero_fails (f : Carrier → Carrier) (h : PositiveOrderData f) :
    inverseOfOrder f h (f zero) ≠ zero := by
  intro equal
  have positive := inverse_positive f h (f zero)
  rw [equal] at positive
  exact lt_irrefl zero positive

/-- An additive inverse law forces the original positive-input multiplication law. -/
theorem inverse_add_requires_mul (f : Carrier → Carrier) (h : PositiveOrderData f)
    (hadd : ∀ a b, inverseOfOrder f h (add a b) =
      mul (inverseOfOrder f h a) (inverseOfOrder f h b))
    {x y : Carrier} (hx : lt zero x) (hy : lt zero y) :
    f (mul x y) = add (f x) (f y) := by
  have equal := congrArg f (hadd (f x) (f y))
  rw [inverse_right f h, inverse_left f h hx, inverse_left f h hy] at equal
  exact equal.symm

theorem inverse_measurable (f : Carrier → Carrier) (h : PositiveOrderData f) :
    MeasurableMap borel borel (inverseOfOrder f h) :=
  monotone_measurable (inverse_monotone f h)

end
end
end Problib.Analysis
