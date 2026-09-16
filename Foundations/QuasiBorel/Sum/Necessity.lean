module

public import Foundations.QuasiBorel.Sum.Laws

set_option autoImplicit false

/-!
# Necessity witnesses for quasi-Borel sums and initial objects

This module collects counterexamples and necessity witnesses for coproducts.
It refutes naive demands for total generators into every summand.
It also refutes using unrestricted empty spaces as initial objects.
-/
namespace Foundations.QuasiBorel.Sum.Necessity

universe u v w

/-- Refutes demanding total generators into every summand.
Given an inhabited source, total functions into a sum space exist even when one
summand is empty and admits no total generator. -/
public theorem total_branches_exclude_empty_summand {Ω : Type u} (seed : Ω) :
    Nonempty (Ω → _root_.Sum PEmpty.{v + 1} Unit) ∧
      ¬Nonempty (Ω → PEmpty.{v + 1}) := by
  constructor
  · exact ⟨fun _ => _root_.Sum.inr ()⟩
  · rintro ⟨branch⟩
    exact (branch seed).elim

/-- Proves that constant random elements into the right summand are accepted
even when the left summand is the initial space. -/
public theorem initial_left_accepts_right_constant {Ω : Type u} (source : Source Ω)
    (right : Space.{u, w} source) (point : right.Carrier) :
    (Space.sum (Space.initial.{u, v} source) right).Random
      (fun _ => _root_.Sum.inr point) :=
  SumRandom.inr (right.constant point)

/-- Proves that constant random elements into the left summand are accepted
even when the right summand is the initial space. -/
public theorem initial_right_accepts_left_constant {Ω : Type u} (source : Source Ω)
    (left : Space.{u, w} source) (point : left.Carrier) :
    (Space.sum left (Space.initial.{u, v} source)).Random
      (fun _ => _root_.Sum.inl point) :=
  SumRandom.inl (left.constant point)

/-- Refutes using unrestricted empty spaces as initial objects.
When the source is empty, unrestricted empty spaces accept the identity map and
cannot map to `initial`. -/
public theorem unrestricted_empty_is_not_initial :
    ¬Nonempty (Hom (Space.unrestricted (Source.unrestricted Empty) Empty)
      (Space.initial.{0, 0} (Source.unrestricted Empty))) := by
  rintro ⟨morphism⟩
  exact morphism.mapRandom (random := fun seed => seed) True.intro

end Foundations.QuasiBorel.Sum.Necessity
