import Problib.Probability.Finite.Expectation

set_option autoImplicit false

namespace Problib.Probability.FiniteEstimator

open Problib.Probability

universe u

structure Unbiased {Outcome : Type u}
    (law : FinitePMF Outcome) (estimate : Outcome → Rat) (target : Rat) : Prop where
  mean : law.expectation estimate = target

theorem exact_unbiased (target : Rat) :
    Unbiased (FinitePMF.dirac target) (fun value => value) target := by
  constructor
  simp

def addEstimate {Outcome : Type u}
    (left right : Outcome → Rat) (outcome : Outcome) : Rat :=
  left outcome + right outcome

theorem add_unbiased {Outcome : Type u} {law : FinitePMF Outcome}
    {left right : Outcome → Rat} {leftTarget rightTarget : Rat}
    (leftUnbiased : Unbiased law left leftTarget)
    (rightUnbiased : Unbiased law right rightTarget) :
    Unbiased law (addEstimate left right) (leftTarget + rightTarget) := by
  constructor
  change law.expectation (fun outcome => left outcome + right outcome) = _
  rw [FinitePMF.expectation_add, leftUnbiased.mean, rightUnbiased.mean]

def MomentFactorizes {Outcome : Type u} (law : FinitePMF Outcome)
    (left right : Outcome → Rat) : Prop :=
  law.expectation (fun outcome => left outcome * right outcome) =
    law.expectation left * law.expectation right

def multiplyEstimate {Outcome : Type u}
    (left right : Outcome → Rat) (outcome : Outcome) : Rat :=
  left outcome * right outcome

theorem multiply_unbiased_of_factorized_moment
    {Outcome : Type u} {law : FinitePMF Outcome}
    {left right : Outcome → Rat} {leftTarget rightTarget : Rat}
    (leftUnbiased : Unbiased law left leftTarget)
    (rightUnbiased : Unbiased law right rightTarget)
    (factorized : MomentFactorizes law left right) :
    Unbiased law (multiplyEstimate left right) (leftTarget * rightTarget) := by
  constructor
  calc
    law.expectation (multiplyEstimate left right) =
        law.expectation left * law.expectation right := factorized
    _ = leftTarget * rightTarget := by rw [leftUnbiased.mean, rightUnbiased.mean]

def Centered {Outcome : Type u} (law : FinitePMF Outcome)
    (control : Outcome → Rat) : Prop :=
  law.expectation control = 0

def withBaseline {Outcome : Type u} (value pathwise score : Outcome → Rat)
    (baseline : Rat) (outcome : Outcome) : Rat :=
  pathwise outcome + (value outcome - baseline) * score outcome

def withoutBaseline {Outcome : Type u} (value pathwise score : Outcome → Rat)
    (outcome : Outcome) : Rat :=
  pathwise outcome + value outcome * score outcome

theorem baseline_preserves_mean {Outcome : Type u} {law : FinitePMF Outcome}
    (value pathwise score : Outcome → Rat) (baseline : Rat)
    (centered : Centered law score) :
    law.expectation (withBaseline value pathwise score baseline) =
      law.expectation (withoutBaseline value pathwise score) := by
  change law.expectation (fun outcome =>
      pathwise outcome + (value outcome - baseline) * score outcome) =
    law.expectation (fun outcome => pathwise outcome + value outcome * score outcome)
  rw [FinitePMF.expectation_add, FinitePMF.expectation_add]
  apply congrArg (fun tangent => law.expectation pathwise + tangent)
  calc
    law.expectation (fun outcome => (value outcome - baseline) * score outcome) =
        law.expectation (fun outcome =>
          value outcome * score outcome + (-baseline) * score outcome) := by
      apply FinitePMF.expectation_congr
      intro outcome
      rw [Rat.sub_eq_add_neg, Rat.add_mul]
    _ = law.expectation (fun outcome => value outcome * score outcome) +
        law.expectation (fun outcome => (-baseline) * score outcome) :=
      FinitePMF.expectation_add law _ _
    _ = law.expectation (fun outcome => value outcome * score outcome) +
        (-baseline) * law.expectation score := by
      rw [FinitePMF.expectation_scale]
    _ = law.expectation (fun outcome => value outcome * score outcome) := by
      rw [centered, Rat.mul_zero, Rat.add_zero]

structure Couples {Left Right : Type u}
    (law : FinitePMF (Left × Right))
    (left : FinitePMF Left) (right : FinitePMF Right) : Prop where
  left_marginal : ∀ observable,
    law.expectation (fun pair => observable pair.1) = left.expectation observable
  right_marginal : ∀ observable,
    law.expectation (fun pair => observable pair.2) = right.expectation observable

def difference {Outcome : Type u} (read : Outcome → Rat)
    (pair : Outcome × Outcome) : Rat :=
  read pair.2 - read pair.1

theorem coupled_difference_mean {Outcome : Type u}
    {law : FinitePMF (Outcome × Outcome)} {left right : FinitePMF Outcome}
    (couples : Couples law left right) (read : Outcome → Rat) :
    law.expectation (difference read) =
      right.expectation read - left.expectation read := by
  calc
    law.expectation (difference read) =
        law.expectation (fun pair => read pair.2 + (-1) * read pair.1) := by
      apply FinitePMF.expectation_congr
      intro pair
      rw [difference, Rat.sub_eq_add_neg, Rat.neg_mul, Rat.one_mul]
    _ = law.expectation (fun pair => read pair.2) +
        law.expectation (fun pair => (-1) * read pair.1) :=
      FinitePMF.expectation_add law _ _
    _ = right.expectation read + (-1) * left.expectation read := by
      rw [FinitePMF.expectation_scale, couples.right_marginal, couples.left_marginal]
    _ = right.expectation read - left.expectation read := by
      rw [Rat.sub_eq_add_neg, Rat.neg_mul, Rat.one_mul]

structure PartialEvaluation {Outcome : Type u}
    (coupled target : FinitePMF Outcome) : Prop where
  preserves : ∀ observable,
    target.expectation observable = coupled.expectation observable

structure Inference {Outcome : Type u}
    (target estimate : FinitePMF Outcome) : Prop where
  preserves : ∀ observable,
    estimate.expectation observable = target.expectation observable

theorem inference_after_partialEvaluation_preserves_difference
    {Outcome : Type u}
    {coupled target estimate : FinitePMF (Outcome × Outcome)}
    {left right : FinitePMF Outcome}
    (couples : Couples coupled left right)
    (partialEvaluation : PartialEvaluation coupled target)
    (inference : Inference target estimate)
    (read : Outcome → Rat) :
    estimate.expectation (difference read) =
      right.expectation read - left.expectation read := by
  rw [inference.preserves, partialEvaluation.preserves]
  exact coupled_difference_mean couples read

end Problib.Probability.FiniteEstimator
