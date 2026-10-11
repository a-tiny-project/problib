import Problib.Probability.Finite.Expectation

set_option autoImplicit false

namespace Problib.Probability.FiniteEstimator

open Problib.Probability

universe u

structure Unbiased {Outcome : Type u}
    (law : FinitePMF Outcome) (estimate : Outcome → Rat) (target : Rat) : Prop where
  mean : law.expectation estimate = target

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

structure PartialEvaluation {Outcome : Type u}
    (coupled target : FinitePMF Outcome) : Prop where
  preserves : ∀ observable,
    target.expectation observable = coupled.expectation observable

structure Inference {Outcome : Type u}
    (target estimate : FinitePMF Outcome) : Prop where
  preserves : ∀ observable,
    estimate.expectation observable = target.expectation observable

end Problib.Probability.FiniteEstimator
